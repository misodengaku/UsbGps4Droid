/*
 * Copyright (C) 2016, 2017 Oliver Bell
 * Copyright (C) 2010, 2011, 2012 Herbert von Broeuschmeul
 * Copyright (C) 2010, 2011, 2012 BluetoothGPS4Droid Project
 * Copyright (C) 2011, 2012 UsbGPS4Droid Project
 *
 * This file is part of UsbGPS4Droid.
 *
 * UsbGPS4Droid is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * UsbGPS4Droid is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with UsbGPS4Droid. If not, see <http://www.gnu.org/licenses/>.
 */

package org.broeuschmeul.android.gps.usb.provider.driver;

import android.Manifest;
import android.annotation.SuppressLint;
import android.app.AppOpsManager;
import android.app.Notification;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.Service;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.hardware.usb.UsbDevice;
import android.hardware.usb.UsbDeviceConnection;
import android.hardware.usb.UsbManager;
import android.location.LocationManager;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.SystemClock;
import android.preference.PreferenceManager;
import android.provider.Settings;
import android.util.Log;

import androidx.core.app.NotificationCompat;
import androidx.core.content.ContextCompat;

import com.google.common.util.concurrent.SimpleTimeLimiter;
import com.google.common.util.concurrent.TimeLimiter;
import com.hoho.android.usbserial.driver.UsbSerialDriver;
import com.hoho.android.usbserial.driver.UsbSerialPort;
import com.hoho.android.usbserial.driver.UsbSerialProber;
import com.hoho.android.usbserial.util.SerialInputOutputManager;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicReference;

import org.broeuschmeul.android.gps.nmea.util.NmeaParser;
import org.broeuschmeul.android.gps.sirf.util.SirfUtils;
import org.broeuschmeul.android.gps.usb.provider.BuildConfig;
import org.broeuschmeul.android.gps.usb.provider.R;
import org.broeuschmeul.android.gps.usb.provider.USBGpsApplication;
import org.broeuschmeul.android.gps.usb.provider.ui.GpsInfoActivity;
import org.broeuschmeul.android.gps.usb.provider.util.SuperuserManager;

/**
 * This class is used to establish and manage the connection with the bluetooth
 * GPS.
 *
 * @author Herbert von Broeuschmeul
 */
public class USBGpsManager {

    /**
     * Tag used for log messages
     */
    private static final String LOG_TAG = USBGpsManager.class.getSimpleName();

    // Has more connections logs
    private final boolean debug = true;

    private UsbManager usbManager = null;
    private static final String ACTION_USB_PERMISSION =
            "org.broeuschmeul.android.gps.usb.provider.driver.USBGpsManager.USB_PERMISSION";

    /**
     * Used to listen for nmea updates from UsbGpsManager
     */
    public interface NmeaListener {
        void onNmeaReceived(long timestamp, String nmea);
    }

    private final BroadcastReceiver permissionAndDetachReceiver =
            new BroadcastReceiver() {
                public void onReceive(Context context, Intent intent) {
                    String action = intent.getAction();
                    if (ACTION_USB_PERMISSION.equals(action)) {
                        synchronized (this) {
                            UsbDevice device =
                                    intent.getParcelableExtra(UsbManager.EXTRA_DEVICE);

                            if (intent.getBooleanExtra(UsbManager.EXTRA_PERMISSION_GRANTED,
                                    false)) {
                                if (device != null) {
                                    if (usbManager.hasPermission(device)) {
                                        debugLog("We have permission, good!");
                                        if (enabled) {
                                            connectedGps = new ConnectedGps(gpsVendorId, gpsProductId,
                                                    deviceSpeed);
                                            connectedGps.requestPermission(gpsVendorId, gpsProductId);
                                            new Thread(new Runnable() {
                                                public void run() {
                                                    connectedGps.start();
                                                }
                                            }).start();
                                        }
                                    }
                                }
                            } else {
                                debugLog("permission denied for device " + device);
                            }
                        }
                    } else if (UsbManager.ACTION_USB_DEVICE_DETACHED.equals(action)) {
                        synchronized (this) {
                            if (connectedGps != null && enabled) {
                                connectedGps.close();
                            }
                        }
                    }
                }
            };

    /**
     * A utility class used to manage the communication with the bluetooth GPS whn
     * the connection has been established. It is used to read NMEA data from the
     * GPS or to send SIRF III binary commands or SIRF III NMEA commands to the
     * GPS. You should run the main read loop in one thread and send the commands
     * in a separate one.
     *
     * @author Herbert von Broeuschmeul
     */
    private class ConnectedGps
            extends Thread implements SerialInputOutputManager.Listener {
        /**
         * GPS bluetooth socket used for communication.
         */
        private UsbDevice device;
        private boolean closed = false;
        private final UsbManager manager;
        private UsbSerialPort port;
        private SerialInputOutputManager usbIoManager;
        /**
         * A boolean which indicates if the GPS is ready to receive data.
         * In fact we consider that the GPS is ready when it begins to sends data...
         */
        private boolean ready = false;
        public boolean readBlock = false;
        private UsbSerialDriver driver;
        public final static int USB_READ_WAIT = 500;
        public final static int USB_WRITE_WAIT = 500;
        private Exception readError;
        private String linebuf = null;

        public ConnectedGps(int vendorId, int productId) {
            this(vendorId, productId, defaultDeviceSpeed);
        }

        public ConnectedGps(int vendorId, int productId, String deviceSpeed) {

            this.manager =
                    (UsbManager) appContext.getSystemService(Context.USB_SERVICE);
            List<UsbSerialDriver> availableDrivers =
                    UsbSerialProber.getDefaultProber().findAllDrivers(manager);
            if (availableDrivers.isEmpty()) {
                debugLog("not available");
                return;
            }

            this.device = getDeviceFromAttached(vendorId, productId);
            if (device == null) {
                debugLog("device not found");
                return;
            }

            if (!this.manager.hasPermission(device)) {
                debugLog("not permitted");
                return;
            }

            debugLog("Searching interfaces, found " +
                    availableDrivers.size());
            driver = availableDrivers.get(0);
        }

        public boolean requestPermission(int vendorId, int productId) {
            PendingIntent permissionIntent = PendingIntent.getBroadcast(
                    callingService, 0, new Intent(ACTION_USB_PERMISSION), 0);
            device = getDeviceFromAttached(vendorId, productId);
            if (device == null) {
                debugLog("device not found");
                return false;
            }

            if (!manager.hasPermission(device)) {
                manager.requestPermission(device, permissionIntent);
            }
            return true;
        }

        public void start() {
            UsbDeviceConnection connection = manager.openDevice(device);
            if (connection == null) {
                // add UsbManager.requestPermission(driver.getDevice(), ..) handling
                // here
                return;
            }
            port = driver.getPorts().get(0);
            try {
                port.open(connection);
                port.setParameters(9600, 8, UsbSerialPort.STOPBITS_1,
                        UsbSerialPort.PARITY_NONE);
            } catch (IOException e) {
                debugLog("Error");
                return;
            }
            usbIoManager = new SerialInputOutputManager(port, this);
            if (usbIoManager != null) {

                usbIoManager.start();
            }
        }

        @Override
        public void onNewData(byte[] data) {
            if (linebuf == null) {
                linebuf = "";
            }
            for (byte b : data) {
                if (b != '\r' && b != '\n' && b != '\0') {
                    // gomi
                    linebuf += new String(new byte[]{b});
                }
                if (b == '\r' || b == '\n' || b == '\0') {
                    if (linebuf.length() > 0) {
                        if (notifyNmeaSentence(linebuf + "\r\n")) {
                            ready = true;
                            //   lastRead = SystemClock.uptimeMillis();
                        }
                        linebuf = "";
                    }
                }
            }
        }

        private UsbDevice getDeviceFromAttached(int vendorId, int productId) {
            debugLog("Checking all connected devices");
            for (UsbDevice connectedDevice : manager.getDeviceList().values()) {

                debugLog("Checking device: " + connectedDevice.getProductId() + " " +
                        connectedDevice.getVendorId());

                if (connectedDevice.getVendorId() == vendorId &
                        connectedDevice.getProductId() == productId) {
                    debugLog("Found correct device");

                    return connectedDevice;
                }
            }

            return null;
        }

        @Override
        public void onRunError(Exception e) {
            readError = e;
        }

        public boolean isReady() {
            return ready;
        }

        public void close() {
            ready = false;
            closed = true;
            try {
                debugLog("closing USB GPS output stream");
                port.close();
                usbIoManager.stop();
            } catch (IOException e) {
                if (BuildConfig.DEBUG || debug)
                    Log.e(LOG_TAG, "error while closing GPS NMEA output stream", e);
            }
        }
    }

    private boolean timeSetAlready;
    private final boolean shouldSetTime;

    private final Service callingService;
    private UsbDevice gpsDev;

    private final NmeaParser parser;
    private boolean enabled = false;
    private ExecutorService notificationPool;
    //   private ScheduledExecutorService connectionAndReadingPool;

    private final List<NmeaListener> nmeaListeners =
            Collections.synchronizedList(new LinkedList<NmeaListener>());

    private final LocationManager locationManager;
    private final SharedPreferences sharedPreferences;
    private ConnectedGps connectedGps;
    private int disableReason = 0;

    private final NotificationCompat.Builder connectionProblemNotificationBuilder;
    private final NotificationCompat.Builder serviceStoppedNotificationBuilder;

    private final Context appContext;
    private final NotificationManager notificationManager;

    private final int maxConnectionRetries;
    private final int nbRetriesRemaining;
    private boolean problemNotified = false;

    private final boolean connected = false;
    private boolean setDeviceSpeed = false;
    private boolean sirfGps = false;
    private String deviceSpeed = "auto";
    private String defaultDeviceSpeed = "4800";

    private int gpsProductId = 8963;
    private int gpsVendorId = 1659;

    /**
     * @param callingService
     * @param vendorId
     * @param productId
     * @param maxRetries
     */
    public USBGpsManager(Service callingService, int vendorId, int productId,
                         int maxRetries) {
        this.gpsVendorId = vendorId;
        this.gpsProductId = productId;
        this.callingService = callingService;
        this.maxConnectionRetries = maxRetries + 1;
        this.nbRetriesRemaining = maxConnectionRetries;
        this.appContext = callingService.getApplicationContext();
        this.parser = new NmeaParser(10f, this.appContext);

        locationManager = (LocationManager) callingService.getSystemService(
                Context.LOCATION_SERVICE);

        sharedPreferences =
                PreferenceManager.getDefaultSharedPreferences(callingService);

        deviceSpeed = sharedPreferences.getString(
                USBGpsProviderService.PREF_GPS_DEVICE_SPEED,
                callingService.getString(R.string.defaultGpsDeviceSpeed));

        shouldSetTime = sharedPreferences.getBoolean(
                USBGpsProviderService.PREF_SET_TIME, false);
        timeSetAlready = true;

        defaultDeviceSpeed =
                callingService.getString(R.string.defaultGpsDeviceSpeed);
        setDeviceSpeed = !deviceSpeed.equals(
                callingService.getString(R.string.autoGpsDeviceSpeed));
        sirfGps = sharedPreferences.getBoolean(USBGpsProviderService.PREF_SIRF_GPS,
                false);
        notificationManager = (NotificationManager) callingService.getSystemService(
                Context.NOTIFICATION_SERVICE);
        parser.setLocationManager(locationManager);

        Intent stopIntent =
                new Intent(USBGpsProviderService.ACTION_STOP_GPS_PROVIDER);

        PendingIntent stopPendingIntent = PendingIntent.getService(
                appContext, 0, stopIntent, PendingIntent.FLAG_CANCEL_CURRENT);

        connectionProblemNotificationBuilder =
                new NotificationCompat.Builder(appContext)
                        .setContentIntent(stopPendingIntent)
                        .setSmallIcon(R.drawable.ic_stat_notify);

        Intent restartIntent =
                new Intent(USBGpsProviderService.ACTION_START_GPS_PROVIDER);
        PendingIntent restartPendingIntent = PendingIntent.getService(
                appContext, 0, restartIntent, PendingIntent.FLAG_CANCEL_CURRENT);

        serviceStoppedNotificationBuilder =
                new NotificationCompat.Builder(appContext)
                        .setContentIntent(restartPendingIntent)
                        .setSmallIcon(R.drawable.ic_stat_notify)
                        .setContentTitle(appContext.getString(
                                R.string
                                        .service_closed_because_connection_problem_notification_title))
                        .setContentText(appContext.getString(
                                R.string
                                        .service_closed_because_connection_problem_notification));

        usbManager =
                (UsbManager) callingService.getSystemService(Service.USB_SERVICE);
    }

    private void setDisableReason(int reasonId) {
        disableReason = reasonId;
    }

    /**
     * @return
     */
    public int getDisableReason() {
        return disableReason;
    }

    /**
     * @return true if the bluetooth GPS is enabled
     */
    public synchronized boolean isEnabled() {
        return enabled;
    }

    public boolean isMockLocationEnabled() {
        // Checks if mock location is enabled in settings

        boolean isMockLocation;

        try {
            // If marshmallow or higher then we need to check that this app is set as
            // the provider
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                AppOpsManager opsManager =
                        (AppOpsManager) appContext.getSystemService(Context.APP_OPS_SERVICE);
                isMockLocation = opsManager.checkOp(AppOpsManager.OPSTR_MOCK_LOCATION,
                        android.os.Process.myUid(),
                        BuildConfig.APPLICATION_ID) ==
                        AppOpsManager.MODE_ALLOWED;

            } else {
                // Anything below it then we just need to check the tickbox is checked.
                isMockLocation =
                        !android.provider.Settings.Secure
                                .getString(appContext.getContentResolver(), "mock_location")
                                .equals("0");
            }

        } catch (Exception e) {
            return false;
        }

        return isMockLocation;
    }

    private UsbDevice getDeviceFromAttached() {
        debugLog("Checking all connected devices");
        for (UsbDevice connectedDevice : usbManager.getDeviceList().values()) {

            debugLog("Checking device: " + connectedDevice.getProductId() + " " +
                    connectedDevice.getVendorId());

            if (connectedDevice.getVendorId() == gpsVendorId &
                    connectedDevice.getProductId() == gpsProductId) {
                debugLog("Found correct device");

                return connectedDevice;
            }
        }

        return null;
    }

    /**
     * Enables the USB GPS Provider.
     *
     * @return
     */
    public synchronized boolean enable() {
        IntentFilter permissionFilter = new IntentFilter(ACTION_USB_PERMISSION);
        permissionFilter.addAction(UsbManager.ACTION_USB_DEVICE_DETACHED);
        notificationManager.cancel(
                R.string.service_closed_because_connection_problem_notification_title);

        if (!enabled) {
            log("enabling USB GPS manager");

            if (!isMockLocationEnabled()) {
                if (BuildConfig.DEBUG || debug)
                    Log.e(LOG_TAG, "Mock location provider OFF");
                disable(R.string.msg_mock_location_disabled);
                return this.enabled;

            } else if (PackageManager.PERMISSION_GRANTED !=
                    ContextCompat.checkSelfPermission(
                            callingService,
                            Manifest.permission.ACCESS_FINE_LOCATION)) {
                if (BuildConfig.DEBUG || debug)
                    Log.e(LOG_TAG, "No location permission given");

                log("No location permission given");
                disable(R.string.msg_no_location_permission);
                return this.enabled;

            } else {
                this.enabled = true;
                callingService.registerReceiver(permissionAndDetachReceiver,
                        permissionFilter);
                notificationPool = Executors.newSingleThreadExecutor();
                connectedGps = new ConnectedGps(gpsVendorId, gpsProductId, deviceSpeed);
                connectedGps.requestPermission(gpsVendorId, gpsProductId);
                new Thread(new Runnable() {
                    public void run() {
                        connectedGps.start();
                        //                        connectedGps.run();
                    }
                }).start();

            }
        }
        return this.enabled;
    }

    /**
     * Disables the USB GPS Provider if the maximal number of connection retries
     * is exceeded. This is used when there are possibly non fatal connection
     * problems. In these cases the provider will try to reconnect with the usb
     * device and only after a given retries number will give up and shutdown the
     * service.
     */
    private synchronized void disableIfNeeded() {
        if (enabled) {
            problemNotified = true;
            if (nbRetriesRemaining > 0) {
                // Unable to connect
                if (BuildConfig.DEBUG || debug)
                    Log.e(LOG_TAG, "Connection ended");

                String pbMessage = appContext.getResources().getQuantityString(
                        R.plurals.connection_problem_notification, nbRetriesRemaining,
                        nbRetriesRemaining);

                Notification connectionProblemNotification =
                        connectionProblemNotificationBuilder
                                .setWhen(System.currentTimeMillis())
                                .setContentTitle(appContext.getString(
                                        R.string.connection_problem_notification_title))
                                .setContentText(pbMessage)
                                .setNumber(1 + maxConnectionRetries - nbRetriesRemaining)
                                .build();

                notificationManager.notify(
                        R.string.connection_problem_notification_title,
                        connectionProblemNotification);

            } else {
                disable(R.string.msg_two_many_connection_problems);
            }
        }
    }

    /**
     * Disables the USB GPS provider.
     * <p>
     * It will:
     * <ul>
     * <li>close the connection with the bluetooth device</li>
     * <li>disable the Mock Location Provider used for the Usb GPS</li>
     * <li>stop the UsbGPS4Droid service</li>
     * </ul>
     * The reasonId parameter indicates the reason to close the bluetooth
     * provider. If its value is zero, it's a normal shutdown (normally, initiated
     * by the user). If it's non-zero this value should correspond a valid
     * localized string id (res/values..../...) which will be used to display a
     * notification.
     *
     * @param reasonId the reason to close the bluetooth provider.
     */
    public synchronized void disable(int reasonId) {
        debugLog("disabling USB GPS manager reason: " +
                callingService.getString(reasonId));
        setDisableReason(reasonId);
        disable();
    }

    /**
     * Disables the Usb GPS provider.
     * <p>
     * It will:
     * <ul>
     * <li>close the connection with the bluetooth device</li>
     * <li>disable the Mock Location Provider used for the bluetooth GPS</li>
     * <li>stop the BlueGPS4Droid service</li>
     * </ul>
     * If the bluetooth provider is closed because of a problem, a notification is
     * displayed.
     */
    public synchronized void disable() {
        notificationManager.cancel(R.string.connection_problem_notification_title);

        if (getDisableReason() != 0) {
            NotificationCompat.Builder partialServiceStoppedNotification =
                    serviceStoppedNotificationBuilder.setWhen(System.currentTimeMillis())
                            .setAutoCancel(true)
                            .setContentTitle(appContext.getString(
                                    R.string
                                            .service_closed_because_connection_problem_notification_title))
                            .setContentText(appContext.getString(
                                    R.string
                                            .service_closed_because_connection_problem_notification,
                                    appContext.getString(getDisableReason())));

            // Make the correct notification to direct the user to the correct setting
            if (getDisableReason() == R.string.msg_mock_location_disabled) {
                PendingIntent mockLocationsSettingsIntent = PendingIntent.getActivity(
                        appContext, 0,
                        new Intent(Settings.ACTION_APPLICATION_DEVELOPMENT_SETTINGS),
                        PendingIntent.FLAG_CANCEL_CURRENT);

                partialServiceStoppedNotification
                        .setContentIntent(mockLocationsSettingsIntent)
                        .setStyle(new NotificationCompat.BigTextStyle().bigText(
                                appContext.getString(
                                        R.string
                                                .service_closed_because_connection_problem_notification,
                                        appContext.getString(
                                                R.string.msg_mock_location_disabled_full))));

            } else if (getDisableReason() == R.string.msg_no_location_permission) {
                PendingIntent mockLocationsSettingsIntent = PendingIntent.getActivity(
                        appContext, 0, new Intent(callingService, GpsInfoActivity.class),
                        PendingIntent.FLAG_CANCEL_CURRENT);

                USBGpsApplication.setLocationNotAsked();

                partialServiceStoppedNotification
                        .setContentIntent(mockLocationsSettingsIntent)
                        .setStyle(new NotificationCompat.BigTextStyle().bigText(
                                appContext.getString(
                                        R.string
                                                .service_closed_because_connection_problem_notification,
                                        appContext.getString(
                                                R.string.msg_no_location_permission))));
            }

            Notification serviceStoppedNotification =
                    partialServiceStoppedNotification.build();
            notificationManager.notify(
                    R.string.service_closed_because_connection_problem_notification_title,
                    serviceStoppedNotification);

            sharedPreferences.edit()
                    .putInt(appContext.getString(R.string.pref_disable_reason_key),
                            getDisableReason())
                    .apply();
        }

        if (enabled) {
            debugLog("disabling USB GPS manager");
            callingService.unregisterReceiver(permissionAndDetachReceiver);

            enabled = false;
            //   connectionAndReadingPool.shutdown();

            Runnable closeAndShutdown = new Runnable() {
                @Override
                public void run() {
                    if (connectedGps != null) {
                        connectedGps.close();
                    }
                    //   }
                }
            };

            nmeaListeners.clear();
            disableMockLocationProvider();
            if (notificationPool != null) {
                notificationPool.execute(closeAndShutdown);
                notificationPool.shutdown();
            }
            callingService.stopSelf();

            SharedPreferences.Editor editor = sharedPreferences.edit();
            editor.putBoolean(USBGpsProviderService.PREF_START_GPS_PROVIDER, false);
            editor.apply();

            debugLog("USB GPS manager disabled");
        }
    }

    /**
     * Enables the Mock GPS Location Provider used for the bluetooth GPS.
     * In fact, it delegates to the NMEA parser.
     *
     * @param gpsName the name of the Location Provider to use for the bluetooth
     *                GPS
     * @param force   true if we want to force auto-activation of the mock
     *                location provider (and bypass user preference).
     */
    public void enableMockLocationProvider(String gpsName, boolean force) {
        if (parser != null) {
            debugLog("enabling mock locations provider: " + gpsName);
            parser.enableMockLocationProvider(gpsName, force);
        }
    }

    /**
     * Enables the Mock GPS Location Provider used for the bluetooth GPS.
     * In fact, it delegates to the NMEA parser.
     *
     * @param gpsName the name of the Location Provider to use for the bluetooth
     *                GPS
     */
    public void enableMockLocationProvider(String gpsName) {
        if (parser != null) {
            debugLog("enabling mock locations provider: " + gpsName);
            boolean force = sharedPreferences.getBoolean(
                    USBGpsProviderService.PREF_FORCE_ENABLE_PROVIDER, true);
            parser.enableMockLocationProvider(gpsName, force);
        }
    }

    /**
     * Disables the current Mock GPS Location Provider used for the bluetooth GPS.
     * In fact, it delegates to the NMEA parser.
     *
     * @see NmeaParser#disableMockLocationProvider()
     */
    public void disableMockLocationProvider() {
        if (parser != null) {
            debugLog("disabling mock locations provider");
            parser.disableMockLocationProvider();
        }
    }

    /**
     * Getter use to know if the Mock GPS Listener used for the bluetooth GPS is
     * enabled or not. In fact, it delegates to the NMEA parser.
     *
     * @return true if the Mock GPS Listener used for the bluetooth GPS is
     * enabled.
     * @see NmeaParser#isMockGpsEnabled()
     */
    public boolean isMockGpsEnabled() {
        boolean mockGpsEnabled = false;
        if (parser != null) {
            mockGpsEnabled = parser.isMockGpsEnabled();
        }
        return mockGpsEnabled;
    }

    /**
     * Getter for the name of the current Mock Location Provider in use.
     * In fact, it delegates to the NMEA parser.
     *
     * @return the Mock Location Provider name used for the bluetooth GPS
     * @see NmeaParser#getMockLocationProvider()
     */
    public String getMockLocationProvider() {
        String mockLocationProvider = null;
        if (parser != null) {
            mockLocationProvider = parser.getMockLocationProvider();
        }
        return mockLocationProvider;
    }

    /**
     * Indicates that the bluetooth GPS Provider is out of service.
     * In fact, it delegates to the NMEA parser.
     *
     * @see NmeaParser#setMockLocationProviderOutOfService()
     */
    private void setMockLocationProviderOutOfService() {
        if (parser != null) {
            parser.setMockLocationProviderOutOfService();
        }
    }

    /**
     * Adds an NMEA listener.
     * In fact, it delegates to the NMEA parser.
     *
     * @param listener a {@link NmeaListener} object to register
     * @return true if the listener was successfully added
     */
    public boolean addNmeaListener(NmeaListener listener) {
        if (!nmeaListeners.contains(listener)) {
            debugLog("adding new NMEA listener");
            nmeaListeners.add(listener);
        }
        return true;
    }

    /**
     * Removes an NMEA listener.
     * In fact, it delegates to the NMEA parser.
     *
     * @param listener a {@link NmeaListener} object to remove
     */
    public void removeNmeaListener(NmeaListener listener) {
        debugLog("removing NMEA listener");
        nmeaListeners.remove(listener);
    }

    /**
     * Sets the system time to the given UTC time value
     *
     * @param time UTC value HHmmss.SSS
     */
    @SuppressLint("SimpleDateFormat")
    private void setSystemTime(String time) {
        long parseTime = parser.parseNmeaTime(time);

        Log.v(LOG_TAG, "What?: " + parseTime);

        String timeFormatToybox =
                new SimpleDateFormat("MMddHHmmyyyy.ss").format(new Date(parseTime));

        String timeFormatToolbox =
                new SimpleDateFormat("yyyyMMdd.HHmmss").format(new Date(parseTime));

        debugLog("Setting system time to: " + timeFormatToybox);
        SuperuserManager suManager = SuperuserManager.getInstance();

        debugLog("toolbox date -s " + timeFormatToolbox + "; toybox date " +
                timeFormatToybox +
                "; am broadcast -a android.intent.action.TIME_SET");

        if (suManager.hasPermission()) {
            suManager.asyncExecute(
                    "toolbox date -s " + timeFormatToolbox + "; toybox date " +
                            timeFormatToybox +
                            "; am broadcast -a android.intent.action.TIME_SET");
        } else {
            sharedPreferences.edit()
                    .putBoolean(USBGpsProviderService.PREF_SET_TIME, false)
                    .apply();
        }
    }

    /**
     * Notifies the reception of a NMEA sentence from the USB GPS to registered
     * NMEA listeners.
     *
     * @param nmeaSentence the complete NMEA sentence received from the USB GPS
     *                     (i.e. $....*XY where XY is the checksum)
     * @return true if the input string is a valid NMEA sentence, false otherwise.
     */
    private boolean notifyNmeaSentence(final String nmeaSentence) {
        boolean res = false;
        if (enabled) {
            log("parsing and notifying NMEA sentence: " + nmeaSentence);
            String sentence = null;
            try {
                if (shouldSetTime && !timeSetAlready) {
                    parser.clearLastSentenceTime();
                }

                sentence = parser.parseNmeaSentence(nmeaSentence);

                if (shouldSetTime && !timeSetAlready) {
                    if (!parser.getLastSentenceTime().isEmpty()) {
                        setSystemTime(parser.getLastSentenceTime());
                        timeSetAlready = true;
                    }
                }

            } catch (SecurityException e) {
                if (BuildConfig.DEBUG || debug)
                    Log.e(LOG_TAG, "error while parsing NMEA sentence: " + nmeaSentence,
                            e);
                // a priori Mock Location is disabled
                sentence = null;
                disable(R.string.msg_mock_location_disabled);
            } catch (Exception e) {
                if (BuildConfig.DEBUG || debug) {
                    Log.e(LOG_TAG, "Sentence not parsable");
                    Log.e(LOG_TAG, nmeaSentence);
                }
                e.printStackTrace();
            }
            final String recognizedSentence = sentence;
            final long timestamp = System.currentTimeMillis();
            if (recognizedSentence != null) {
                res = true;
                log("notifying NMEA sentence: " + recognizedSentence);

                ((USBGpsApplication) appContext)
                        .notifyNewSentence(recognizedSentence.replaceAll("(\\r|\\n)", ""));

                synchronized (nmeaListeners) {
                    for (final NmeaListener listener : nmeaListeners) {
                        notificationPool.execute(new Runnable() {
                            @Override
                            public void run() {
                                listener.onNmeaReceived(timestamp, recognizedSentence);
                            }
                        });
                    }
                }
            }
        }
        return res;
    }

    /**
     * Sends a NMEA sentence to the bluetooth GPS.
     *
     * @param command the complete NMEA sentence (i.e. $....*XY where XY is the
     *                checksum).
     */
    public void sendPackagedNmeaCommand(final String command) {
        log("sending NMEA sentence: " + command);
        // connectedGps.write(command);
        log("sent NMEA sentence: " + command);
    }

    /**
     * Sends a SIRF III binary command to the bluetooth GPS.
     *
     * @param commandHexa an hexadecimal string representing a complete binary
     *                    command
     *                    (i.e. with the <em>Start Sequence</em>, <em>Payload
     *                    Length</em>, <em>Payload</em>, <em>Message Checksum</em> and <em>End
     *                    Sequence</em>).
     */
    public void sendPackagedSirfCommand(final String commandHexa) {
        final byte[] command = SirfUtils.genSirfCommand(commandHexa);
        log("sendind SIRF sentence: " + commandHexa);
        // connectedGps.write(command);
        log("sent SIRF sentence: " + commandHexa);
    }

    /**
     * Sends a NMEA sentence to the bluetooth GPS.
     *
     * @param sentence the NMEA sentence without the first "$", the last "*" and
     *                 the checksum.
     */
    public void sendNmeaCommand(String sentence) {
        String command = String.format((Locale) null, "$%s*%02X\r\n", sentence,
                parser.computeChecksum(sentence));
        sendPackagedNmeaCommand(command);
    }

    /**
     * Sends a SIRF III binary command to the bluetooth GPS.
     *
     * @param payload an hexadecimal string representing the payload of the binary
     *                command
     *                (i.e. without <em>Start Sequence</em>, <em>Payload
     *                Length</em>, <em>Message Checksum</em> and <em>End Sequence</em>).
     */
    public void sendSirfCommand(String payload) {
        String command = SirfUtils.createSirfCommandFromPayload(payload);
        sendPackagedSirfCommand(command);
    }

    private void enableNMEA(boolean enable) {
        //            SharedPreferences sharedPreferences =
        //            PreferenceManager.getDefaultSharedPreferences(callingService);
        //            String deviceSpeed =
        //            sharedPreferences.getString(USBGpsProviderService.PREF_GPS_DEVICE_SPEED,
        //            callingService.getString(R.string.defaultGpsDeviceSpeed));
        if (deviceSpeed.equals(
                callingService.getString(R.string.autoGpsDeviceSpeed))) {
            deviceSpeed = callingService.getString(R.string.defaultGpsDeviceSpeed);
        }
        SystemClock.sleep(400);
        if (enable) {
            //                int gll =
            //                (sharedPreferences.getBoolean(USBGpsProviderService.PREF_SIRF_ENABLE_GLL,
            //                false)) ? 1 : 0 ; int vtg =
            //                (sharedPreferences.getBoolean(USBGpsProviderService.PREF_SIRF_ENABLE_VTG,
            //                false)) ? 1 : 0 ; int gsa =
            //                (sharedPreferences.getBoolean(USBGpsProviderService.PREF_SIRF_ENABLE_GSA,
            //                false)) ? 5 : 0 ; int gsv =
            //                (sharedPreferences.getBoolean(USBGpsProviderService.PREF_SIRF_ENABLE_GSV,
            //                false)) ? 5 : 0 ; int zda =
            //                (sharedPreferences.getBoolean(USBGpsProviderService.PREF_SIRF_ENABLE_ZDA,
            //                false)) ? 1 : 0 ; int mss = 0; int epe = 0; int gga = 1;
            //                int rmc = 1;
            //                String command =
            //                getString(R.string.sirf_bin_to_nmea_38400_alt, gga, gll,
            //                gsa, gsv, rmc, vtg, mss, epe, zda); String command =
            //                getString(R.string.sirf_bin_to_nmea_alt, gga, gll, gsa,
            //                gsv, rmc, vtg, mss, epe, zda,
            //                Integer.parseInt(deviceSpeed));
            String command = callingService.getString(R.string.sirf_bin_to_nmea);
            this.sendSirfCommand(command);
        } else {
            //                this.sendNmeaCommand(callingService.getString(R.string.sirf_nmea_to_binary));
            this.sendNmeaCommand(callingService.getString(
                    R.string.sirf_nmea_to_binary_alt, Integer.parseInt(deviceSpeed)));
        }
        SystemClock.sleep(400);
    }

    private void enableNmeaGGA(boolean enable) {
        if (enable) {
            this.sendNmeaCommand(callingService.getString(R.string.sirf_nmea_gga_on));
        } else {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_gga_off));
        }
    }

    private void enableNmeaGLL(boolean enable) {
        if (enable) {
            this.sendNmeaCommand(callingService.getString(R.string.sirf_nmea_gll_on));
        } else {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_gll_off));
        }
    }

    private void enableNmeaGSA(boolean enable) {
        if (enable) {
            this.sendNmeaCommand(callingService.getString(R.string.sirf_nmea_gsa_on));
        } else {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_gsa_off));
        }
    }

    private void enableNmeaGSV(boolean enable) {
        if (enable) {
            this.sendNmeaCommand(callingService.getString(R.string.sirf_nmea_gsv_on));
        } else {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_gsv_off));
        }
    }

    private void enableNmeaRMC(boolean enable) {
        if (enable) {
            this.sendNmeaCommand(callingService.getString(R.string.sirf_nmea_rmc_on));
        } else {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_rmc_off));
        }
    }

    private void enableNmeaVTG(boolean enable) {
        if (enable) {
            this.sendNmeaCommand(callingService.getString(R.string.sirf_nmea_vtg_on));
        } else {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_vtg_off));
        }
    }

    private void enableNmeaZDA(boolean enable) {
        if (enable) {
            this.sendNmeaCommand(callingService.getString(R.string.sirf_nmea_zda_on));
        } else {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_zda_off));
        }
    }

    private void enableSBAS(boolean enable) {
        if (enable) {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_sbas_on));
        } else {
            this.sendNmeaCommand(
                    callingService.getString(R.string.sirf_nmea_sbas_off));
        }
    }

    public void enableSirfConfig(final Bundle extra) {
        debugLog("spooling SiRF config: " + extra);
        if (isEnabled()) {
            notificationPool.execute(new Runnable() {
                @Override
                public void run() {
                    while ((enabled) && ((!connected) || (connectedGps == null) ||
                            (!connectedGps.isReady()))) {
                        debugLog("writing thread is not ready");
                        SystemClock.sleep(500);
                    }
                    if (isEnabled() && (connected) && (connectedGps != null) &&
                            (connectedGps.isReady())) {
                        debugLog("init SiRF config: " + extra);
                        if (extra.containsKey(USBGpsProviderService.PREF_SIRF_ENABLE_GGA)) {
                            enableNmeaGGA(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_GGA, true));
                        }
                        if (extra.containsKey(USBGpsProviderService.PREF_SIRF_ENABLE_RMC)) {
                            enableNmeaRMC(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_RMC, true));
                        }
                        if (extra.containsKey(USBGpsProviderService.PREF_SIRF_ENABLE_GLL)) {
                            enableNmeaGLL(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_GLL, false));
                        }
                        if (extra.containsKey(USBGpsProviderService.PREF_SIRF_ENABLE_VTG)) {
                            enableNmeaVTG(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_VTG, false));
                        }
                        if (extra.containsKey(USBGpsProviderService.PREF_SIRF_ENABLE_GSA)) {
                            enableNmeaGSA(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_GSA, false));
                        }
                        if (extra.containsKey(USBGpsProviderService.PREF_SIRF_ENABLE_GSV)) {
                            enableNmeaGSV(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_GSV, false));
                        }
                        if (extra.containsKey(USBGpsProviderService.PREF_SIRF_ENABLE_ZDA)) {
                            enableNmeaZDA(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_ZDA, false));
                        }
                        if (extra.containsKey(
                                USBGpsProviderService.PREF_SIRF_ENABLE_STATIC_NAVIGATION)) {
                            enableStaticNavigation(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_STATIC_NAVIGATION,
                                    false));
                        } else if (extra.containsKey(
                                USBGpsProviderService.PREF_SIRF_ENABLE_NMEA)) {
                            enableNMEA(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_NMEA, true));
                        }
                        if (extra.containsKey(
                                USBGpsProviderService.PREF_SIRF_ENABLE_SBAS)) {
                            enableSBAS(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_SBAS, true));
                        }
                        debugLog("initialized SiRF config: " + extra);
                    }
                }
            });
        }
    }

    public void enableSirfConfig(final SharedPreferences extra) {
        debugLog("spooling SiRF config: " + extra);
        if (isEnabled()) {
            notificationPool.execute(new Runnable() {
                @Override
                public void run() {
                    while ((enabled) && ((!connected) || (connectedGps == null) ||
                            (!connectedGps.isReady()))) {
                        debugLog("writing thread is not ready");
                        SystemClock.sleep(500);
                    }
                    if (isEnabled() && (connected) && (connectedGps != null) &&
                            (connectedGps.isReady())) {
                        debugLog("init SiRF config: " + extra);
                        if (extra.contains(USBGpsProviderService.PREF_SIRF_ENABLE_GLL)) {
                            enableNmeaGLL(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_GLL, false));
                        }
                        if (extra.contains(USBGpsProviderService.PREF_SIRF_ENABLE_VTG)) {
                            enableNmeaVTG(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_VTG, false));
                        }
                        if (extra.contains(USBGpsProviderService.PREF_SIRF_ENABLE_GSA)) {
                            enableNmeaGSA(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_GSA, false));
                        }
                        if (extra.contains(USBGpsProviderService.PREF_SIRF_ENABLE_GSV)) {
                            enableNmeaGSV(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_GSV, false));
                        }
                        if (extra.contains(USBGpsProviderService.PREF_SIRF_ENABLE_ZDA)) {
                            enableNmeaZDA(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_ZDA, false));
                        }
                        if (extra.contains(
                                USBGpsProviderService.PREF_SIRF_ENABLE_STATIC_NAVIGATION)) {
                            enableStaticNavigation(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_STATIC_NAVIGATION,
                                    false));
                        } else if (extra.contains(
                                USBGpsProviderService.PREF_SIRF_ENABLE_NMEA)) {
                            enableNMEA(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_NMEA, true));
                        }
                        if (extra.contains(USBGpsProviderService.PREF_SIRF_ENABLE_SBAS)) {
                            enableSBAS(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_SBAS, true));
                        }
                        sendNmeaCommand(
                                callingService.getString(R.string.sirf_nmea_gga_on));
                        sendNmeaCommand(
                                callingService.getString(R.string.sirf_nmea_rmc_on));
                        if (extra.contains(USBGpsProviderService.PREF_SIRF_ENABLE_GGA)) {
                            enableNmeaGGA(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_GGA, true));
                        }
                        if (extra.contains(USBGpsProviderService.PREF_SIRF_ENABLE_RMC)) {
                            enableNmeaRMC(extra.getBoolean(
                                    USBGpsProviderService.PREF_SIRF_ENABLE_RMC, true));
                        }
                    }
                }
            });
        }
    }

    private void enableStaticNavigation(boolean enable) {
        SharedPreferences sharedPreferences =
                PreferenceManager.getDefaultSharedPreferences(callingService);
        boolean isInNmeaMode = sharedPreferences.getBoolean(
                USBGpsProviderService.PREF_SIRF_ENABLE_NMEA, true);
        if (isInNmeaMode) {
            enableNMEA(false);
        }
        if (enable) {
            this.sendSirfCommand(
                    callingService.getString(R.string.sirf_bin_static_nav_on));
        } else {
            this.sendSirfCommand(
                    callingService.getString(R.string.sirf_bin_static_nav_off));
        }
        if (isInNmeaMode) {
            enableNMEA(true);
        }
    }

    private void log(String message) {
        if (BuildConfig.DEBUG)
            Log.d(LOG_TAG, message);
    }

    private void debugLog(String message) {
        if (BuildConfig.DEBUG || debug)
            Log.d(LOG_TAG, message);
    }

    public void setTalkerIDFilter(final String talkerID) {
        if (talkerID.length() != 2 && talkerID.length() != 0)
        {
            debugLog("invalid Talker ID");
            return;
        }
        parser.talkerFilter = talkerID;
    }
}
