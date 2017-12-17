package org.broeuschmeul.android.gps.usb.provider.ui;

import android.content.Intent;
import android.content.SharedPreferences;
import android.content.res.Configuration;
import android.location.Location;
import android.os.Bundle;
import android.preference.PreferenceManager;
import android.support.v7.widget.SwitchCompat;
import android.support.v7.widget.Toolbar;
import android.text.Layout;
import android.text.TextUtils;
import android.text.method.ScrollingMovementMethod;
import android.view.Menu;
import android.view.MenuInflater;
import android.view.MenuItem;
import android.view.View;
import android.widget.CompoundButton;
import android.widget.TextView;

import org.broeuschmeul.android.gps.nmea.util.NmeaParser;
import org.broeuschmeul.android.gps.usb.provider.USBGpsApplication;
import org.broeuschmeul.android.gps.usb.provider.R;
import org.broeuschmeul.android.gps.usb.provider.driver.USBGpsProviderService;

import java.text.DecimalFormat;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Locale;

/**
 * Created by Oliver Bell 5/12/15
 *
 * This activity displays a log, as well as the GPS info. If the users device is
 * large enough and in landscape, the settings fragment will be shown alongside
 */

public class GpsInfoActivity extends USBGpsBaseActivity implements
        USBGpsApplication.ServiceDataListener {

    private SharedPreferences sharedPreferences;
    private static final String TAG = GpsInfoActivity.class.getSimpleName();

    private USBGpsApplication application;

    private SwitchCompat startSwitch;
    private TextView numSatellites;
    private TextView accuracyText;
    private TextView locationText;
    private TextView elevationText;
    private TextView logText;
    private TextView timeText;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        if (isDoublePane()) {
            savedInstanceState = null;
            setContentView(R.layout.activity_info_double);
        } else {
            setContentView(R.layout.activity_info);
        }

        super.onCreate(savedInstanceState);

        Toolbar toolbar = (Toolbar) findViewById(R.id.toolbar);
        setSupportActionBar(toolbar);

        sharedPreferences = PreferenceManager.getDefaultSharedPreferences(this);

        application = (USBGpsApplication) getApplication();

        setupUI();

        if (isDoublePane()) {
            showSettingsFragment(R.id.settings_holder, false);
        }
    }

    private void setupUI() {
        if (!isDoublePane()) {
            startSwitch = (SwitchCompat) findViewById(R.id.service_start_switch);
            startSwitch.setOnCheckedChangeListener(new CompoundButton.OnCheckedChangeListener() {
                @Override
                public void onCheckedChanged(CompoundButton buttonView, boolean isChecked) {
                    sharedPreferences
                            .edit()
                            .putBoolean(USBGpsProviderService.PREF_START_GPS_PROVIDER, isChecked)
                            .apply();
                }
            });
        }

        numSatellites = (TextView) findViewById(R.id.num_satellites_text);
        accuracyText = (TextView) findViewById(R.id.accuracy_text);
        locationText = (TextView) findViewById(R.id.location_text);
        elevationText = (TextView) findViewById(R.id.elevation_text);
        timeText = (TextView) findViewById(R.id.gps_time_text);

        logText = (TextView) findViewById(R.id.log_box);
        logText.setMovementMethod(new ScrollingMovementMethod());

    }

    private boolean isDoublePane() {
        return (getResources().getConfiguration().screenLayout
                & Configuration.SCREENLAYOUT_SIZE_MASK) >= Configuration.SCREENLAYOUT_SIZE_LARGE &&
                getResources()
                        .getConfiguration()
                        .orientation == Configuration.ORIENTATION_LANDSCAPE;
    }

    private void updateData() {
        boolean running =
                sharedPreferences.getBoolean(USBGpsProviderService.PREF_START_GPS_PROVIDER, false);

        if (!isDoublePane()) {
            startSwitch.setChecked(
                    running
            );
        }

        String accuracyValue = "N/A";
        String numSatellitesValue = "N/A";
        String lat = "N/A";
        String lon = "N/A";
        String elevation = "N/A";
        String gpsTime = "N/A";
        String systemTime = "N/A";

        Location location = application.getLastLocation();
        if (!running) {
            location = null;
        }

        if (location != null) {
            accuracyValue = String.valueOf(location.getAccuracy());
            if (location.getExtras() != null) {
                numSatellitesValue = String.valueOf(location.getExtras().getInt(NmeaParser.SATELLITE_KEY));
            }
            DecimalFormat df = new DecimalFormat("#.#####");
            lat = df.format(location.getLatitude());
            lon = df.format(location.getLongitude());
            elevation = String.valueOf(location.getAltitude());

            gpsTime = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss.SSS", Locale.US)
                    .format(new Date(location.getTime()));

            systemTime = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss.SSS", Locale.US)
                    .format(new Date(location.getExtras().getLong(NmeaParser.SYSTEM_TIME_FIX)));
        }

        numSatellites.setText(
                getString(R.string.number_of_satellites_placeholder, numSatellitesValue)
        );
        accuracyText.setText(getString(R.string.accuracy_placeholder, accuracyValue));
        locationText.setText(getString(R.string.location_placeholder, lat, lon));
        elevationText.setText(getString(R.string.elevation_placeholder, elevation));
        timeText.setText(getString(R.string.gps_time_placeholder, gpsTime, systemTime));
        updateLog();
    }

    public void updateGpsTime() {

    }

    public void updateLog() {
        logText.scrollTo(0, 0);
        logText.setText(TextUtils.join("\n", application.getSentenceLog()));
        Layout layout = logText.getLayout();
        if (layout != null) {
            int lineTop = layout.getLineTop(logText.getLineCount());
            final int scrollAmount = lineTop + logText.getPaddingTop()
                    + logText.getPaddingBottom() - logText.getBottom() + logText.getTop();
            if (scrollAmount > 0) {
                logText.scrollBy(0, scrollAmount);
            } else {
                logText.scrollTo(0, 0);
            }
        }
    }

    @Override
    public void onResume() {
        updateData();
        sharedPreferences.registerOnSharedPreferenceChangeListener(this);
        ((USBGpsApplication) getApplication()).registerServiceDataListener(this);
        super.onResume();
    }

    @Override
    public void onPause() {
        sharedPreferences.unregisterOnSharedPreferenceChangeListener(this);
        ((USBGpsApplication) getApplication()).unregisterServiceDataListener(this);
        super.onPause();
    }

    @Override
    public boolean onCreateOptionsMenu(Menu menu) {
        if (!isDoublePane()) {
            MenuInflater inflater = getMenuInflater();
            inflater.inflate(R.menu.menu_main, menu);
        }
        return true;
    }

    @Override
    public boolean onOptionsItemSelected(MenuItem item) {
        switch (item.getItemId()) {
            case R.id.action_settings:
                startActivity(new Intent(this, SettingsActivity.class));
                return true;
        }
        return super.onOptionsItemSelected(item);
    }

    @Override
    public void onNewSentence(String sentence) {
        updateLog();
    }

    @Override
    public void onLocationNotified(Location location) {
        updateData();
    }

    @Override
    public void onSharedPreferenceChanged(SharedPreferences sharedPreferences, String key) {
        if (key.equals(USBGpsProviderService.PREF_START_GPS_PROVIDER)) {
            updateData();
        }

        super.onSharedPreferenceChanged(sharedPreferences, key);
    }
}
