// SPDX-License-Identifier: GPL-3.0-only
// Copyright (C) 2026 Median Browser contributors

package com.xinyv.median;

import static com.xinyv.median.ByteFormat.humanBytes;

import android.Manifest;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.ActivityNotFoundException;
import android.app.DownloadManager;
import android.app.PictureInPictureParams;
import android.print.PrintManager;
import android.content.Context;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.res.ColorStateList;
import android.content.pm.ActivityInfo;
import android.content.pm.PackageInfo;
import android.content.pm.PackageManager;
import android.database.Cursor;
import android.graphics.Color;
import android.graphics.drawable.GradientDrawable;
import android.net.Uri;
import android.net.http.SslError;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.os.Message;
import android.os.Parcel;
import android.os.Process;
import android.os.SystemClock;
import android.provider.Settings;
import android.text.InputType;
import android.util.Rational;
import android.view.Gravity;
import android.view.KeyEvent;
import android.view.MotionEvent;
import android.view.View;
import android.view.ViewGroup;
import android.view.ViewConfiguration;
import android.view.ViewPropertyAnimator;
import android.view.Window;
import android.view.WindowManager;
import android.view.inputmethod.EditorInfo;
import android.view.inputmethod.InputMethodManager;
import android.webkit.CookieManager;
import android.webkit.DownloadListener;
import android.webkit.GeolocationPermissions;
import android.webkit.HttpAuthHandler;
import android.webkit.JsPromptResult;
import android.webkit.PermissionRequest;
import android.webkit.SslErrorHandler;
import android.webkit.ValueCallback;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebResourceError;
import android.webkit.WebSettings;
import android.webkit.WebStorage;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.webkit.WebViewDatabase;
import android.widget.Button;
import android.widget.AdapterView;
import android.widget.BaseAdapter;
import android.widget.CheckBox;
import android.widget.EditText;
import android.widget.FrameLayout;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ListView;
import android.widget.ProgressBar;
import android.widget.ScrollView;
import android.widget.Switch;
import android.widget.TextView;
import android.widget.Toast;

import androidx.webkit.ScriptHandler;
import androidx.webkit.WebSettingsCompat;
import androidx.webkit.WebViewCompat;
import androidx.webkit.WebViewFeature;
import androidx.webkit.WebViewNavigationWarmupCompat;
import androidx.webkit.WebViewStartupCompat;

import org.json.JSONArray;
import org.json.JSONObject;
import org.json.JSONTokener;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.InputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.ThreadPoolExecutor;
import java.security.MessageDigest;
import java.util.Iterator;

public final class MainActivity extends Activity implements Runnable {
    private static final int FILE_CHOOSER_REQUEST = 401;
    private static final int BACKUP_EXPORT_REQUEST = 402;
    private static final int BACKUP_IMPORT_REQUEST = 403;
    private static final int WEB_PERMISSION_REQUEST = 404;
    private static final int GEOLOCATION_PERMISSION_REQUEST = 405;
    private static final int VAULT_UNLOCK_REQUEST = 406;
    private static final long VAULT_UNLOCK_WINDOW_MS = 105_000L;
    private static final int FULL_BACKUP_EXPORT_REQUEST = 407;
    private static final int FULL_BACKUP_IMPORT_REQUEST = 408;
    private static final int HOME_WALLPAPER_REQUEST = HomeCustomizationController.REQUEST_WALLPAPER;
    private static final int HOME_LOGO_REQUEST = HomeCustomizationController.REQUEST_LOGO;
    private static final int QR_SCAN_REQUEST = 411;
    private static final int DOWNLOAD_DIRECTORY_REQUEST = 412;
    private static final String PREFS = "median_browser_v2";
    private static final String HOME_URL = "https://median.invalid/";
    private static final String QR_URL = "https://median.invalid/scan";
    private static final String STATE_WEBVIEW = "median.webview.state";
    private static final String STATE_TABS = "median.tabs.state";
    private static final String PREF_STARTUP_DIAGNOSTIC = "startup_diagnostic_v1";
    private static final int MAX_TABS = 64;
    // Automatic subscription refresh is useful after startup, but its network traffic should not
    // compete with the first page's remaining resources.
    private static final long FILTER_SUBSCRIPTION_IDLE_DELAY_MS = 3200L;
    // A cold Chromium provider can take longer than one frame to dispatch its first callback.
    // Retrying at 450 ms often opens a second socket before the original request is accepted;
    // wait long enough for the normal acknowledgement path and keep the retry one-shot.
    private static final long INITIAL_NAVIGATION_ACK_MS = 1400L;
    private static final int MAX_WEBVIEW_STATE_BYTES = 262144;
    private static final int MAX_TAB_METADATA_BYTES = 262144;
    private static final int MAX_SAVED_TAB_URL_CHARS = 16384;
    private static final int MAX_SAVED_TAB_TITLE_CHARS = 256;
    // The bridge is transported through window.prompt. Reject oversized messages before
    // JSONObject allocates a tree on the UI thread.
    private static final int SCRIPT_BRIDGE_MAX_MESSAGE_CHARS = 256 * 1024;
    private static final int SCRIPT_ASSET_MAX_BYTES = 8 * 1024 * 1024;
    private static final long SCRIPT_ASSET_TOTAL_MAX_BYTES = 32L * 1024L * 1024L;
    private static final byte[] EMPTY_RESPONSE = new byte[0];
    private static final String MODE_PERFORMANCE = "performance";
    private static final String MODE_STANDARD = "standard";
    private static final String MODE_POWER_SAVE = "power_save";

    // Track user navigation to prevent unwanted home page redirects
    private boolean userHasNavigated = false;
    private static final int SHEET_ROW_NAVIGATE = 0;
    private static final int SHEET_ROW_ACTION = 1;
    private static final int SHEET_ROW_TOGGLE_OFF = 2;
    private static final int SHEET_ROW_TOGGLE_ON = 3;
    private static final int SHEET_TAG_SURFACE = 1;
    private static final int SHEET_TAG_HANDLE = 2;
    private static final int SHEET_TAG_PRIMARY = 3;
    private static final int SHEET_TAG_MUTED = 4;
    private static final int SHEET_TAG_ACCENT = 5;
    private static final int SHEET_TAG_ROW = 6;
    private static final int SHEET_TAG_PLAIN_SURFACE = 7;
    private static final String PREF_COMMUNITY_NOTICE_SHOWN = "community_notice_shown_v1";
    private static final String GITHUB_URL = "https://github.com/bi-box/Median";
    private static final String TELEGRAM_URL = "https://telegram.me/MedianBeta";
    private static final String COMMUNITY_INFO =
            "Mises à jour du projet, versions et retours :\n" + GITHUB_URL +
            "\n\nCanal de test officiel et annonces :\n" + TELEGRAM_URL;

    // Modern color palette with refined tonal progression
    private static final int WHITE = 0xFFFCFCFD;
    private static final int TEXT = 0xFF0A0D12;
    private static final int MUTED = 0xFF6B7280;
    private static final int SURFACE = 0xFFF4F6F8;
    private static final int BLUE = 0xFF3B82F6;
    private static final int DARK_WEB = 0xFF05070C;
    private static final int DARK_SHEET = 0xFF0F131C;
    private static final int DARK_OVERLAY = 0xCC000000;
    private static final int LIGHT_OVERLAY = 0x4D000000;
    private static final int DARK_BACKGROUND = 0xFF0A0D12;
    private static final int DARK_CARD = 0xFF161D2B;
    private static final int DARK_SURFACE = 0xFF1E2636;
    private static final int DARK_TEXT = 0xFFF0F1F3;
    private static final int DARK_MUTED = 0xFF9CA3AF;
    private static final int DARK_ACCENT = 0xFF60A5FA;

    private FrameLayout rootFrame;
    private FrameLayout browserChrome;
    private LinearLayout topBar;
    private LinearLayout bottomBar;
    private View statusBarBackground;
    private View navigationBarBackground;
    private FrameLayout webContainer;
    private WebView webView;
    private EditText addressBar;
    private LinearLayout addressPill;
    private ProgressBar progressBar;
    private BrowserIconView backButton;
    private BrowserIconView forwardButton;
    private BrowserIconView tabButton;
    private BrowserIconView shieldButton;
    private BrowserIconView refreshButton;
    private View startupSurface;
    private TextView startupStatus;
    private ValueCallback<Uri[]> fileChooserCallback;
    private WebView fileChooserView;
    private String fileChooserDocumentUrl = "";
    private String homeToken;
    private String adPickToken;
    private String qrToken;
    private final Handler uiHandler = new Handler(Looper.getMainLooper());
    private ExecutorService startupExecutor;
    private StartupDataLoader startupDataLoader;
    private ExecutorService webViewStartupExecutor;
    private String webViewStartupDiagnostic = "Init compatible";
    private ThreadPoolExecutor navigationExecutor;
    private ExecutorService scriptExecutor;
    private ExecutorService scriptNetworkExecutor;
    private UserScriptNetwork userScriptNetwork;
    private boolean activityResumed;
    private volatile boolean activityDestroyed;
    private boolean startupReady;
    private final long startupStartedAt = SystemClock.elapsedRealtime();
    private long startupReadyAt;
    private long startupNavigationAt;
    private volatile long scriptRegistrationGeneration;
    private final StartupReadiness startupReadiness = new StartupReadiness(
            StartupReadiness.VIEW | StartupReadiness.DATA | StartupReadiness.FILTERS | StartupReadiness.RESUMED);
    private Bundle startupSavedState;
    private String startupExternalUrl = "";
    private String startupScriptToken = "";
    private List<UserScriptStore.DocumentStartPayload> startupScriptPayloads = Collections.emptyList();
    private boolean startupScriptPayloadsApplied;
    private String pendingStartupInput;
    // The first navigation must not wait for the large local stores. Their decoded snapshots
    // are attached later on the UI thread and only refresh data that is actually visible.
    private boolean startupFastPosted;
    private boolean startupFastStarted;
    private boolean startupDataReady;
    private boolean startupCustomRulesReady;
    private boolean startupSessionPending;
    private long lastExecutorBusyToastAt;
    private boolean deferredStartupPending;
    private boolean deferredStartupComplete;
    private final Runnable deferredStartup = new Runnable() {
        @Override public void run() {
            deferredStartupPending = false;
            if (deferredStartupComplete || isFinishing() || !activityResumed) return;
            // Local rules start alongside provider initialization. Only subscription network
            // refresh waits for the completed page's idle window.
            if (!pageFinished || !isNetworkPage(currentPageUrl)) return;
            deferredStartupComplete = true;
            updateFilterSubscriptions(true);
        }
    };
    private View customView;
    private View activeOverlay;
    private View activeOverlayPanel;
    private boolean activeOverlaySheet;
    private boolean overlayDismissInProgress;
    private Runnable activeOverlayBackAction;
    private Runnable activeOverlayDismissAction;
    private Object predictiveBackCallback;
    private HomeCustomizationController homeCustomizationController;
    private Runnable bookmarkFolderRootBackAction;
    private Runnable filterCenterBackAction;
    private Runnable scriptCenterBackAction;
    private Runnable passwordMenuBackAction;
    private WebChromeClient.CustomViewCallback customViewCallback;
    private int previousOrientation;
    private int previousSystemUi;

    private final AdBlockEngine adBlock = new AdBlockEngine();
    private AdBlockRuleLoader adBlockRuleLoader;
    private NavigationConnectionHints connectionHints;
    private UserScriptStore scriptStore;
    private final MediaResourceSniffer mediaSniffer = new MediaResourceSniffer();
    private long liveMediaCaptureSequence = -1L;
    private BrowserServices services;
    private BrowserDataStore dataStore;
    private BookmarkFolderStore bookmarkFolders;
    private HomeImageStore homeImages;
    private FaviconStore favicons;
    private SearchEngineStore searchEngines;
    private SiteSettingsStore siteSettingsStore;
    private DeviceProfile deviceProfile;
    private SharedPreferences prefs;
    private volatile boolean adBlockEnabled;
    private boolean desktopMode;
    private boolean nightMode;
    private boolean edgeNavigationEnabled;
    private boolean httpsOnly;
    private boolean restoreTabs;
    private boolean acceptThirdPartyCookies;
    private String searchEngine;
    private volatile String performanceMode;
    private volatile Set<String> siteExceptions;
    private int blockedAtPageStart;
    private volatile boolean scriptDownloadInProgress;
    private final ConcurrentHashMap<WebView, String> scriptBridgeTokens = new ConcurrentHashMap<WebView, String>();
    private final ConcurrentHashMap<WebView, Long> scriptDocumentGenerations = new ConcurrentHashMap<WebView, Long>();
    private final ConcurrentHashMap<WebView, List<ScriptHandler>> scriptHandlers =
            new ConcurrentHashMap<WebView, List<ScriptHandler>>();
    private final ConcurrentHashMap<WebView, String> scriptTabIds = new ConcurrentHashMap<WebView, String>();
    private final ScriptTabStateStore scriptTabValues = new ScriptTabStateStore();
    private long scriptTabSequence;
    private final Set<WebView> documentStartScriptViews = ConcurrentHashMap.newKeySet();
    private volatile boolean filterUpdateInProgress;
    private boolean autoPictureInPicture;
    private boolean immersiveScrollChrome;
    private boolean clearDataOnExit;
    private boolean exitDataCleared;
    private boolean chromeHiddenByScroll;
    private boolean immersivePageLayout;
    private boolean immersiveGestureActive;
    private boolean immersiveGestureDirectionLocked;
    private boolean immersiveGestureVertical;
    private float immersiveGestureDownX;
    private float immersiveGestureDownY;
    private float immersiveGestureY;
    private float immersiveGestureOffset;
    private boolean immersiveGestureStartHidden;
    private boolean keyboardVisible;
    private int legacyKeyboardOverlap;
    private int systemKeyboardBottom;
    private boolean systemKeyboardVisible;
    private int systemInsetLeft;
    private int systemInsetTop;
    private int systemInsetRight;
    private int systemInsetBottom;
    private boolean cleanTrackingParameters;
    private boolean passwordAutofillEnabled;
    private boolean passwordSavePromptsEnabled;
    private final CookieFlushScheduler cookieFlushScheduler = new CookieFlushScheduler();
    private boolean compatibilityDialogShowing;
    private String lastCompatibilityOfferHost = "";
    private long lastCompatibilityOfferAt;
    private boolean rendererRecoveryPending;
    // WebView request callbacks run off the UI thread. Never call WebView methods there.
    private volatile String currentPageUrl = HOME_URL;
    private volatile String currentPageHost = "";
    private boolean homeThemeRepairPending;
    private final ConcurrentHashMap<WebView, String> pageHosts = new ConcurrentHashMap<WebView, String>();
    private final ConcurrentHashMap<WebView, String> startedPageUrls = new ConcurrentHashMap<WebView, String>();
    private final ConcurrentHashMap<WebView, Boolean> adBlockActiveByView = new ConcurrentHashMap<WebView, Boolean>();
    private final ConcurrentHashMap<WebView, String> mobileUserAgents = new ConcurrentHashMap<WebView, String>();
    private final ConcurrentHashMap<WebView, String> appliedSiteSettings = new ConcurrentHashMap<WebView, String>();
    private final ConcurrentHashMap<WebView, InitialNavigationGuard> initialNavigationGuards =
            new ConcurrentHashMap<WebView, InitialNavigationGuard>();
    private final ConcurrentHashMap<WebView, NavigationGestureGuard> navigationGestureGuards =
            new ConcurrentHashMap<WebView, NavigationGestureGuard>();
    private final ConcurrentHashMap<WebView, String> navigationSourceDocuments = new ConcurrentHashMap<WebView, String>();
    private final ConcurrentHashMap<WebView, MainFrameNavigationContext> mainFrameNavigationContexts =
            new ConcurrentHashMap<WebView, MainFrameNavigationContext>();
    private final ConcurrentHashMap<WebView, String> popupSourceDocuments = new ConcurrentHashMap<WebView, String>();
    private final ConcurrentHashMap<WebView, Object> cosmeticInjected = new ConcurrentHashMap<WebView, Object>();
    private final Set<WebView> unresponsiveWebViews = ConcurrentHashMap.newKeySet();
    private final Set<WebView> trustedHomeViews = ConcurrentHashMap.newKeySet();
    private final Set<WebView> customHomeViews = ConcurrentHashMap.newKeySet();
    private final Set<WebView> adPickerViews = ConcurrentHashMap.newKeySet();
    private static final class AdPickerSession {
        final String documentUrl;
        AdPickerSession(String url) { documentUrl = navigationDocumentUrl(url); }
    }
    private final ConcurrentHashMap<WebView, AdPickerSession> adPickerSessions = new ConcurrentHashMap<WebView, AdPickerSession>();
    private final Set<WebView> qrScannerViews = ConcurrentHashMap.newKeySet();
    private final Set<String> faviconFetchQueued = ConcurrentHashMap.newKeySet();
    private final ConcurrentHashMap<WebView, String> renderedHomeKeys = new ConcurrentHashMap<WebView, String>();
    private String cachedHomeKey = "";
    private String cachedHomeHtml = "";

    private volatile long navigationSequence;
    private boolean pageCommitted;
    private boolean pageFinished;
    private PreparedInjection preparedInjection;
    private long injectedStartSequence = -1;
    private long injectedEndSequence = -1;
    private boolean chromeUpdatePending;
    private boolean progressUpdatePending;
    private boolean hotTrimPending;
    private int pendingProgress = 100;
    private int renderedProgress = -1;
    private String renderedAddress;
    private Boolean renderedBackEnabled;
    private Boolean renderedForwardEnabled;
    private Integer renderedTabCount;
    private Boolean renderedShieldActive;
    private PermissionRequest pendingPermissionRequest;
    private String[] pendingWebPermissionResources;
    private WebView pendingPermissionView;
    private String pendingPermissionOrigin;
    private GeolocationPermissions.Callback pendingGeolocationCallback;
    private String pendingGeolocationOrigin;
    private WebView pendingGeolocationView;
    private Runnable pendingVaultAction;
    private Runnable pendingVaultCancelAction;
    private long vaultUnlockedUntil;
    private PasswordVault.Credential stagedCredential;
    private long stagedCredentialAt;
    private String lastCredentialOfferKey = "";
    private long lastCredentialOfferAt;
    private final Runnable vaultLock = new Runnable() {
        @Override public void run() {
            vaultUnlockedUntil = 0L;
            if (stagedCredential != null) stagedCredential.clear();
            stagedCredential = null;
            stagedCredentialAt = 0L;
            if (services != null) services.lockVault();
        }
    };

    private static final class PreparedInjection {
        final long sequence;
        final String url;
        final String startScript;
        final String endScript;

        PreparedInjection(long sequence, String url, String startScript, String endScript) {
            this.sequence = sequence;
            this.url = url;
            this.startScript = startScript;
            this.endScript = endScript;
        }
    }

    private static final class BrowserTab {
        String scriptTabId;
        String title = "Nouvel onglet";
        String url = HOME_URL;
        Bundle state;
        WebView liveView;
        long lastActiveAt;
        boolean pinned;
    }

    private final ArrayList<BrowserTab> tabs = new ArrayList<BrowserTab>();
    private final ArrayList<BrowserTab> closedTabs = new ArrayList<BrowserTab>();
    private int currentTabIndex = 0;

    @Override
    protected void onCreate(Bundle state) {
        // Select the real Activity theme before WebView or window content is constructed. WebView
        // reads isLightTheme to expose prefers-color-scheme to websites.
        prefs = getSharedPreferences(PREFS, MODE_PRIVATE);
        nightMode = prefs.getBoolean("night_mode", false);
        setTheme(nightMode ? R.style.AppThemeDark : R.style.AppTheme);
        super.onCreate(state);
        // Prepare the provider before any WebView API, in parallel with native UI and disk work.
        beginWebViewStartup();
        Window window = getWindow();
        // Use modern surface colors instead of harsh white/black
        int startupChrome = nightMode ? 0xFF0A0D12 : 0xFFFAFBFC;
        window.setStatusBarColor(startupChrome);
        window.setNavigationBarColor(startupChrome);
        int layoutFlags = View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN | View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION |
                View.SYSTEM_UI_FLAG_LAYOUT_STABLE;
        window.getDecorView().setSystemUiVisibility(layoutFlags | (nightMode ? 0 :
                (View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR | View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR)));
        window.setSoftInputMode(WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE);
        if (Build.VERSION.SDK_INT >= 30) window.setDecorFitsSystemWindows(false);
        if (Build.VERSION.SDK_INT >= 28) {
            WindowManager.LayoutParams attributes = window.getAttributes();
            // DEFAULT letterboxes a fullscreen window around the camera cutout on some
            // devices. Showing/hiding the status bar would then still resize the page.
            attributes.layoutInDisplayCutoutMode = WindowManager.LayoutParams.LAYOUT_IN_DISPLAY_CUTOUT_MODE_SHORT_EDGES;
            window.setAttributes(attributes);
        }

        deviceProfile = DeviceProfile.detect(this);
        migrateLegacyLogoExample();
        homeImages = new HomeImageStore(this);
        favicons = new FaviconStore(this);
        searchEngines = new SearchEngineStore(prefs);
        adBlockEnabled = prefs.getBoolean("adblock", true);
        startupCustomRulesReady = !adBlockEnabled;
        startupReadiness.set(StartupReadiness.FILTERS, startupCustomRulesReady);
        desktopMode = prefs.getBoolean("desktop", false);
        edgeNavigationEnabled = prefs.getBoolean("edge_navigation", true);
        httpsOnly = prefs.getBoolean("https_only", true);
        restoreTabs = HomeOpenPolicy.restoresLast(prefs.getString("home_open_mode", ""),
                prefs.getBoolean("restore_tabs", false));
        acceptThirdPartyCookies = prefs.getBoolean("accept_third_party_cookies", false);
        searchEngine = prefs.getString("search_engine", "google");
        if (!searchEngines.contains(searchEngine)) searchEngine = "google";
        performanceMode = prefs.getString("performance_mode", MODE_STANDARD);
        autoPictureInPicture = prefs.getBoolean("auto_picture_in_picture", false);
        immersiveScrollChrome = prefs.getBoolean("immersive_scroll_chrome", true);
        clearDataOnExit = prefs.getBoolean("clear_data_on_exit", false);
        cleanTrackingParameters = prefs.getBoolean("clean_tracking_parameters", true);
        passwordAutofillEnabled = prefs.getBoolean("password_autofill", true);
        passwordSavePromptsEnabled = prefs.getBoolean("password_save_prompts", true);
        if (!MODE_PERFORMANCE.equals(performanceMode) && !MODE_POWER_SAVE.equals(performanceMode)) performanceMode = MODE_STANDARD;
        siteExceptions = new HashSet<String>(prefs.getStringSet("site_exceptions", new HashSet<String>()));
        services = new BrowserServices(this);
        startupExecutor = BackgroundExecutor.create(2, 8, "median-startup", false);
        navigationExecutor = BackgroundExecutor.create(1, 2, "median-navigation", true);
        scriptExecutor = BackgroundExecutor.create(1, 64, "median-work", false);
        scriptNetworkExecutor = BackgroundExecutor.create(3, 96, "median-network", false);
        connectionHints = new NavigationConnectionHints(uiHandler, prefs, adBlock,
                new NavigationConnectionHints.Host() {
                    @Override public boolean isCurrentPageCallback(WebView source, long sequence) {
                        return !exitDataCleared && MainActivity.this.isCurrentPageCallback(source, sequence);
                    }
                    @Override public boolean isAdBlockEnabled() { return adBlockEnabled; }
                });
        adBlockRuleLoader = new AdBlockRuleLoader(adBlock, prefs, services, uiHandler,
                new AdBlockRuleLoader.TaskQueue() {
                    @Override public boolean execute(Runnable task) { return executeTask(scriptExecutor, task); }
                }, new AdBlockRuleLoader.Listener() {
                    @Override public void onPublished(boolean notifyUser) { onAdBlockRulesLoaded(notifyUser); }
                    @Override public void onFailed() { onAdBlockRulesLoadFailed(); }
                });
        // Publish the small custom-rule snapshot first, then compile cached subscriptions in
        // the same background task. Neither operation waits for onPageFinished or uses the UI.
        rebuildAdBlockRulesAsync(false);

        BrowserTab first = new BrowserTab();
        tabs.add(first);
        // Start both disk decoders before constructing the view hierarchy and WebView. Previously
        // the synchronous Chromium startup completed first, so the advertised parallel path was
        // actually serialized on every cold launch.
        beginStartupLoad(state, getIntent());
        buildUi();
        registerPredictiveBack();
    }

    /**
     * Uses the provider's supported async protocol when available. The callback is always posted
     * to the main looper, so onCreate finishes building the native surface before it is delivered.
     */
    private void beginWebViewStartup() {
        webViewStartupExecutor = BackgroundExecutor.createStartup(1, 32, "median-webview-startup");
        WebViewStartupCompat.startUpWebView(webViewStartupExecutor, new WebViewStartupCompat.Callback() {
            @Override public void onSuccess(WebViewStartupCompat.Result result) {
                finishWebViewStartupExecutor();
                if (activityDestroyed || isFinishing()) return;
                webViewStartupDiagnostic = result.usedAsyncStartup() ? "Init asynchrone" : "Init compatible";
                if (result.getTotalTimeInUiThreadMillis() != null)
                    webViewStartupDiagnostic += " · UI " + result.getTotalTimeInUiThreadMillis() + " ms";
                if (result.getMaxTimePerTaskInUiThreadMillis() != null)
                    webViewStartupDiagnostic += " · Tâche max " + result.getMaxTimePerTaskInUiThreadMillis() + " ms";
                postAfterUiTransition(new Runnable() {
                    @Override public void run() { initializeInitialWebView(); }
                });
            }

            @Override
            public void onFailure(Throwable error) {
                finishWebViewStartupExecutor();
                if (activityDestroyed || isFinishing()) return;
                // A real provider startup failure makes further WebView API calls unsafe.
                // Keep the native surface visible rather than retrying new WebView here.
                if (startupStatus != null) startupStatus.setText("Échec du moteur web, veuillez redémarrer Median");
            }
        });
    }

    private void finishWebViewStartupExecutor() {
        if (webViewStartupExecutor != null) webViewStartupExecutor.shutdown();
        webViewStartupExecutor = null;
    }

    /** Constructs the view only after provider preparation, or on the older-provider fallback. */
    private void initializeInitialWebView() {
        if (activityDestroyed || isFinishing() || webView != null || webContainer == null) return;

        webView = createConfiguredWebView();
        // Keep the startup surface until view construction has actually succeeded.
        if (startupSurface != null && startupSurface.getParent() == webContainer) {
            Motion.fadeOutStartup(startupSurface, reduceMotion(), new Runnable() {
                @Override public void run() {
                    if (startupSurface != null && startupSurface.getParent() == webContainer) {
                        webContainer.removeView(startupSurface);
                        startupSurface = null;
                    }
                }
            });
        } else {
            webContainer.removeAllViews();
        }

        final WebView initialView = webView;
        // Keep the startup surface above the newly created view until its short fade completes.
        webContainer.addView(initialView, 0, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        // WebView already renders through the provider's hardware pipeline. A temporary forced
        // layer duplicates its backing surface and delays the first useful frame on cold startup,
        // so let the view draw immediately while the startup surface fades away.
        initialView.setAlpha(1f);

        // configureWebView() runs before this field is assigned, so its generic renderer policy
        // cannot yet know that this is the visible tab. Promote it immediately after binding;
        // otherwise the first homepage/network navigation may run at background priority.
        applyPerformanceMode(webView);
        BrowserTab first = tabs.get(0);
        bindWebViewToTab(first, webView);
        first.lastActiveAt = SystemClock.uptimeMillis();
        if (activityResumed) webView.onResume();
        // Do not start a placeholder navigation here. maybeStartFastStartup() owns the first
        // useful navigation and can run before the background stores have finished decoding.
        startupReadiness.set(StartupReadiness.VIEW, true);
        updateChrome();
        maybeStartFastStartup();
        maybeCompleteStartup();
    }

    /** Starts the first useful page as soon as the native view and Activity are resumed. */
    private void maybeStartFastStartup() {
        if (startupReady || startupFastStarted || startupFastPosted || webView == null || !activityResumed ||
                !startupCustomRulesReady)
            return;
        startupFastPosted = true;
        final Runnable launch = new Runnable() {
            @Override public void run() {
                if (activityDestroyed || isFinishing() || webView == null || !activityResumed) {
                    startupFastPosted = false;
                    return;
                }
                startupFastPosted = false;
                startupFastStarted = true;
                Bundle savedState = startupSavedState;
                String externalUrl = startupExternalUrl;
                startupSavedState = null;
                startupExternalUrl = "";
                completeStartup(savedState, externalUrl);
            }
        };
        // An attached WebView is ready to accept the first navigation now. A second queue hop
        // adds main-thread latency without warming Chromium or improving renderer readiness.
        // Keep the attach-aware frame fallback for OEMs that resume before the first attach.
        if (webView.isAttachedToWindow()) launch.run();
        else postAfterUiTransition(launch);
    }

    /** Decodes larger user state away from the first-frame path. */
    private void beginStartupLoad(final Bundle savedState, Intent intent) {
        final String externalUrl = isExternalHttpIntent(intent) ? intent.getData().toString() : "";
        if (externalUrl.length() > 0) WebViewNavigationWarmupCompat.enqueueForStartup(externalUrl);
        startupSavedState = savedState;
        startupExternalUrl = externalUrl;
        startupDataLoader = new StartupDataLoader(getApplicationContext(), prefs, uiHandler,
                new StartupDataLoader.TaskQueue() {
                    @Override public boolean execute(Runnable task) { return executeTask(startupExecutor, task); }
                }, new StartupDataLoader.Listener() {
                    @Override public void onConnectionHintsReady(ConnectionHintsStore hints) {
                        if (activityDestroyed || exitDataCleared || !connectionHints.publishRestored(hints)) return;
                        if (webView != null && !pageFinished && isNetworkPage(currentPageUrl)) {
                            prepareNavigationConnections(currentPageUrl);
                            installConnectionHintScript(webView, currentPageUrl, true);
                        }
                    }

                    @Override public boolean onLoaded(StartupDataLoader.Result load) {
                        if (activityDestroyed || isFinishing()) return false;
                        dataStore = load.data;
                        bookmarkFolders = load.folders;
                        siteSettingsStore = load.sites;
                        scriptStore = load.scripts;
                        connectionHints.publishRestored(load.connectionHints);
                        startupScriptToken = load.scriptToken;
                        startupScriptPayloads = load.scriptPayloads;
                        startupDataReady = true;
                        startupReadiness.set(StartupReadiness.DATA, true);
                        onStartupDataReady();
                        maybeCompleteStartup();
                        return true;
                    }

                    @Override
                    public void onFailed() {
                        if (activityDestroyed || isFinishing()) return;
                        toast("Impossible de lire les données locales, redémarrez Median");
                        finishAfterTransition();
                    }

                    @Override
                    public void onWorkersFinished() {
                        if (startupExecutor != null) startupExecutor.shutdown();
                    }
                });
        startupDataLoader.start();
    }

    private void maybeCompleteStartup() {
        if (startupReady || startupFastPosted || startupFastStarted || webView == null ||
                !startupReadiness.claimPost()) return;
        postAfterUiTransition(new Runnable() {
            @Override
            public void run() {
                if (!startupReadiness.begin() || activityDestroyed || isFinishing() || webView == null) return;
                Bundle savedState = startupSavedState;
                String externalUrl = startupExternalUrl;
                startupSavedState = null;
                startupExternalUrl = "";
                completeStartup(savedState, externalUrl);
            }
        });
    }

    private void completeStartup(Bundle savedState, String externalUrl) {
        startupReady = true;
        startupReadyAt = SystemClock.elapsedRealtime();
        if (startupDataReady) installPreparedDocumentStartUserScripts(webView);
        boolean restoredTabs = restoreTabMetadata(savedState);
        BrowserTab active = tabs.get(currentTabIndex);
        Bundle webViewState = savedState == null ? null :
                (savedState.containsKey(STATE_WEBVIEW) ? savedState.getBundle(STATE_WEBVIEW) :
                        savedState.containsKey(STATE_TABS) ? null : savedState);
        String directInput = StartupNavigationPolicy.preferredInput(pendingStartupInput, externalUrl);
        pendingStartupInput = null;
        if (directInput.length() > 0) {
            // Typed input is newer than an external launch intent. Loading the homepage/session
            // first and this destination immediately afterwards recreates the cold-start race
            // fixed above, so execute only the selected direct navigation.
            startupSessionPending = false;
            loadInput(directInput);
        } else if (restoreWebViewState(webView, webViewState)) {
            startupSessionPending = false;
            active.url = webView.getUrl() == null ? HOME_URL : webView.getUrl();
            if (isHomeUrl(active.url)) {
                // A restored WebView can contain the placeholder homepage rendered before the
                // bookmark stores finished loading. Always rebuild internal home pages from the
                // now-ready stores so long-idle/process-death restores cannot show stale/empty data.
                renderedHomeKeys.remove(webView);
                showHome();
            } else if (isQrScannerUrl(active