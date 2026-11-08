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
            "Mises à jour du projet, versions et retours de bugs :\n" + GITHUB_URL +
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
    private String webViewStartupDiagnostic = "Initialisation de compatibilité";
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
                webViewStartupDiagnostic = result.usedAsyncStartup() ? "Initialisation asynchrone" : "Initialisation de compatibilité";
                if (result.getTotalTimeInUiThreadMillis() != null)
                    webViewStartupDiagnostic += " · UI " + result.getTotalTimeInUiThreadMillis() + " ms";
                if (result.getMaxTimePerTaskInUiThreadMillis() != null)
                    webViewStartupDiagnostic += " · tâche la plus longue " + result.getMaxTimePerTaskInUiThreadMillis() + " ms";
                postAfterUiTransition(new Runnable() {
                    @Override public void run() { initializeInitialWebView(); }
                });
            }

            @Override public void onFailure(Throwable error) {
                finishWebViewStartupExecutor();
                if (activityDestroyed || isFinishing()) return;
                // A real provider startup failure makes further WebView API calls unsafe.
                // Keep the native surface visible rather than retrying new WebView here.
                if (startupStatus != null) startupStatus.setText("Échec du démarrage du moteur de rendu web, veuillez fermer puis rouvrir Median");
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

                    @Override public void onFailed() {
                        if (activityDestroyed || isFinishing()) return;
                        toast("Impossible de lire les données locales de navigation, veuillez redémarrer Median");
                        finishAfterTransition();
                    }

                    @Override public void onWorkersFinished() {
                        if (startupExecutor != null) startupExecutor.shutdown();
                    }
                });
        startupDataLoader.start();
    }

    private void maybeCompleteStartup() {
        if (startupReady || startupFastPosted || startupFastStarted || webView == null ||
                !startupReadiness.claimPost()) return;
        postAfterUiTransition(new Runnable() {
            @Override public void run() {
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
            } else if (isQrScannerUrl(active.url)) {
                showQrScannerPage();
            } else if (isNetworkPage(active.url)) {
                currentPageUrl = active.url;
                currentPageHost = hostOf(active.url);
                prepareNetworkDestination(webView, active.url, currentPageHost);
                watchInitialNetworkNavigation(webView, active.url);
            } else if (isOfflineUrl(active.url)) {
                currentPageUrl = active.url;
                currentPageHost = "";
                prepareOfflineDestination(webView, active.url);
            } else {
                currentPageUrl = active.url;
                currentPageHost = "";
                applyPageAccessPolicy(webView, active.url);
                appliedSiteSettings.remove(webView);
            }
        } else if (restoredTabs) {
            // Activity recreation is independent of the fresh-launch homepage preference.
            // Metadata also retains the selected URL if Chromium could not save its history.
            startupSessionPending = false;
            if (isHomeUrl(active.url)) showHome();
            else if (isQrScannerUrl(active.url)) showQrScannerPage();
            else loadNetworkUrl(webView, active.url);
        } else {
            startupSessionPending = restoreTabs && dataStore == null;
            if (!restoreStartupSession()) {
                active.url = configuredHomeUrl();
                if (isHomeUrl(active.url)) showHome();
                else loadNetworkUrl(webView, active.url);
            }
        }
        requestChromeUpdate();
        showCommunityNoticeOnFirstLaunch(savedState);
    }

    private boolean restoreStartupSession() {
        if (!restoreTabs || dataStore == null || webView == null) return false;
        List<BrowserDataStore.SessionTab> saved = dataStore.restoreSession();
        if (saved.isEmpty()) return false;
        tabs.clear();
        for (BrowserDataStore.SessionTab item : saved) {
            BrowserTab restored = new BrowserTab();
            restored.title = item.title;
            restored.url = item.url;
            restored.pinned = item.pinned;
            tabs.add(restored);
        }
        currentTabIndex = Math.min(dataStore.restoredSessionIndex(), tabs.size() - 1);
        BrowserTab active = tabs.get(currentTabIndex);
        bindWebViewToTab(active, webView);
        active.lastActiveAt = SystemClock.uptimeMillis();
        if (isHomeUrl(active.url)) showHome();
        else loadNetworkUrl(webView, active.url);
        return true;
    }

    /** Publishes decoded stores after first paint without replacing an active user navigation. */
    private void onStartupDataReady() {
        if (activityDestroyed || webView == null) return;
        installPreparedDocumentStartUserScripts(webView);
        if (startupSessionPending && isHomeUrl(currentPageUrl) && isHomeUrl(webView.getUrl())) {
            startupSessionPending = false;
            if (restoreStartupSession()) {
                requestChromeUpdate();
                return;
            }
        }
        // The cache key includes every persisted site setting. Publishing the stores does not
        // invalidate an identical default policy; avoid resending settings during the first load.
        // A real site override changes the key and is still applied below.
        // Only apply settings or show home if the current page matches what WebView is actually showing
        // AND the user hasn't navigated away from the initial state
        String actualUrl = webView.getUrl();
        if (!pageFinished && isNetworkPage(currentPageUrl)) prepareNavigationConnections(currentPageUrl);
        if (isNetworkPage(currentPageUrl) && isNetworkPage(actualUrl)) {
            applySiteSettings(webView, currentPageHost);
        } else if (!userHasNavigated && isHomeUrl(currentPageUrl) && isHomeUrl(actualUrl)) {
            showHome();
        }
    }

    /** Network refresh yields to page completion; local filtering is already initialized. */
    private void scheduleDeferredStartupWork() {
        if (!startupReady) return;
        if (deferredStartupComplete || deferredStartupPending) return;
        deferredStartupPending = true;
        uiHandler.postDelayed(deferredStartup, FILTER_SUBSCRIPTION_IDLE_DELAY_MS);
    }

    private boolean executeTask(ExecutorService executor, Runnable task) {
        if (executor == null || executor.isShutdown() || task == null) return false;
        try {
            executor.execute(task);
            return true;
        } catch (RejectedExecutionException ignored) {
            long now = SystemClock.uptimeMillis();
            if (!activityDestroyed && now - lastExecutorBusyToastAt > 2500L) {
                lastExecutorBusyToastAt = now;
                uiHandler.post(new Runnable() {
                    @Override public void run() { if (!activityDestroyed) toast("Tâches d'arrière-plan occupées, veuillez réessayer plus tard"); }
                });
            }
            return false;
        }
    }

    private boolean requireStartupReady() {
        if (startupReady) return true;
        long now = SystemClock.uptimeMillis();
        if (now - lastExecutorBusyToastAt > 1200L) {
            lastExecutorBusyToastAt = now;
            toast("Restauration des données locales de navigation…");
        }
        return false;
    }

    private String homeToken() {
        if (homeToken == null) homeToken = UrlCleaner.randomToken();
        return homeToken;
    }

    private String adPickToken() {
        if (adPickToken == null) adPickToken = UrlCleaner.randomToken();
        return adPickToken;
    }

    private String qrToken() {
        if (qrToken == null) qrToken = UrlCleaner.randomToken();
        return qrToken;
    }

    /**
     * 2.1.5 wrote its editor example into real preferences before the user
     * pressed Save. Repair only the exact inconsistent legacy state once.
     */
    private void migrateLegacyLogoExample() {
        final String migrationKey = "home_logo_example_migrated_v216";
        if (prefs.getBoolean(migrationKey, false)) return;
        String code = LogoMarkup.clean(prefs.getString("home_logo_code", ""));
        String title = HomePageConfig.cleanTitle(prefs.getString("home_title", HomePageConfig.DEFAULT_TITLE));
        SharedPreferences.Editor editor = prefs.edit().putBoolean(migrationKey, true);
        if (LogoMarkup.LEGACY_GRADIENT_EXAMPLE.equals(code) && HomePageConfig.DEFAULT_TITLE.equals(title)) {
            editor.remove("home_logo_code");
            if ("custom".equals(prefs.getString("home_logo_style", "median")))
                editor.putString("home_logo_style", "median");
        }
        editor.apply();
    }

    private void buildUi() {
        rootFrame = new FrameLayout(this);
        rootFrame.setBackgroundColor(nightMode ? DARK_WEB : WHITE);
        int chromeBackground = nightMode ? DARK_BACKGROUND : WHITE;
        int chromeSurface = nightMode ? DARK_SURFACE : SURFACE;
        int chromeText = nightMode ? DARK_TEXT : TEXT;
        int chromeHint = nightMode ? DARK_MUTED : 0xff80868b;

        browserChrome = new FrameLayout(this);
        browserChrome.setBackgroundColor(chromeBackground);
        rootFrame.addView(browserChrome, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

        topBar = new LinearLayout(this);
        topBar.setOrientation(LinearLayout.HORIZONTAL);
        topBar.setGravity(Gravity.CENTER_VERTICAL);
        topBar.setPadding(dp(12), dp(8), dp(12), dp(8));
        topBar.setBackgroundColor(chromeBackground);

        addressPill = new LinearLayout(this);
        addressPill.setOrientation(LinearLayout.HORIZONTAL);
        addressPill.setGravity(Gravity.CENTER_VERTICAL);
        addressPill.setPadding(dp(4), 0, dp(4), 0);
        addressPill.setBackground(roundRect(chromeSurface, 999));
        addressPill.setElevation(0.5f * getResources().getDisplayMetrics().density);

        shieldButton = iconButton(BrowserIconView.SHIELD, "Protection et scripts");
        addressPill.addView(shieldButton, new LinearLayout.LayoutParams(dp(42), dp(42)));

        addressBar = new EditText(this);
        addressBar.setSingleLine(true);
        addressBar.setTextSize(15.5f);
        addressBar.setTextColor(chromeText);
        addressBar.setHintTextColor(chromeHint);
        addressBar.setHint("Rechercher ou saisir une adresse");
        addressBar.setSelectAllOnFocus(true);
        addressBar.setImeOptions(EditorInfo.IME_ACTION_GO);
        addressBar.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_URI);
        addressBar.setBackgroundColor(Color.TRANSPARENT);
        addressBar.setPadding(dp(8), 0, dp(8), 0);
        addressPill.addView(addressBar, new LinearLayout.LayoutParams(0, dp(46), 1f));

        refreshButton = iconButton(BrowserIconView.RELOAD, "Actualiser");
        addressPill.addView(refreshButton, new LinearLayout.LayoutParams(dp(42), dp(42)));
        topBar.addView(addressPill, new LinearLayout.LayoutParams(0, dp(46), 1f));

        topBar.setElevation(dp(8));
        browserChrome.addView(topBar, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(62), Gravity.TOP));

        progressBar = new ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal);
        progressBar.setMax(100);
        progressBar.setProgressTintList(android.content.res.ColorStateList.valueOf(BLUE));
        progressBar.setVisibility(View.GONE);
        progressBar.setElevation(dp(9));
        FrameLayout.LayoutParams progressParams = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(2), Gravity.TOP);
        progressParams.topMargin = dp(62);
        browserChrome.addView(progressBar, progressParams);

        webContainer = new FrameLayout(this);
        webContainer.setBackgroundColor(nightMode ? DARK_WEB : WHITE);
        startupSurface = new LinearLayout(this);
        ((LinearLayout) startupSurface).setOrientation(LinearLayout.VERTICAL);
        ((LinearLayout) startupSurface).setGravity(Gravity.CENTER);
        startupSurface.setPadding(dp(24), dp(24), dp(24), dp(24));
        startupSurface.setBackgroundColor(nightMode ? DARK_WEB : WHITE);
        ImageView startupMark = new ImageView(this);
        startupMark.setImageResource(R.drawable.ic_launcher_foreground);
        startupMark.setContentDescription("Median");
        startupMark.setScaleType(ImageView.ScaleType.CENTER_INSIDE);
        ((LinearLayout) startupSurface).addView(startupMark, new LinearLayout.LayoutParams(dp(88), dp(88)));
        TextView startupName = new TextView(this);
        startupName.setText("median");
        startupName.setTextColor(chromeText);
        startupName.setTextSize(23f);
        startupName.setGravity(Gravity.CENTER);
        startupName.setLetterSpacing(0.08f);
        ((LinearLayout) startupSurface).addView(startupName, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT));
        startupStatus = new TextView(this);
        startupStatus.setText("Préparation du moteur de rendu web…");
        startupStatus.setTextColor(nightMode ? DARK_MUTED : MUTED);
        startupStatus.setTextSize(12f);
        startupStatus.setGravity(Gravity.CENTER);
        startupStatus.setPadding(0, dp(8), 0, 0);
        ((LinearLayout) startupSurface).addView(startupStatus, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT));
        webContainer.addView(startupSurface, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

        // Apply smooth fade-in animation to startup screen
        Motion.fadeInStartup(startupSurface, reduceMotion(), null);

        FrameLayout.LayoutParams pageParams = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.MATCH_PARENT);
        pageParams.topMargin = dp(62);
        pageParams.bottomMargin = dp(62);
        browserChrome.addView(webContainer, 0, pageParams);

        bottomBar = new LinearLayout(this);
        bottomBar.setOrientation(LinearLayout.HORIZONTAL);
        bottomBar.setGravity(Gravity.CENTER);
        bottomBar.setPadding(dp(10), dp(4), dp(10), dp(4));
        bottomBar.setBackgroundColor(chromeBackground);
        bottomBar.setElevation(dp(8));

        backButton = iconButton(BrowserIconView.BACK, "Retour");
        forwardButton = iconButton(BrowserIconView.FORWARD, "Suivant");
        BrowserIconView home = iconButton(BrowserIconView.HOME, "Accueil");
        tabButton = iconButton(BrowserIconView.TABS, "Onglets");
        BrowserIconView menu = iconButton(BrowserIconView.MENU, "Menu");
        BrowserIconView[] bottomButtons = new BrowserIconView[] { backButton, forwardButton, home, tabButton, menu };
        for (BrowserIconView button : bottomButtons) bottomBar.addView(button, new LinearLayout.LayoutParams(0, dp(54), 1f));
        browserChrome.addView(bottomBar, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(62), Gravity.BOTTOM));

        statusBarBackground = new View(this);
        navigationBarBackground = new View(this);
        statusBarBackground.setBackgroundColor(chromeBackground);
        navigationBarBackground.setBackgroundColor(chromeBackground);
        statusBarBackground.setElevation(dp(8));
        navigationBarBackground.setElevation(dp(8));
        browserChrome.addView(statusBarBackground, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, Gravity.TOP));
        browserChrome.addView(navigationBarBackground, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, Gravity.BOTTOM));

        setContentView(rootFrame);
        installSystemBarInsets(rootFrame);

        addressBar.setOnEditorActionListener(new TextView.OnEditorActionListener() {
            @Override public boolean onEditorAction(TextView v, int actionId, KeyEvent event) {
                if (actionId == EditorInfo.IME_ACTION_GO || actionId == EditorInfo.IME_ACTION_SEARCH ||
                        (event != null && event.getKeyCode() == KeyEvent.KEYCODE_ENTER)) {
                    loadInput(addressBar.getText().toString());
                    hideKeyboard();
                    addressBar.clearFocus();
                    return true;
                }
                return false;
            }
        });
        addressBar.setOnFocusChangeListener(new View.OnFocusChangeListener() {
            @Override public void onFocusChange(View v, boolean hasFocus) {
                if (hasFocus) showBrowserChrome(false);
                Motion.focusPill(addressPill, hasFocus, reduceMotion());
                if (hasFocus) {
                    String url = currentPageUrl;
                    if (isInternalBrowserUrl(url) || "about:blank".equalsIgnoreCase(url)) addressBar.setText("");
                    else if (url != null && !url.contentEquals(addressBar.getText())) addressBar.setText(url);
                    addressBar.selectAll();
                } else {
                    updateAddressBar();
                }
            }
        });
        refreshButton.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) {
                if (webView == null) return;
                if (isHomeUrl(currentPageUrl)) {
                    renderedHomeKeys.remove(webView);
                    showHome();
                } else if (isQrScannerUrl(currentPageUrl)) showQrScannerPage();
                else reloadWebView(webView);
            }
        });
        refreshButton.setOnLongClickListener(new View.OnLongClickListener() {
            @Override public boolean onLongClick(View v) {
                if (webView == null) return true;
                webView.stopLoading();
                toast("Chargement arrêté");
                return true;
            }
        });
        shieldButton.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { showProtectionPanel(); }
        });
        backButton.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) {
                if (webView != null && webView.canGoBack()) {
                    goBackWebView(webView);
                    scheduleRestoredHomeRepair(webView);
                }
            }
        });
        forwardButton.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) {
                if (webView != null && webView.canGoForward()) goForwardWebView(webView);
            }
        });
        home.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { openConfiguredHome(); }
        });
        home.setOnLongClickListener(new View.OnLongClickListener() {
            @Override public boolean onLongClick(View v) { newTab(); return true; }
        });
        tabButton.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { showTabs(); }
        });
        tabButton.setOnLongClickListener(new View.OnLongClickListener() {
            @Override public boolean onLongClick(View v) { newTab(); return true; }
        });
        menu.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { showMainMenu(); }
        });
        applyChromeTheme();
    }


    private void installSystemBarInsets(final View target) {
        if (target == null) return;
        target.setOnApplyWindowInsetsListener(new View.OnApplyWindowInsetsListener() {
            @Override public android.view.WindowInsets onApplyWindowInsets(View view, android.view.WindowInsets insets) {
                int imeBottom;
                boolean imeVisible;
                if (Build.VERSION.SDK_INT >= 30) {
                    android.graphics.Insets bars = insets.getInsetsIgnoringVisibility(
                            android.view.WindowInsets.Type.systemBars() | android.view.WindowInsets.Type.displayCutout());
                    systemInsetLeft = bars.left;
                    systemInsetTop = bars.top;
                    systemInsetRight = bars.right;
                    systemInsetBottom = bars.bottom;
                    imeBottom = insets.getInsets(android.view.WindowInsets.Type.ime()).bottom;
                    imeVisible = insets.isVisible(android.view.WindowInsets.Type.ime());
                } else {
                    systemInsetLeft = insets.getStableInsetLeft();
                    systemInsetTop = insets.getStableInsetTop();
                    systemInsetRight = insets.getStableInsetRight();
                    systemInsetBottom = insets.getStableInsetBottom();
                    if (Build.VERSION.SDK_INT >= 28 && insets.getDisplayCutout() != null) {
                        android.view.DisplayCutout cutout = insets.getDisplayCutout();
                        systemInsetLeft = Math.max(systemInsetLeft, cutout.getSafeInsetLeft());
                        systemInsetTop = Math.max(systemInsetTop, cutout.getSafeInsetTop());
                        systemInsetRight = Math.max(systemInsetRight, cutout.getSafeInsetRight());
                        systemInsetBottom = Math.max(systemInsetBottom, cutout.getSafeInsetBottom());
                    }
                    // On these releases adjustResize already removes the keyboard area from
                    // the window. Do not subtract its height a second time as root padding.
                    imeVisible = insets.getSystemWindowInsetBottom() > systemInsetBottom + dp(100);
                    imeBottom = 0;
                }
                systemKeyboardBottom = imeBottom;
                systemKeyboardVisible = imeVisible;
                applyPageInsets();
                return Build.VERSION.SDK_INT >= 30 ? insets : insets.consumeSystemWindowInsets();
            }
        });
        if (Build.VERSION.SDK_INT < 30) {
            target.getViewTreeObserver().addOnGlobalLayoutListener(new android.view.ViewTreeObserver.OnGlobalLayoutListener() {
                private final android.graphics.Rect visibleFrame = new android.graphics.Rect();
                private final int[] location = new int[2];
                @Override public void onGlobalLayout() {
                    if (activityDestroyed) return;
                    target.getWindowVisibleDisplayFrame(visibleFrame);
                    target.getLocationOnScreen(location);
                    int overlap = Math.max(0, location[1] + target.getHeight() - visibleFrame.bottom);
                    // FULLSCREEN makes adjustResize ineffective on Android 8-10. Subtract
                    // only the keyboard portion still covering this window, not one already
                    // removed by the system. Status/nav changes never cross this threshold.
                    int next = overlap > dp(100) ? overlap : 0;
                    if (next == legacyKeyboardOverlap) return;
                    legacyKeyboardOverlap = next;
                    applyPageInsets();
                }
            });
        }
        target.requestApplyInsets();
    }

    private void applyPageInsets() {
        if (rootFrame == null) return;
        boolean fullSurface = immersivePageLayout || customView != null || isInPictureInPictureMode();
        keyboardVisible = systemKeyboardVisible || legacyKeyboardOverlap > 0;
        int imeBottom = Math.max(systemKeyboardBottom, legacyKeyboardOverlap);
        int top = fullSurface ? 0 : systemInsetTop;
        int bottom = fullSurface || keyboardVisible ? imeBottom : systemInsetBottom;
        if (rootFrame.getPaddingLeft() != systemInsetLeft || rootFrame.getPaddingTop() != top ||
                rootFrame.getPaddingRight() != systemInsetRight || rootFrame.getPaddingBottom() != bottom) {
            rootFrame.setPadding(systemInsetLeft, top, systemInsetRight, bottom);
        }
        updateChromeInsets();
    }

    private void updateChromeInsets() {
        if (topBar == null || bottomBar == null) return;
        int top = immersivePageLayout ? systemInsetTop : 0;
        int bottom = immersivePageLayout && !keyboardVisible ? systemInsetBottom : 0;
        FrameLayout.LayoutParams topParams = (FrameLayout.LayoutParams) topBar.getLayoutParams();
        FrameLayout.LayoutParams bottomParams = (FrameLayout.LayoutParams) bottomBar.getLayoutParams();
        FrameLayout.LayoutParams progressParams = (FrameLayout.LayoutParams) progressBar.getLayoutParams();
        if (topParams.topMargin != top) {
            topParams.topMargin = top;
            topBar.setLayoutParams(topParams);
        }
        if (bottomParams.bottomMargin != bottom) {
            bottomParams.bottomMargin = bottom;
            bottomBar.setLayoutParams(bottomParams);
        }
        if (progressParams.topMargin != top + dp(62)) {
            progressParams.topMargin = top + dp(62);
            progressBar.setLayoutParams(progressParams);
        }
        updateSystemBarBackgrounds();
        updatePageMargins();
    }

    private void updateSystemBarBackgrounds() {
        if (statusBarBackground == null || navigationBarBackground == null) return;
        FrameLayout.LayoutParams status = (FrameLayout.LayoutParams) statusBarBackground.getLayoutParams();
        FrameLayout.LayoutParams navigation = (FrameLayout.LayoutParams) navigationBarBackground.getLayoutParams();
        if (status.height != systemInsetTop) {
            status.height = systemInsetTop;
            statusBarBackground.setLayoutParams(status);
        }
        int bottom = keyboardVisible ? 0 : systemInsetBottom;
        if (navigation.height != bottom) {
            navigation.height = bottom;
            navigationBarBackground.setLayoutParams(navigation);
        }
        int visible = immersivePageLayout && !chromeHiddenByScroll && !isInPictureInPictureMode() ?
                View.VISIBLE : View.INVISIBLE;
        statusBarBackground.setVisibility(visible);
        navigationBarBackground.setVisibility(visible);
    }

    private void updatePageMargins() {
        if (webContainer == null) return;
        // Changing the viewport while WebView is tracking a finger changes its scroll
        // geometry mid-gesture. Commit the new space after UP/CANCEL instead.
        if (immersiveGestureActive && immersivePageLayout && !keyboardVisible &&
                customView == null && !isInPictureInPictureMode()) return;
        boolean fullscreen = isInPictureInPictureMode() || (immersivePageLayout && chromeHiddenByScroll);
        int top = fullscreen ? 0 : dp(62) + (immersivePageLayout ? systemInsetTop : 0);
        int bottom = fullscreen ? 0 : dp(62) +
                (immersivePageLayout && !keyboardVisible ? systemInsetBottom : 0);
        FrameLayout.LayoutParams params = (FrameLayout.LayoutParams) webContainer.getLayoutParams();
        if (params.topMargin == top && params.bottomMargin == bottom) return;
        // Native space is required here: an overlay makes a page's first and last
        // controls unreachable at its scroll limits. Resize once per chrome state,
        // never on scroll callbacks or on every toolbar animation frame.
        params.topMargin = top;
        params.bottomMargin = bottom;
        webContainer.setLayoutParams(params);
    }

    private void updateImmersivePageLayout() {
        if (webContainer == null || rootFrame == null) return;
        boolean next = immersiveScrollChrome && isNetworkPage(currentPageUrl);
        if (next == immersivePageLayout) return;
        immersivePageLayout = next;
        immersiveGestureActive = false;
        updatePageMargins();
        updateChromeInsets();
        applyPageInsets();
        if (!next) showBrowserChrome(false);
        else setImmersiveSystemBars(chromeHiddenByScroll);
        rootFrame.requestApplyInsets();
    }

    /** Keeps the page edge-to-edge while the scroll chrome is hidden. */
    private void setImmersiveSystemBars(boolean hidden) {
        hidden = hidden || customView != null || isInPictureInPictureMode();
        Window window = getWindow();
        if (Build.VERSION.SDK_INT >= 30) {
            window.setStatusBarColor(Color.TRANSPARENT);
            window.setNavigationBarColor(Color.TRANSPARENT);
            android.view.WindowInsetsController controller = window.getInsetsController();
            if (controller != null) {
                int bars = android.view.WindowInsets.Type.statusBars() |
                        android.view.WindowInsets.Type.navigationBars();
                controller.setSystemBarsBehavior(
                        android.view.WindowInsetsController.BEHAVIOR_SHOW_TRANSIENT_BARS_BY_SWIPE);
                if (hidden) controller.hide(bars); else controller.show(bars);
            }
            return;
        }

        View decor = window.getDecorView();
        int flags = decor.getSystemUiVisibility();
        int immersiveFlags = View.SYSTEM_UI_FLAG_FULLSCREEN |
                View.SYSTEM_UI_FLAG_HIDE_NAVIGATION |
                View.SYSTEM_UI_FLAG_IMMERSIVE_STICKY |
                View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN |
                View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION |
                View.SYSTEM_UI_FLAG_LAYOUT_STABLE;
        flags &= ~immersiveFlags;
        // Root padding owns safe areas on every page. Keep these flags in ordinary mode
        // too, otherwise the system and root would both subtract the bar insets.
        flags |= View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN | View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION |
                View.SYSTEM_UI_FLAG_LAYOUT_STABLE;
        if (hidden) flags |= immersiveFlags;
        else {
            if (nightMode) {
                flags &= ~(View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR | View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR);
            } else {
                flags |= View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR | View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR;
            }
        }
        decor.setSystemUiVisibility(flags);
    }

    private BrowserIconView iconButton(int icon, String description) {
        BrowserIconView button = new BrowserIconView(this, icon);
        button.setContentDescription(description);
        // Platform selectable drawables retain the Activity's original theme. Drawing the
        // bounded pressed halo in BrowserIconView keeps theme switches deterministic and avoids
        // a drawable allocation for every toolbar icon.
        button.setBackground(null);
        return button;
    }

    private WebView createConfiguredWebView() {
        WebView view = new WebView(this);
        // The window already uses hardware acceleration. A permanent View layer adds
        // a full-viewport texture on top of Chromium's own compositor, including hot tabs.
        styleWebView(view);
        configureWebView(view);
        pageHosts.put(view, "");
        return view;
    }

    /** Observe actual finger direction; resize, fling and script scrolls are not gestures. */
    private void observeImmersiveTouch(WebView source, MotionEvent event) {
        if (source != webView || activityDestroyed || event == null) return;
        int action = event.getActionMasked();
        // A sheet, custom video view, or window transition may appear between DOWN and CANCEL.
        // Consume the terminal event for our bookkeeping before checking those transient modes.
        if (action == MotionEvent.ACTION_CANCEL || action == MotionEvent.ACTION_UP) {
            boolean wasActive = immersiveGestureActive;
            boolean startHidden = immersiveGestureStartHidden;
            float offset = immersiveGestureOffset;
            immersiveGestureActive = false;
            if (wasActive) {
                boolean eligible = immersivePageLayout && activeOverlay == null && customView == null &&
                        !isInPictureInPictureMode();
                if (action == MotionEvent.ACTION_UP && eligible) settleImmersiveChrome(offset >= .5f, true);
                else resetImmersiveChromeVisual(startHidden);
            }
            if (!immersivePageLayout || activeOverlay != null || customView != null ||
                    isInPictureInPictureMode()) return;
        }
        if (!immersivePageLayout || activeOverlay != null || customView != null ||
                isInPictureInPictureMode()) return;
        if (action == MotionEvent.ACTION_DOWN) {
            immersiveGestureActive = true;
            immersiveGestureDirectionLocked = false;
            immersiveGestureVertical = false;
            immersiveGestureDownX = event.getRawX();
            immersiveGestureDownY = event.getRawY();
            immersiveGestureY = event.getRawY();
            immersiveGestureStartHidden = chromeHiddenByScroll;
            immersiveGestureOffset = chromeOffsetFromViews(chromeHiddenByScroll);
            cancelChromeAnimationsForGesture();
            applyChromeGestureOffset(immersiveGestureOffset);
        } else if (event.getPointerCount() > 1 && immersiveGestureActive) {
            immersiveGestureActive = false;
            resetImmersiveChromeVisual(immersiveGestureStartHidden);
            updatePageMargins();
        } else if (action == MotionEvent.ACTION_MOVE && immersiveGestureActive) {
            float rawX = event.getRawX();
            float rawY = event.getRawY();
            float dx = rawX - immersiveGestureDownX;
            float dy = rawY - immersiveGestureDownY;
            float deltaY = rawY - immersiveGestureY;
            immersiveGestureY = rawY;
            if (!immersiveGestureDirectionLocked) {
                float slop = Math.max(dp(8), ViewConfiguration.get(source.getContext()).getScaledTouchSlop());
                if (Math.hypot(dx, dy) <= slop) return;
                immersiveGestureDirectionLocked = true;
                immersiveGestureVertical = Math.abs(dy) > Math.abs(dx) * 1.2f;
                if (!immersiveGestureVertical) {
                    immersiveGestureActive = false;
                    resetImmersiveChromeVisual(immersiveGestureStartHidden);
                    return;
                }
                // Consume only movement beyond slop when the direction first locks.
                deltaY = Math.signum(dy) * (Math.abs(dy) - slop);
            }
            if (immersiveGestureVertical) {
                float travel = Math.max(dp(62), Math.max(topBar.getHeight(), bottomBar.getHeight()));
                // Clamp each increment: overscroll must not create a dead zone on reversal.
                immersiveGestureOffset = clamp01(immersiveGestureOffset - deltaY / travel);
                applyChromeGestureOffset(immersiveGestureOffset);
            }
        }
    }

    private void hideBrowserChrome() {
        settleImmersiveChrome(true, false);
    }

    private void showBrowserChrome(boolean animate) {
        if (topBar == null || bottomBar == null || isInPictureInPictureMode()) return;
        if (animate && immersivePageLayout) {
            settleImmersiveChrome(false, true);
            return;
        }
        immersiveGestureActive = false;
        resetImmersiveChromeVisual(false);
        setImmersiveSystemBars(false);
    }

    private void settleImmersiveChrome(boolean hidden, boolean force) {
        if (!immersivePageLayout || topBar == null || bottomBar == null ||
                isInPictureInPictureMode() || (!force && hidden == chromeHiddenByScroll)) return;
        float offset = chromeOffsetFromViews(chromeHiddenByScroll);
        chromeHiddenByScroll = hidden;
        updatePageMargins();
        updateSystemBarBackgrounds();
        setImmersiveSystemBars(hidden);
        long duration = Math.max(60L, Math.round((reduceMotion() ? 80L : 180L) *
                Math.abs((hidden ? 1f : 0f) - offset)));
        cancelViewAnimationIfRunning(topBar);
        cancelViewAnimationIfRunning(bottomBar);
        cancelViewAnimationIfRunning(progressBar);
        applyChromeGestureOffset(offset);
        topBar.animate().translationY(hidden ? -topBar.getHeight() : 0f).alpha(hidden ? 0f : 1f).setDuration(duration)
                .withEndAction(new Runnable() {
                    @Override public void run() {
                        if (chromeHiddenByScroll) {
                            topBar.setVisibility(View.INVISIBLE);
                            topBar.setTranslationY(0f);
                            topBar.setAlpha(1f);
                        }
                    }
                }).start();
        bottomBar.animate().translationY(hidden ? bottomBar.getHeight() : 0f).alpha(hidden ? 0f : 1f).setDuration(duration)
                .withEndAction(new Runnable() {
                    @Override public void run() {
                        if (chromeHiddenByScroll) {
                            bottomBar.setVisibility(View.INVISIBLE);
                            bottomBar.setTranslationY(0f);
                            bottomBar.setAlpha(1f);
                        }
                    }
                }).start();
        if (progressBar != null) {
            syncChromeProgress(offset);
            if (!hidden && renderedProgress >= 0 && renderedProgress < 100) {
                progressBar.setProgress(renderedProgress);
                progressBar.setVisibility(View.VISIBLE);
                progressBar.animate().translationY(0f).alpha(1f).setDuration(duration).start();
            } else {
                progressBar.setVisibility(View.GONE);
            }
        }
    }

    private float chromeOffsetFromViews(boolean hidden) {
        if (topBar == null || bottomBar == null) return 0f;
        if (topBar.getVisibility() != View.VISIBLE && bottomBar.getVisibility() != View.VISIBLE)
            return hidden ? 1f : 0f;
        float topHeight = Math.max(1f, topBar.getHeight());
        float bottomHeight = Math.max(1f, bottomBar.getHeight());
        float topOffset = -topBar.getTranslationY() / topHeight;
        float bottomOffset = bottomBar.getTranslationY() / bottomHeight;
        return clamp01((topOffset + bottomOffset) * .5f);
    }

    private void cancelChromeAnimationsForGesture() {
        cancelViewAnimationIfRunning(topBar);
        cancelViewAnimationIfRunning(bottomBar);
        cancelViewAnimationIfRunning(progressBar);
        topBar.setVisibility(View.VISIBLE);
        bottomBar.setVisibility(View.VISIBLE);
    }

    /** Cancel only an active property animation and detach stale callbacks first. */
    private static void cancelViewAnimationIfRunning(View view) {
        if (view == null) return;
        ViewPropertyAnimator animator = view.animate();
        // ViewPropertyAnimator has no isRunning() API. Clearing callbacks before
        // cancel() makes this safe for both an active and an already-idle animator.
        animator.setListener(null).setUpdateListener(null).withEndAction(null).cancel();
    }

    private void applyChromeGestureOffset(float offset) {
        if (topBar == null || bottomBar == null) return;
        offset = clamp01(offset);
        topBar.setVisibility(View.VISIBLE);
        bottomBar.setVisibility(View.VISIBLE);
        topBar.setTranslationY(-topBar.getHeight() * offset);
        bottomBar.setTranslationY(bottomBar.getHeight() * offset);
        topBar.setAlpha(1f - offset);
        bottomBar.setAlpha(1f - offset);
        syncChromeProgress(offset);
    }

    private void syncChromeProgress(float offset) {
        if (progressBar == null) return;
        progressBar.setTranslationY(-topBar.getHeight() * offset);
        progressBar.setAlpha(1f - offset);
        boolean loading = renderedProgress >= 0 && renderedProgress < 100 &&
                !isInPictureInPictureMode() && customView == null;
        progressBar.setVisibility(loading && offset < 1f ? View.VISIBLE : View.GONE);
    }

    private void resetImmersiveChromeVisual(boolean hidden) {
        hidden = hidden && immersivePageLayout;
        chromeHiddenByScroll = hidden;
        cancelChromeAnimationsForGesture();
        applyChromeGestureOffset(hidden ? 1f : 0f);
        if (hidden || isInPictureInPictureMode() || customView != null) {
            topBar.setVisibility(View.INVISIBLE);
            bottomBar.setVisibility(View.INVISIBLE);
            topBar.setTranslationY(0f);
            bottomBar.setTranslationY(0f);
            topBar.setAlpha(1f);
            bottomBar.setAlpha(1f);
        }
        updatePageMargins();
        updateSystemBarBackgrounds();
    }

    private float clamp01(float value) {
        return Math.max(0f, Math.min(1f, value));
    }

    private void bindWebViewToTab(BrowserTab tab, WebView view) {
        if (tab == null || view == null) return;
        tab.liveView = view;
        scriptTabIds.put(view, scriptTabId(tab));
    }

    private String scriptTabId(BrowserTab tab) {
        if (tab.scriptTabId == null) tab.scriptTabId = "t" + Long.toString(++scriptTabSequence, 36);
        return tab.scriptTabId;
    }

    private void styleWebView(WebView view) {
        view.setBackgroundColor(nightMode ? DARK_WEB : WHITE);
        view.setFocusable(true);
        view.setFocusableInTouchMode(true);
        view.setClickable(true);
        view.setVerticalScrollBarEnabled(false);
        view.setHorizontalScrollBarEnabled(false);
        view.setOverScrollMode(View.OVER_SCROLL_IF_CONTENT_SCROLLS);
        view.setDrawingCacheEnabled(false);
        resetWebViewTransform(view);
    }

    /** WebView owns its input surface. Never animate or leave transforms on that surface. */
    private void resetWebViewTransform(WebView view) {
        if (view == null) return;
        cancelViewAnimationIfRunning(view);
        view.setAlpha(1f);
        view.setTranslationX(0f);
        view.setTranslationY(0f);
        view.setScaleX(1f);
        view.setScaleY(1f);
    }

    private WebView acquireWebView() {
        return createConfiguredWebView();
    }

    private int liveWebViewCount() {
        int count = 0;
        for (BrowserTab tab : tabs) if (tab.liveView != null) count++;
        return count;
    }

    private BrowserTab tabForView(WebView view) {
        if (view == null) return null;
        for (BrowserTab tab : tabs) if (tab.liveView == view) return tab;
        return null;
    }

    private String pageHostFor(WebView view) {
        if (view == webView) return currentPageHost;
        String value = pageHosts.get(view);
        return value == null ? "" : value;
    }

    private void updateTabForView(WebView view, String url, String title) {
        BrowserTab tab = tabForView(view);
        if (tab == null) return;
        if (url != null) tab.url = url;
        if (title != null && title.length() > 0) tab.title = title;
    }


    private interface SheetHandler {
        void onItem(int index);
    }

    private final class SettingsDialogReturn implements DialogInterface.OnClickListener, DialogInterface.OnCancelListener {
        private final Runnable action;
        SettingsDialogReturn(Runnable action) { this.action = action; }
        @Override public void onClick(DialogInterface dialog, int which) { continueSettingsPanel(action); }
        @Override public void onCancel(DialogInterface dialog) { continueSettingsPanel(action); }
    }

    private final class HomeOpenDialogReturn implements DialogInterface.OnClickListener, DialogInterface.OnCancelListener {
        private final boolean customization;
        HomeOpenDialogReturn(boolean customization) { this.customization = customization; }
        @Override public void onClick(DialogInterface dialog, int which) { continueHomeOpenSettings(customization); }
        @Override public void onCancel(DialogInterface dialog) { continueHomeOpenSettings(customization); }
    }

    /** Gives the handle and title strip a forgiving drag path without stealing list-row gestures. */
    private void installSheetDrag(final View target, final View panel) {
        if (target == null || panel == null) return;
        final float touchSlop = Math.max(dp(8), ViewConfiguration.get(target.getContext()).getScaledTouchSlop());
        target.setOnTouchListener(new View.OnTouchListener() {
            // The target is a child of panel. Use raw coordinates so panel translation does not
            // feed back into the next event's local coordinates while the finger is down.
            float downRawX;
            float downRawY;
            float downPanelTranslation;
            long downAt;
            boolean dragging;
            boolean cancelled;

            @Override public boolean onTouch(View view, MotionEvent event) {
                int action = event.getActionMasked();
                if (action == MotionEvent.ACTION_DOWN) {
                    cancelViewAnimationIfRunning(panel);
                    downRawX = event.getRawX();
                    downRawY = event.getRawY();
                    downPanelTranslation = panel.getTranslationY();
                    downAt = event.getEventTime();
                    dragging = false;
                    cancelled = false;
                    return true;
                }
                if (action == MotionEvent.ACTION_MOVE) {
                    float dx = event.getRawX() - downRawX;
                    float dy = event.getRawY() - downRawY;
                    if (!dragging && !cancelled && (Math.abs(dx) > touchSlop || Math.abs(dy) > touchSlop)) {
                        // Lock after slop. Only a clearly downward gesture owns the panel; this
                        // keeps a title tap, horizontal control swipe, or upward scroll intact.
                        dragging = dy > touchSlop && dy > Math.abs(dx) * 1.12f;
                        if (!dragging) cancelled = true;
                    }
                    if (dragging) {
                        // Keep the surface under the finger. The measured height works for short
                        // landscape panels and avoids a second hidden threshold.
                        float maximum = panel.getHeight() > 0 ? panel.getHeight() : dp(480);
                        panel.setTranslationY(Math.max(0f, Math.min(maximum,
                                downPanelTranslation + dy)));
                    }
                    return true;
                }
                if (action == MotionEvent.ACTION_UP) {
                    float dx = event.getRawX() - downRawX;
                    float dy = event.getRawY() - downRawY;
                    long elapsed = Math.max(1L, event.getEventTime() - downAt);
                    float dismissDistance = Math.max(dp(64), panel.getHeight() > 0 ? panel.getHeight() * .25f : dp(120));
                    boolean quickDismiss = dy >= dp(24) && dy * 1000f / elapsed >= dp(820);
                    boolean close = dragging && (dy >= dismissDistance || quickDismiss) &&
                            dy > Math.abs(dx) * 1.05f;
                    if (close && panel == activeOverlayPanel) dismissOverlay();
                    else if (dragging)
                        panel.animate().translationY(0f).setDuration(reduceMotion() ? 80L : 150L).start();
                    dragging = false;
                    cancelled = false;
                    return true;
                }
                if (action == MotionEvent.ACTION_CANCEL) {
                    if (dragging)
                        panel.animate().translationY(0f).setDuration(reduceMotion() ? 80L : 120L).start();
                    dragging = false;
                    cancelled = false;
                    return true;
                }
                return true;
            }
        });
    }

    /** Shared denial path for auth, Web permission and geolocation dialogs. */
    private static final class DenyDialog implements DialogInterface.OnClickListener, DialogInterface.OnCancelListener {
        private final Object request;
        private final String origin;
        DenyDialog(Object request, String origin) { this.request = request; this.origin = origin; }
        @Override public void onClick(DialogInterface dialog, int which) { deny(); }
        @Override public void onCancel(DialogInterface dialog) { deny(); }
        private void deny() {
            if (request instanceof HttpAuthHandler) ((HttpAuthHandler) request).cancel();
            else if (request instanceof PermissionRequest) ((PermissionRequest) request).deny();
            else ((GeolocationPermissions.Callback) request).invoke(origin, false, false);
        }
    }

    private void showActionSheet(String title, String subtitle, String[] items, int[] icons, final SheetHandler handler) {
        showActionSheet(title, subtitle, items, icons, null, null, null, null, handler);
    }

    private void showActionSheet(String title, String subtitle, String[] items, int[] icons,
                                 int[] rowKinds, String[] sectionHeaders, final Runnable backAction,
                                 final SheetHandler handler) {
        showActionSheet(title, subtitle, items, icons, rowKinds, sectionHeaders, backAction, null, handler);
    }

    private void showActionSheet(String title, String subtitle, String[] items, int[] icons,
                                 int[] rowKinds, String[] sectionHeaders, final Runnable backAction,
                                 final Runnable dismissAction, final SheetHandler handler) {
        dismissOverlayForNavigation();
        final int sheetSurface = nightMode ? DARK_SHEET : WHITE;
        final int sheetText = nightMode ? DARK_TEXT : TEXT;
        final int sheetMuted = nightMode ? DARK_MUTED : MUTED;
        final FrameLayout overlay = new FrameLayout(this);
        overlay.setBackgroundColor(Color.argb(104, 0, 0, 0));
        overlay.setClickable(true);
        overlay.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { dismissOverlay(); }
        });

        LinearLayout panel = new LinearLayout(this);
        panel.setTag(SHEET_TAG_SURFACE);
        panel.setOrientation(LinearLayout.VERTICAL);
        panel.setBackground(roundRect(sheetSurface, 20));
        panel.setPadding(dp(8), dp(7), dp(8), dp(8));
        panel.setClickable(true);
        panel.setElevation(dp(12));

        View handle = new View(this);
        handle.setTag(SHEET_TAG_HANDLE);
        handle.setBackground(sheetHandleDrawable());
        LinearLayout.LayoutParams handleParams = new LinearLayout.LayoutParams(dp(48), dp(32));
        handleParams.gravity = Gravity.CENTER_HORIZONTAL;
        handleParams.setMargins(0, 0, 0, 0);
        panel.addView(handle, handleParams);
        handle.setContentDescription("Faites glisser vers le bas pour fermer");
        installSheetDrag(handle, panel);

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.CENTER_VERTICAL);
        header.setPadding(backAction == null ? dp(10) : 0, 0, dp(2), dp(2));
        if (backAction != null) {
            BrowserIconView back = iconButton(BrowserIconView.BACK, "Retour au niveau précédent");
            back.setTintColor(sheetText);
            header.addView(back, new LinearLayout.LayoutParams(dp(42), dp(42)));
            back.setOnClickListener(new View.OnClickListener() {
                @Override public void onClick(View v) { navigateOverlayBack(); }
            });
        }
        LinearLayout titles = new LinearLayout(this);
        titles.setOrientation(LinearLayout.VERTICAL);
        TextView heading = new TextView(this);
        heading.setTag(SHEET_TAG_PRIMARY);
        heading.setText(title);
        heading.setTextColor(sheetText);
        heading.setTextSize(18f);
        heading.setTypeface(android.graphics.Typeface.DEFAULT_BOLD);
        titles.addView(heading);
        if (subtitle != null && subtitle.length() > 0) {
            TextView sub = new TextView(this);
            sub.setTag(SHEET_TAG_MUTED);
            sub.setText(subtitle);
            sub.setTextColor(sheetMuted);
            sub.setTextSize(12f);
            sub.setPadding(0, dp(2), 0, 0);
            titles.addView(sub);
        }
        header.addView(titles, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
        BrowserIconView close = iconButton(BrowserIconView.CLOSE, "Fermer");
        close.setTintColor(sheetText);
        header.addView(close, new LinearLayout.LayoutParams(dp(42), dp(42)));
        panel.addView(header, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
        // The title strip is a generous drag target. Child buttons still receive their own taps,
        // while a swipe that starts beside them behaves like the native bottom-sheet gesture.
        installSheetDrag(header, panel);

        ScrollView scroll = new ScrollView(this);
        scroll.setTag(SHEET_TAG_PLAIN_SURFACE);
        scroll.setFillViewport(false);
        scroll.setVerticalScrollBarEnabled(false);
        scroll.setBackgroundColor(sheetSurface);
        LinearLayout list = new LinearLayout(this);
        list.setTag(SHEET_TAG_PLAIN_SURFACE);
        list.setOrientation(LinearLayout.VERTICAL);
        list.setPadding(0, dp(2), 0, dp(2));
        list.setBackgroundColor(sheetSurface);
        scroll.addView(list);
        int rowsHeight = 0;
        for (int i = 0; i < items.length; i++) {
            final int index = i;
            String section = sectionHeaders != null && i < sectionHeaders.length ? sectionHeaders[i] : null;
            if (section != null && section.trim().length() > 0) {
                TextView sectionLabel = new TextView(this);
                sectionLabel.setTag(SHEET_TAG_ACCENT);
                sectionLabel.setText(section.trim());
                sectionLabel.setTextColor(nightMode ? DARK_ACCENT : BLUE);
                sectionLabel.setTextSize(11.5f);
                sectionLabel.setTypeface(android.graphics.Typeface.DEFAULT_BOLD);
                sectionLabel.setGravity(Gravity.BOTTOM | Gravity.START);
                sectionLabel.setPadding(dp(12), dp(5), dp(8), dp(3));
                sectionLabel.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
                list.addView(sectionLabel, new LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT, dp(24)));
                rowsHeight += 24;
            }
            String item = items[i] == null ? "" : items[i];
            int detailBreak = item.indexOf('\n');
            String primaryText = detailBreak < 0 ? item : item.substring(0, detailBreak);
            String detailText = detailBreak < 0 ? "" : item.substring(detailBreak + 1).trim();
            final int rowKind = rowKinds != null && i < rowKinds.length ? rowKinds[i] : SHEET_ROW_NAVIGATE;
            final boolean toggleRow = rowKind == SHEET_ROW_TOGGLE_OFF || rowKind == SHEET_ROW_TOGGLE_ON;
            int rowHeight = detailText.length() == 0 ? 48 : 60;
            rowsHeight += rowHeight;
            LinearLayout row = new LinearLayout(this);
            row.setTag(SHEET_TAG_ROW);
            row.setOrientation(LinearLayout.HORIZONTAL);
            row.setGravity(Gravity.CENTER_VERTICAL);
            row.setPadding(dp(6), 0, dp(6), 0);
            // Never inherit a selectable drawable from the Activity's original theme. Explicitly
            // painting the row surface prevents stale dark rounded blocks after a live theme
            // switch; BrowserIconView supplies the small pressed affordance independently.
            row.setBackgroundColor(sheetSurface);
            row.setForeground(null);
            row.setStateListAnimator(null);
            row.setBackgroundTintList(null);
            row.setClickable(true);
            BrowserIconView icon = iconButton(icons != null && i < icons.length ? icons[i] : BrowserIconView.MENU, primaryText);
            icon.setClickable(false);
            icon.setTintColor(sheetText);
            row.addView(icon, new LinearLayout.LayoutParams(dp(42), dp(rowHeight)));
            TextView label = new TextView(this);
            label.setTag(SHEET_TAG_PRIMARY);
            label.setText(primaryText);
            label.setTextColor(sheetText);
            label.setTextSize(14.5f);
            label.setSingleLine(true);
            label.setEllipsize(android.text.TextUtils.TruncateAt.END);
            if (detailText.length() > 0) {
                LinearLayout labels = new LinearLayout(this);
                labels.setOrientation(LinearLayout.VERTICAL);
                labels.setGravity(Gravity.CENTER_VERTICAL);
                labels.setPadding(dp(5), 0, dp(3), 0);
                labels.addView(label, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                        ViewGroup.LayoutParams.WRAP_CONTENT));
                TextView detail = new TextView(this);
                detail.setTag(SHEET_TAG_MUTED);
                detail.setText(detailText);
                detail.setTextColor(sheetMuted);
                detail.setTextSize(12f);
                detail.setSingleLine(true);
                detail.setEllipsize(android.text.TextUtils.TruncateAt.END);
                detail.setPadding(0, dp(2), 0, 0);
                labels.addView(detail, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                        ViewGroup.LayoutParams.WRAP_CONTENT));
                row.addView(labels, new LinearLayout.LayoutParams(0, dp(rowHeight), 1f));
            } else {
                label.setGravity(Gravity.CENTER_VERTICAL);
                label.setPadding(dp(5), 0, dp(3), 0);
                row.addView(label, new LinearLayout.LayoutParams(0, dp(rowHeight), 1f));
            }
            if (toggleRow) {
                final Switch toggle = new Switch(this);
                toggle.setChecked(rowKind == SHEET_ROW_TOGGLE_ON);
                toggle.setShowText(false);
                toggle.setClickable(false);
                toggle.setFocusable(false);
                toggle.setMinimumWidth(0);
                int[][] states = new int[][] {
                        new int[] { android.R.attr.state_checked }, new int[] {}
                };
                toggle.setThumbTintList(new ColorStateList(states, new int[] {
                        BLUE, nightMode ? 0xffbdc1c6 : 0xff757575
                }));
                toggle.setTrackTintList(new ColorStateList(states, new int[] {
                        0x761a73e8, nightMode ? 0xff505459 : 0xffbdc1c6
                }));
                row.addView(toggle, new LinearLayout.LayoutParams(dp(54), dp(rowHeight)));
                row.setContentDescription(primaryText + (toggle.isChecked() ? ", activé" : ", désactivé"));
                row.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) {
                        boolean next = !toggle.isChecked();
                        toggle.setChecked(next);
                        v.setContentDescription(primaryText + (next ? ", activé" : ", désactivé"));
                        handler.onItem(index);
                    }
                });
            } else {
                if (rowKind != SHEET_ROW_ACTION) {
                    TextView chevron = new TextView(this);
                    chevron.setTag(SHEET_TAG_MUTED);
                    chevron.setText("›");
                    chevron.setTextColor(sheetMuted);
                    chevron.setTextSize(27f);
                    chevron.setGravity(Gravity.CENTER);
                    chevron.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
                    row.addView(chevron, new LinearLayout.LayoutParams(dp(28), dp(rowHeight)));
                } else {
                row.setPadding(dp(6), 0, dp(14), 0);
                }
                row.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) {
                        dismissOverlayForNavigation();
                        handler.onItem(index);
                    }
                });
            }
            LinearLayout.LayoutParams rowParams = new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, dp(rowHeight));
            list.addView(row, rowParams);
        }
        panel.addView(scroll, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f));

        int safeTop = Math.max(0, systemInsetTop - rootFrame.getPaddingTop());
        int safeBottom = Math.max(0, systemInsetBottom - rootFrame.getPaddingBottom());
        int maxHeight = Math.round(getResources().getDisplayMetrics().heightPixels * .90f) - safeTop - safeBottom;
        int desiredHeight = dp(100 + rowsHeight);
        int panelHeight = Math.min(maxHeight, desiredHeight);
        FrameLayout.LayoutParams panelParams = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, panelHeight, Gravity.BOTTOM);
        panelParams.setMargins(dp(6), safeTop, dp(6), dp(6) + safeBottom);
        overlay.addView(panel, panelParams);
        rootFrame.addView(overlay, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        activeOverlay = overlay;
        activeOverlayPanel = panel;
        activeOverlaySheet = true;
        activeOverlayBackAction = backAction;
        activeOverlayDismissAction = dismissAction;
        overlayDismissInProgress = false;
        // Repaint the fully-built hierarchy so no platform drawable from a previous theme
        // survives a live night-mode switch.
        themeSheetTree(panel);
        Motion.showSheet(overlay, panel, reduceMotion());
        close.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { dismissOverlay(); }
        });
    }

    private void dismissOverlay() {
        if (activeOverlay == null) return;
        final View removing = activeOverlay;
        final View panel = activeOverlayPanel;
        final boolean sheet = activeOverlaySheet;
        final Runnable dismissAction = activeOverlayDismissAction;
        activeOverlay = null;
        activeOverlayPanel = null;
        activeOverlayBackAction = null;
        activeOverlayDismissAction = null;
        activeOverlaySheet = false;
        overlayDismissInProgress = true;
        Motion.hideOverlay(removing, panel, sheet, reduceMotion(), new Runnable() {
            @Override public void run() {
                if (removing.getParent() instanceof ViewGroup) ((ViewGroup) removing.getParent()).removeView(removing);
                overlayDismissInProgress = false;
                if (!activityDestroyed && dismissAction != null) dismissAction.run();
            }
        });
    }

    private void dismissOverlayForNavigation() {
        if (activeOverlay == null) return;
        View removing = activeOverlay;
        View panel = activeOverlayPanel;
        activeOverlay = null;
        activeOverlayPanel = null;
        activeOverlayBackAction = null;
        activeOverlayDismissAction = null;
        activeOverlaySheet = false;
        overlayDismissInProgress = false;
        cancelViewAnimationIfRunning(removing);
        cancelViewAnimationIfRunning(panel);
        if (removing.getParent() instanceof ViewGroup) ((ViewGroup) removing.getParent()).removeView(removing);
    }

    private void navigateOverlayBack() {
        if (activeOverlay == null) return;
        Runnable action = activeOverlayBackAction;
        if (action == null) {
            dismissOverlay();
            return;
        }
        dismissOverlayForNavigation();
        action.run();
    }

    private void registerPredictiveBack() {
        if (Build.VERSION.SDK_INT < 33 || predictiveBackCallback != null) return;
        registerPredictiveBackApi33();
    }

    @android.annotation.TargetApi(33)
    private void registerPredictiveBackApi33() {
        final android.window.OnBackInvokedCallback callback = new android.window.OnBackInvokedCallback() {
            @Override public void onBackInvoked() { handleBrowserBack(); }
        };
        getOnBackInvokedDispatcher().registerOnBackInvokedCallback(
                android.window.OnBackInvokedDispatcher.PRIORITY_DEFAULT, callback);
        predictiveBackCallback = callback;
    }

    private void unregisterPredictiveBack() {
        if (Build.VERSION.SDK_INT < 33 || predictiveBackCallback == null) return;
        unregisterPredictiveBackApi33();
    }

    @android.annotation.TargetApi(33)
    private void unregisterPredictiveBackApi33() {
        try {
            getOnBackInvokedDispatcher().unregisterOnBackInvokedCallback(
                    (android.window.OnBackInvokedCallback) predictiveBackCallback);
        } catch (RuntimeException ignored) {
        }
        predictiveBackCallback = null;
    }

    /** Installs the cold-start payload already assembled on the background startup thread. */
    private void installPreparedDocumentStartUserScripts(WebView target) {
        // Store readiness and view readiness can arrive in either order. Keep the prepared
        // payload until both exist, then consume it once: a later startup callback must not
        // remove a registration just because the token/payload fields were already cleared.
        if (target == null || !startupDataReady || startupScriptPayloadsApplied) return;
        startupScriptPayloadsApplied = true;
        String token = startupScriptToken;
        List<UserScriptStore.DocumentStartPayload> payloads = startupScriptPayloads;
        startupScriptToken = "";
        startupScriptPayloads = Collections.emptyList();
        installDocumentStartUserScripts(target, token, payloads);
    }

    private void installDocumentStartUserScripts(WebView target) {
        // configureWebView() runs before the first WebView is assigned to the Activity. Reuse
        // its background-prepared payload instead of copying and registering it a second time
        // on the UI thread; subsequent tabs keep the normal per-view token/registration path.
        if (!startupReady && webView == null) {
            installPreparedDocumentStartUserScripts(target);
            return;
        }
        if (target == null || scriptStore == null || !scriptStore.hasEnabledScripts()) {
            removeDocumentStartUserScripts(target);
            return;
        }
        String token = UrlCleaner.randomToken();
        List<UserScriptStore.DocumentStartPayload> payloads = scriptStore.buildDocumentStartPayloads(token);
        installDocumentStartUserScripts(target, token, payloads);
    }

    /** UI-only registration; expensive payload assembly is performed before this call. */
    private void installDocumentStartUserScripts(WebView target, String token,
                                                 List<UserScriptStore.DocumentStartPayload> payloads) {
        removeDocumentStartUserScripts(target);
        if (target == null || token == null || token.length() < 32 || payloads == null || payloads.isEmpty() ||
                !WebViewFeature.isFeatureSupported(WebViewFeature.DOCUMENT_START_SCRIPT)) return;
        ArrayList<ScriptHandler> handlers = new ArrayList<ScriptHandler>(payloads.size());
        try {
            for (UserScriptStore.DocumentStartPayload payload : payloads) {
                if (payload == null || payload.source.length() == 0 || payload.allowedOriginRules.isEmpty()) continue;
                handlers.add(WebViewCompat.addDocumentStartJavaScript(target, payload.source,
                        payload.allowedOriginRules));
            }
            if (handlers.isEmpty()) return;
            scriptBridgeTokens.put(target, token);
            scriptHandlers.put(target, Collections.unmodifiableList(handlers));
            documentStartScriptViews.add(target);
        } catch (RuntimeException error) {
            for (ScriptHandler handler : handlers) {
                try { handler.remove(); } catch (RuntimeException ignored) {}
            }
            scriptBridgeTokens.remove(target);
            scriptHandlers.remove(target);
            documentStartScriptViews.remove(target);
        }
    }

    private void removeDocumentStartUserScripts(WebView target) {
        if (target == null) return;
        List<ScriptHandler> handlers = scriptHandlers.remove(target);
        if (handlers != null) for (ScriptHandler handler : handlers)
            if (handler != null) try { handler.remove(); } catch (RuntimeException ignored) {}
        cancelScriptRequests(target);
        scriptBridgeTokens.remove(target);
        documentStartScriptViews.remove(target);
    }

    private void refreshUserScriptRegistrations(boolean reloadActive) {
        final ArrayList<WebView> live = new ArrayList<WebView>();
        for (BrowserTab tab : tabs) if (tab.liveView != null && !live.contains(tab.liveView)) live.add(tab.liveView);
        final boolean reload = reloadActive;
        final long generation = ++scriptRegistrationGeneration;
        final UserScriptStore store = scriptStore;
        Runnable prepare = new Runnable() {
            @Override public void run() {
                final String[] tokens = new String[live.size()];
                final ArrayList<List<UserScriptStore.DocumentStartPayload>> payloads =
                        new ArrayList<List<UserScriptStore.DocumentStartPayload>>(live.size());
                for (int i = 0; i < live.size(); i++) payloads.add(Collections.<UserScriptStore.DocumentStartPayload>emptyList());
                if (store != null && store.hasEnabledScripts()) for (int i = 0; i < live.size(); i++) {
                    tokens[i] = UrlCleaner.randomToken();
                    payloads.set(i, store.buildDocumentStartPayloads(tokens[i]));
                }
                uiHandler.post(new Runnable() {
                    @Override public void run() {
                        if (activityDestroyed || generation != scriptRegistrationGeneration) return;
                        for (int i = 0; i < live.size(); i++)
                            installDocumentStartUserScripts(live.get(i), tokens[i], payloads.get(i));
                        if (reload && webView != null && isNetworkPage(webView.getUrl())) {
                            reloadWebView(webView);
                            toast("Autorisations des scripts utilisateur mises à jour, rechargement de la page en cours");
                        }
                    }
                });
            }
        };
        if (!executeTask(scriptExecutor, prepare)) {
            for (WebView view : live) installDocumentStartUserScripts(view);
            if (reload && webView != null && isNetworkPage(webView.getUrl())) reloadWebView(webView);
        }
    }

    private void cancelScriptRequests(WebView target) {
        String token = scriptBridgeTokens.get(target);
        if (userScriptNetwork != null) userScriptNetwork.cancel(token);
    }

    private long scriptDocumentGeneration(WebView target) {
        Long generation = target == null ? null : scriptDocumentGenerations.get(target);
        return generation == null ? 0L : generation;
    }

    private void advanceScriptDocumentGeneration(WebView target) {
        if (target == null) return;
        long previous = scriptDocumentGeneration(target);
        scriptDocumentGenerations.put(target, previous == Long.MAX_VALUE ? 1L : previous + 1L);
    }

    private void configureWebView(final WebView target) {
        initialNavigationGuards.put(target, new InitialNavigationGuard());
        navigationGestureGuards.put(target, new NavigationGestureGuard(
                ViewConfiguration.get(this).getScaledTouchSlop()));
        mainFrameNavigationContexts.put(target, new MainFrameNavigationContext());
        WebSettings settings = target.getSettings();
        WebViewPolicy.applySecureDefaults(settings, WebSettings.LOAD_DEFAULT);
        settings.setLoadsImagesAutomatically(true);
        settings.setLoadWithOverviewMode(false);
        settings.setUseWideViewPort(false);
        settings.setMediaPlaybackRequiresUserGesture(true);
        // target=_blank and user-gesture popups are promoted to real browser tabs.
        settings.setSupportMultipleWindows(true);
        settings.setTextZoom(100);
        String initialUserAgent = settings.getUserAgentString();
        String mobileUserAgent = WebViewPolicy.mobileUserAgent(initialUserAgent);
        mobileUserAgents.put(target, mobileUserAgent);
        applyDesktopMode(target, settings, initialUserAgent);
        applyPerformanceMode(target, settings);

        CookieManager cookieManager = CookieManager.getInstance();
        cookieManager.setAcceptCookie(true);
        cookieManager.setAcceptThirdPartyCookies(target, acceptThirdPartyCookies);
        // Configure the native renderer before any URL can be loaded. No page-wide JavaScript or
        // DOM traversal is involved in dark mode.
        applyDarkMode(target, settings);
        installDocumentStartUserScripts(target);

        EdgeNavigationController.attach(target, new EdgeNavigationController.Callback() {
            @Override public void onTouchEvent(MotionEvent event) {
                observeNavigationTouch(target, event);
                observeImmersiveTouch(target, event);
            }
            @Override public boolean isEnabled() { return edgeNavigationEnabled; }
            @Override public boolean canGoBack() { return target.canGoBack(); }
            @Override public boolean canGoForward() { return target.canGoForward(); }
            @Override public void goBack() {
                goBackWebView(target);
                scheduleRestoredHomeRepair(target);
            }
            @Override public void goForward() { goForwardWebView(target); }
        });
        target.setOnLongClickListener(new View.OnLongClickListener() {
            @Override public boolean onLongClick(View ignored) { return handleWebViewLongPress(target); }
        });

        if (Build.VERSION.SDK_INT >= 29) {
            RendererWatchdog.attach(target, getMainExecutor(), new RendererWatchdog.Callback() {
                @Override public void onUnresponsive(final WebView view, final RendererWatchdog.Terminator terminateRenderer) {
                    if (view == null || !unresponsiveWebViews.add(view)) return;
                    uiHandler.postDelayed(new Runnable() {
                        @Override public void run() {
                            if (!unresponsiveWebViews.remove(view) || isFinishing()) return;
                            if (!terminateRenderer.terminate()) {
                                try { view.stopLoading(); } catch (RuntimeException ignored) {}
                            }
                            toast("Page sans réponse, redémarrage du moteur de rendu");
                        }
                    }, 4500L);
                }

                @Override public void onResponsive(WebView view) {
                    if (view != null) unresponsiveWebViews.remove(view);
                }
            });
        }

        target.setWebViewClient(new WebViewClient() {
            @Override
            public boolean shouldOverrideUrlLoading(WebView view, String url) {
                clearMainFrameRequest(view);
                if (adPickerSessions.containsKey(view)) {
                    clearMainFrameNavigation(view);
                    return true;
                }
                // Check using the source document before destination settings replace its host.
                // Native touch state also protects providers using the legacy callback.
                if (shouldBlockPageNavigation(view, url, false, false)) return true;
                rememberAcceptedTouchNavigation(view, url, false, false);
                rememberMainFrameNavigation(view, url);
                if (view != webView) return false;
                if (isNetworkPage(url)) {
                    prepareNetworkDestination(view, url);
                    watchInitialNetworkNavigation(view, url);
                }
                return handleNavigation(view, url);
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
                if (adPickerSessions.containsKey(view)) {
                    clearMainFrameNavigation(view);
                    return true;
                }
                if (request == null) return false;
                // Subframe navigation must never change the active page host or its
                // WebSettings. Doing so breaks SPA controls while scrolling still works.
                if (!request.isForMainFrame()) return false;
                clearMainFrameRequest(view);
                String url = request.getUrl().toString();
                if (shouldBlockPageNavigation(view, url, request.hasGesture(), request.isRedirect())) return true;
                rememberAcceptedTouchNavigation(view, url, request.hasGesture(), request.isRedirect());
                rememberMainFrameNavigation(view, url);
                if (view != webView) return false;
                if (isNetworkPage(url)) {
                    prepareNetworkDestination(view, url);
                    watchInitialNetworkNavigation(view, url);
                }
                return handleNavigation(view, url);
            }

            @Override
            public WebResourceResponse shouldInterceptRequest(WebView view, String url) {
                return interceptRequest(view, url);
            }

            @Override
            public WebResourceResponse shouldInterceptRequest(WebView view, WebResourceRequest request) {
                if (request == null) return null;
                return interceptRequest(view, request);
            }

            @Override
            public void onLoadResource(WebView view, String url) {
                super.onLoadResource(view, url);
                // shouldInterceptRequest() already observes media candidates off the UI
                // thread. onLoadResource is a redundant UI-thread callback for every static
                // asset; scanning it here makes image/script-heavy pages compete with Chromium
                // for the frame budget. The explicit media probe still covers DOM/blob players
                // when the media center is opened.
            }

            @Override
            public void onPageStarted(WebView view, String url, android.graphics.Bitmap favicon) {
                super.onPageStarted(view, url, favicon);
                // URL changes from pushState/replaceState keep this generation. A real main-frame
                // navigation advances it before cancelling requests from the outgoing document.
                advanceScriptDocumentGeneration(view);
                NavigationGestureGuard gestureGuard = navigationGestureGuards.get(view);
                String initiatingDocument = protectedNavigationSourceDocument(view);
                long startedAt = SystemClock.uptimeMillis();
                // POST may skip override, and some providers start the page before the
                // request callback. Preserve a verified drag before replacing source state.
                if (gestureGuard != null && gestureGuard.hasRecentDrag(initiatingDocument, startedAt) &&
                        navigationProtectionActive(navigationSourceHost(view, initiatingDocument))) {
                    gestureGuard.onNavigationAccepted(initiatingDocument, url, true, false, startedAt);
                    rememberMainFrameNavigation(view, url);
                }
                MainFrameNavigationContext navigationContext = mainFrameNavigationContexts.get(view);
                if (navigationContext != null) navigationContext.onPageStarted(url);
                if (gestureGuard != null) gestureGuard.onPageStarted(url);
                popupSourceDocuments.remove(view);
                rememberNavigationSourceDocument(view, url);
                if (view == webView) showBrowserChrome(false);
                // A chooser belongs to the document that opened it. If that document
                // navigates before Android returns a result, never deliver the selected
                // URI to the replacement page.
                if (fileChooserCallback != null && fileChooserView == view) finishFileChooser(null);
                String startedHost = hostOf(url);
                cacheFavicon(startedHost, favicon);
                startedPageUrls.put(view, navigationDocumentUrl(url));
                unresponsiveWebViews.remove(view);
                adPickerViews.remove(view);
                adPickerSessions.remove(view);
                if (isQrScannerUrl(url)) qrScannerViews.add(view); else qrScannerViews.remove(view);
                cancelScriptRequests(view);
                if (InternalNavigationPolicy.shouldClearHomeTrust(isHomeUrl(url), url)) {
                    trustedHomeViews.remove(view);
                    customHomeViews.remove(view);
                }
                boolean offline = isOfflineUrl(url);
                if (offline) prepareOfflineDestination(view, url);
                else if (isInternalBrowserUrl(url)) prepareHomeDestination(view);
                else {
                    applyPageAccessPolicy(view, url);
                    applySiteSettings(view, startedHost);
                    // POST and history/provider navigations can bypass shouldOverrideUrlLoading.
                    prepareNavigationConnections(url);
                    installConnectionHintScript(view, url, true);
                }
                updateTabForView(view, url, view.getTitle());
                cosmeticInjected.remove(view);
                if (url != null) {
                    pageHosts.put(view, startedHost);
                    adBlockActiveByView.put(view, Boolean.valueOf(isAdBlockActiveForHost(startedHost)));
                }
                if (view != webView) return;
                // Cancel queued work from the previous document before arranging any early
                // cosmetic task for this one. The old ordering could enqueue the task and then
                // immediately clear it in advanceNavigationSequence().
                advanceNavigationSequence();
                if (url != null) {
                    currentPageUrl = url;
                    currentPageHost = startedHost;
                    if (stagedCredential != null && !currentPageHost.equalsIgnoreCase(stagedCredential.host)) {
                        stagedCredential.clear();
                        stagedCredential = null;
                        stagedCredentialAt = 0L;
                    }
                    mediaSniffer.beginPage(url);
                }
                // Stop the previous document's terminal fade before the new page
                // starts reporting progress. Regular progress updates must not
                // cancel this animation on every callback.
                cancelViewAnimationIfRunning(progressBar);
                blockedAtPageStart = adBlock.getBlockedCount();
                if (view == webView && refreshButton != null) {
                    cancelViewAnimationIfRunning(refreshButton);
                    refreshButton.animate().rotationBy(180f).setDuration(reduceMotion() ? 100L : 220L).start();
                }
                pageCommitted = false;
                pageFinished = false;
                preparedInjection = null;
                schedulePageEnhancements(url, navigationSequence);
                if (url != null && isAdBlockActiveForHost(currentPageHost) &&
                        adBlock.requiresEarlyCosmetic(currentPageHost)) {
                    // Let document-start user scripts claim the navigation worker first; CSS
                    // construction remains off the UI thread and can follow in the same window.
                    scheduleCosmeticInjection(view, currentPageHost);
                }
                requestChromeUpdate();
            }

            @Override
            public void onPageCommitVisible(WebView view, String url) {
                super.onPageCommitVisible(view, url);
                retireMainFrameNavigation(view, url);
                String expectedDocument = startedPageUrls.get(view);
                if (expectedDocument != null && !expectedDocument.equals(navigationDocumentUrl(url))) return;
                NavigationGestureGuard gestureGuard = navigationGestureGuards.get(view);
                if (gestureGuard != null) gestureGuard.onNavigationCommitted(url);
                InitialNavigationGuard guard = initialNavigationGuards.get(view);
                if (guard != null && guard.acknowledge(url) && view == webView && startupNavigationAt != 0L)
                    recordStartupNavigation("Première navigation : engagée", url);
                if (view != webView) return;
                pageCommitted = true;
                injectPreparedStart(navigationSequence);
                // Cached rules compile independently of this callback. Only their network
                // refresh waits for the completed document's idle window.
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                super.onPageFinished(view, url);
                retireMainFrameNavigation(view, url);
                // History can restore the cached home document without onPageStarted. Its
                // last started URL then still belongs to the page we just left; authenticate
                // the restored document before that stale-callback guard returns.
                String settledUrl = view.getUrl() == null ? url : view.getUrl();
                if (isHomeUrl(settledUrl)) verifyTrustedHome(view);
                String expectedDocument = startedPageUrls.get(view);
                if (expectedDocument != null && !expectedDocument.equals(navigationDocumentUrl(url))) {
                    if (view == webView && homeThemeRepairPending &&
                            (isHomeUrl(url) || isHomeUrl(view.getUrl()))) {
                        view.post(new Runnable() {
                            @Override public void run() {
                                if (!activityDestroyed && webView == view &&
                                        isHomeUrl(currentPageUrl) && isHomeUrl(view.getUrl()) && homeThemeRepairPending)
                                    showHome(true);
                            }
                        });
                    }
                    return;
                }
                NavigationGestureGuard gestureGuard = navigationGestureGuards.get(view);
                if (gestureGuard != null) gestureGuard.onNavigationCommitted(url);
                if (isHomeUrl(url) || isHomeUrl(settledUrl)) {
                    // A back gesture can restore a homepage document generated before the
                    // latest theme switch. Native chrome already reflects the new mode, so
                    // replace that stale document before it becomes visible as a mixed page.
                    if (view == webView && (homeThemeRepairPending || !isHomeRenderCurrent(view))) {
                        view.post(new Runnable() {
                            @Override public void run() {
                                if (!activityDestroyed && webView == view &&
                                        isHomeUrl(currentPageUrl) && isHomeUrl(view.getUrl()) &&
                                        (homeThemeRepairPending || !isHomeRenderCurrent(view)))
                                    showHome(true);
                            }
                        });
                        return;
                    }
                }
                InitialNavigationGuard guard = initialNavigationGuards.get(view);
                if (guard != null && guard.acknowledge(settledUrl) && view == webView && startupNavigationAt != 0L)
                    recordStartupNavigation("Première navigation : terminée", settledUrl);
                updateTabForView(view, settledUrl, view.getTitle());
                if (settledUrl != null) {
                    String finishedHost = hostOf(settledUrl);
                    pageHosts.put(view, finishedHost);
                    adBlockActiveByView.put(view, Boolean.valueOf(isAdBlockActiveForHost(finishedHost)));
                    if (isNetworkPage(settledUrl) && isAdBlockActiveForHost(finishedHost)) {
                        // An explicit site rule may already have been scheduled at page start.
                        // Keep that ticket for the same document so the CSS is built only once;
                        // generic subscription selectors still start at page finish.
                        boolean earlyCosmetic = adBlock.requiresEarlyCosmetic(finishedHost);
                        if (!earlyCosmetic || cosmeticInjected.get(view) == null) {
                            if (!earlyCosmetic) cosmeticInjected.remove(view);
                            scheduleCosmeticInjection(view, finishedHost);
                        }
                    }
                }
                if (view != webView) return;
                if (settledUrl != null) {
                    currentPageUrl = settledUrl;
                    currentPageHost = hostOf(settledUrl);
                }
                pageFinished = true;
                pageCommitted = true;
                // onPageFinished can precede window load. The media scheduler verifies the
                // actual load end, then an idle/frame boundary, before wrapping fetch/XHR.
                scheduleLiveMediaCapture(view, settledUrl, navigationSequence);
                if (view == webView && isNetworkPage(settledUrl)) scheduleDeferredStartupWork();
                collectConnectionHints(view, settledUrl, navigationSequence);
                if (refreshButton != null) refreshButton.animate().rotation(0f).setDuration(120L).start();
                injectPreparedStart(navigationSequence);
                injectPreparedEnd(navigationSequence);
                if (dataStore != null && !isInternalBrowserUrl(settledUrl))
                    dataStore.recordVisit(view.getTitle(), settledUrl);
                updateCurrentTab(settledUrl, view.getTitle());
                persistSession();
                requestChromeUpdate();
            }

            @Override
            public void doUpdateVisitedHistory(WebView view, String url, boolean isReload) {
                super.doUpdateVisitedHistory(view, url, isReload);
                // pushState/replaceState can change the page identity without onPageStarted.
                // Keep this separate from startedPageUrls, which also guards page callbacks.
                if (url != null) rememberNavigationSourceDocument(view, url);
                updateTabForView(view, url, view.getTitle());
                if (url != null) pageHosts.put(view, hostOf(url));
                // Cached history restoration may also skip onPageFinished. A URL alone does
                // not grant command access: the probe checks the document's private token.
                if (isHomeUrl(view.getUrl())) verifyTrustedHome(view);
                if (view != webView) return;
                String previousUrl = currentPageUrl;
                if (url != null) {
                    currentPageUrl = url;
                    currentPageHost = hostOf(url);
                }
                String historyUrl = url == null ? view.getUrl() : url;
                if ((isHomeUrl(historyUrl) || isHomeUrl(view.getUrl())) &&
                        (homeThemeRepairPending || !isHomeRenderCurrent(view))) {
                    // History restoration may use the provider's cached document and skip
                    // onPageFinished. Repair the stale themed homepage at the history callback.
                    view.post(new Runnable() {
                        @Override public void run() {
                            if (!activityDestroyed && webView == view &&
                                    isHomeUrl(currentPageUrl) && isHomeUrl(view.getUrl()) &&
                                    (homeThemeRepairPending || !isHomeRenderCurrent(view))) showHome(true);
                        }
                    });
                    return;
                }
                updateCurrentTab(url, view.getTitle());
                requestChromeUpdate();
            }

            public boolean onRenderProcessGone(final WebView view, android.webkit.RenderProcessGoneDetail detail) {
                // A renderer callback can arrive after a tab was closed or frozen. Such a
                // detached view must not tear down the surviving tab set during recovery.
                if (activityDestroyed || view == null || tabForView(view) == null) return true;
                if (!rendererRecoveryPending) {
                    rendererRecoveryPending = true;
                    uiHandler.post(new Runnable() {
                        @Override public void run() { recoverFromRendererLoss(); }
                    });
                }
                return true;
            }

            @Override
            public void onReceivedSslError(WebView view, SslErrorHandler handler, SslError error) {
                handler.cancel();
                if (view == webView && !activityDestroyed) {
                    toast("Échec de la vérification du certificat, chargement arrêté");
                    String failed = error == null ? currentPageUrl : error.getUrl();
                    String current = view.getUrl();
                    if (failed != null && current != null &&
                            sameCredentialDocument(failed, current) &&
                            hostOf(failed).equalsIgnoreCase(currentPageHost)) {
                        maybeOfferCompatibilityMode(failed, "Échec du certificat ou du chargement HTTPS de la page principale");
                    }
                }
            }

            @Override
            public void onReceivedError(WebView view, WebResourceRequest request, WebResourceError error) {
                super.onReceivedError(view, request, error);
                if (request != null && request.isForMainFrame() && request.getUrl() != null)
                    retireMainFrameNavigation(view, request.getUrl().toString());
                if (view == webView && request != null && request.isForMainFrame() &&
                        error != null && compatibilityRelevantError(error.getErrorCode())) {
                    String failed = request.getUrl() == null ? currentPageUrl : request.getUrl().toString();
                    String current = view.getUrl();
                    if (current != null && sameCredentialDocument(failed, current))
                        maybeOfferCompatibilityMode(failed, "Échec du chargement de la page principale (" + error.getErrorCode() + "）");
                }
            }

            @Override
            public void onReceivedHttpAuthRequest(WebView view, final android.webkit.HttpAuthHandler handler, String host, String realm) {
                if (view != webView || handler == null) { if (handler != null) handler.cancel(); return; }
                final String expectedUrl = view.getUrl();
                final String expectedHost = host == null ? "" : host.toLowerCase(Locale.US);
                final EditText username = new EditText(MainActivity.this);
                username.setHint("Nom d'utilisateur");
                username.setSingleLine(true);
                final EditText password = new EditText(MainActivity.this);
                password.setHint("Mot de passe");
                password.setSingleLine(true);
                password.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_PASSWORD);
                LinearLayout fields = new LinearLayout(MainActivity.this);
                fields.setOrientation(LinearLayout.VERTICAL);
                fields.setPadding(dp(18), 0, dp(18), 0);
                fields.addView(username);
                fields.addView(password);
                DenyDialog deny = new DenyDialog(handler, null);
                AlertDialog dialog = new AlertDialog.Builder(MainActivity.this).setTitle("Authentification du site")
                        .setMessage(host + (realm == null || realm.length() == 0 ? "" : " · " + realm)).setView(fields)
                        .setPositiveButton("Connexion", new DialogInterface.OnClickListener() {
                            @Override public void onClick(DialogInterface dialog, int which) {
                                String current = view.getUrl();
                                if (activityDestroyed || view != webView || !sameCredentialDocument(expectedUrl, current) ||
                                        !expectedHost.equalsIgnoreCase(hostOf(current))) {
                                    handler.cancel();
                                    toast("La page a changé, l'authentification a été annulée");
                                    return;
                                }
                                handler.proceed(username.getText().toString(), password.getText().toString());
                            }
                        }).setNegativeButton("Annuler", deny).setOnCancelListener(deny).create();
                secureDialog(dialog);
                dialog.show();
            }
        });

        target.setWebChromeClient(new WebChromeClient() {
            @Override
            public void onProgressChanged(WebView view, int newProgress) {
                if (view == webView) {
                    // A queued or merely accepted navigation commonly reports exactly 10%.
                    // Crossing that boundary proves the main-frame load made forward progress.
                    InitialNavigationGuard guard = initialNavigationGuards.get(view);
                    if (newProgress > 10 && guard != null && !guard.isAcknowledged()) {
                        String url = view.getUrl();
                        if (guard.acknowledge(url) && startupNavigationAt != 0L)
                            recordStartupNavigation("Première navigation : réponse reçue", url);
                    }
                    scheduleProgressUpdate(newProgress);
                }
            }

            @Override
            public void onReceivedTitle(WebView view, String title) {
                updateTabForView(view, view.getUrl(), title);
                if (view == webView) requestChromeUpdate();
            }

            @Override
            public void onReceivedIcon(WebView view, android.graphics.Bitmap icon) {
                cacheFavicon(hostOf(view == null ? null : view.getUrl()), icon);
            }

            @Override
            public boolean onJsPrompt(final WebView view, String url, String message,
                                      final String defaultValue, JsPromptResult result) {
                if (handleQrScannerPrompt(view, message, defaultValue, result)) return true;
                if (handleAdPickerPrompt(view, message, defaultValue, result)) return true;
                if (message != null && (message.startsWith("__MEDIAN_CREDENTIAL__") ||
                        message.startsWith("__MEDIAN_AUTOFILL__"))) {
                    // Legacy page-controlled password markers are inert. Do not parse them or
                    // let them reach Chromium's prompt UI.
                    if (result != null) result.confirm("");
                    return true;
                }
                if (homeToken != null && homeToken.equals(message)) {
                    boolean accepted = result != null && view == webView && isHomeUrl(view.getUrl()) &&
                            trustedHomeViews.contains(view) && !customHomeViews.contains(view) &&
                            defaultValue != null && defaultValue.startsWith("median://");
                    if (result != null) result.confirm("");
                    if (accepted) view.post(new Runnable() {
                        @Override public void run() {
                            if (activityDestroyed || view != webView || !isHomeUrl(view.getUrl()) ||
                                    !trustedHomeViews.contains(view) || customHomeViews.contains(view)) return;
                            handleNavigation(view, defaultValue);
                        }
                    });
                    return true;
                }
                if (handleScriptBridgePrompt(view, url, message, result)) return true;
                return super.onJsPrompt(view, url, message, defaultValue, result);
            }

            @Override
            public void onShowCustomView(View view, CustomViewCallback callback) {
                if (target != webView) { callback.onCustomViewHidden(); return; }
                enterFullscreen(view, callback);
            }

            @Override
            public void onHideCustomView() {
                if (target == webView) exitFullscreen();
            }

            @Override
            public void onPermissionRequest(PermissionRequest request) {
                handleWebPermissionRequest(target, request);
            }

            @Override
            public void onPermissionRequestCanceled(PermissionRequest request) {
                if (request != null && request == pendingPermissionRequest) {
                    pendingPermissionRequest = null;
                    pendingWebPermissionResources = null;
                    pendingPermissionView = null;
                    pendingPermissionOrigin = null;
                }
            }

            @Override
            public void onGeolocationPermissionsShowPrompt(String origin, GeolocationPermissions.Callback callback) {
                handleGeolocationRequest(target, origin, callback);
            }

            @Override
            public boolean onCreateWindow(WebView view, boolean isDialog, boolean isUserGesture, Message resultMsg) {
                if (adPickerSessions.containsKey(view)) return false;
                SiteSettingsStore.SiteSettings site = siteSettingsStore == null
                        ? new SiteSettingsStore.SiteSettings() : siteSettingsStore.forHost(pageHostFor(view));
                int popups = site.get(SiteSettingsStore.POPUPS);
                if (popups == SiteSettingsStore.BLOCK || (!isUserGesture && popups != SiteSettingsStore.ALLOW) ||
                        resultMsg == null || !(resultMsg.obj instanceof WebView.WebViewTransport)) return false;
                // A drag is not an intentional request for a new window. Explicit per-site
                // ALLOW continues to permit automatic popups as the user requested.
                NavigationGestureGuard gestureGuard = navigationGestureGuards.get(view);
                String sourceDocument = navigationSourceDocument(view);
                if (popups != SiteSettingsStore.ALLOW && isUserGesture &&
                        navigationProtectionActive(navigationSourceHost(view, sourceDocument)) &&
                        gestureGuard != null && gestureGuard.hasRecentDrag(sourceDocument, SystemClock.uptimeMillis())) return false;
                if (tabs.size() >= MAX_TABS) {
                    if (isUserGesture) toast("Nombre maximal d'onglets : " + MAX_TABS + " onglets");
                    return false;
                }
                BrowserTab tab = new BrowserTab();
                WebView popup = createConfiguredWebView();
                if (sourceDocument.length() > 0) popupSourceDocuments.put(popup, sourceDocument);
                bindWebViewToTab(tab, popup);
                tab.lastActiveAt = SystemClock.uptimeMillis();
                tabs.add(tab);
                WebView.WebViewTransport transport = (WebView.WebViewTransport) resultMsg.obj;
                transport.setWebView(popup);
                resultMsg.sendToTarget();
                activateTab(tabs.size() - 1);
                return true;
            }

            @Override
            public void onCloseWindow(WebView window) {
                BrowserTab tab = tabForView(window);
                if (tab == null) return;
                int index = tabs.indexOf(tab);
                if (index == currentTabIndex) {
                    closeCurrentTab();
                } else if (index >= 0) {
                    tabs.remove(index);
                    destroyTabView(tab, false);
                    if (index < currentTabIndex) currentTabIndex--;
                    renderedTabCount = null;
                    persistSession();
                    requestChromeUpdate();
                }
            }

            @Override
            public boolean onShowFileChooser(WebView view, ValueCallback<Uri[]> callback, FileChooserParams params) {
                if (view != webView) {
                    try { if (callback != null) callback.onReceiveValue(null); } catch (RuntimeException ignored) {}
                    return true;
                }
                finishFileChooser(null);
                fileChooserCallback = callback;
                fileChooserView = view;
                fileChooserDocumentUrl = navigationDocumentUrl(view.getUrl());
                Intent intent;
                try {
                    intent = params.createIntent();
                } catch (Exception e) {
                    intent = new Intent(Intent.ACTION_GET_CONTENT);
                    intent.addCategory(Intent.CATEGORY_OPENABLE);
                    intent.setType("*/*");
                }
                try {
                    startActivityForResult(intent, FILE_CHOOSER_REQUEST);
                    return true;
                } catch (Exception e) {
                    finishFileChooser(null);
                    toast("Aucun sélecteur de fichiers disponible");
                    return true;
                }
            }
        });

        target.setDownloadListener(new DownloadListener() {
            @Override public void onDownloadStart(String url, String userAgent, String contentDisposition,
                                                  String mimetype, long contentLength) {
                if (adPickerSessions.containsKey(target)) return;
                if (looksLikeUserScript(url)) {
                    installScriptFromUrl(url);
                    return;
                }
                enqueueDownload(target, url, userAgent, contentDisposition, mimetype, contentLength);
            }
        });

    }

    private boolean handleWebViewLongPress(final WebView source) {
        WebView.HitTestResult hit = source == null ? null : source.getHitTestResult();
        if (hit == null) return false;
        int type = hit.getType();
        final boolean image = type == WebView.HitTestResult.IMAGE_TYPE || type == WebView.HitTestResult.SRC_IMAGE_ANCHOR_TYPE;
        boolean link = type == WebView.HitTestResult.SRC_ANCHOR_TYPE || type == WebView.HitTestResult.SRC_IMAGE_ANCHOR_TYPE;
        final String url = hit.getExtra();
        if ((!image && !link) || !isNetworkPage(url)) return false;
        if (!image && looksLikeUserScript(url)) {
            showActionSheet("Lien du script utilisateur", hostOf(url),
                    new String[] { "Installer et vérifier le script", "Copier l'adresse du script", "Ouvrir dans un nouvel onglet" },
                    new int[] { BrowserIconView.SCRIPT, BrowserIconView.PLUS, BrowserIconView.TABS },
                    new SheetHandler() {
                        @Override public void onItem(int which) {
                            if (which == 0) installScriptFromUrl(url);
                            else if (which == 1) {
                                ClipboardManager manager = (ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
                                if (manager != null) manager.setPrimaryClip(ClipData.newPlainText("UserScript", url));
                                toast("Adresse du script copiée");
                            } else openUrlInNewTab(url, true);
                        }
                    });
            return true;
        }
        String[] items = new String[] { "Ouvrir dans un nouvel onglet", "Ouvrir dans un onglet en arrière-plan", "Copier l'adresse", "Partager l'adresse",
                image ? "Télécharger l'image" : "Lien de téléchargement", "Envoyer vers un gestionnaire de téléchargement externe" };
        int[] icons = new int[] { BrowserIconView.PLUS, BrowserIconView.TABS, BrowserIconView.PLUS,
                BrowserIconView.SHARE, BrowserIconView.STORAGE, BrowserIconView.STORAGE };
        showActionSheet(image ? "Image et lien" : "Actions sur le lien", hostOf(url), items, icons, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) openUrlInNewTab(url, true);
                else if (which == 1) openUrlInNewTab(url, false);
                else if (which == 2) {
                    android.content.ClipboardManager manager = (android.content.ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
                    if (manager != null) manager.setPrimaryClip(android.content.ClipData.newPlainText("Lien", url));
                    toast("Adresse copiée");
                } else if (which == 3) {
                    Intent share = new Intent(Intent.ACTION_SEND);
                    share.setType("text/plain");
                    share.putExtra(Intent.EXTRA_TEXT, url);
                    try { startActivity(Intent.createChooser(share, "Partager le lien")); } catch (Exception e) { toast("Aucune application de partage disponible"); }
                } else if (which == 4) {
                    String ua = source.getSettings().getUserAgentString();
                    enqueueDownload(source, url, ua, null, image ? "image/*" : "application/octet-stream");
                } else sendToExternalDownloader(url);
            }
        });
        return true;
    }

    private void openUrlInNewTab(String url, boolean foreground) {
        if (!isNetworkPage(url)) return;
        if (tabs.size() >= MAX_TABS) { toast("Maximum autorisé : " + MAX_TABS + " onglets"); return; }
        BrowserTab tab = new BrowserTab();
        tab.url = url;
        String host = hostOf(url);
        tab.title = host.length() == 0 ? "Nouvel onglet" : host;
        tabs.add(tab);
        if (foreground) activateTab(tabs.size() - 1);
        else {
            renderedTabCount = null;
            persistSession();
            requestChromeUpdate();
            toast("Ouvert dans un onglet en arrière-plan");
        }
    }

    private void enqueueDownload(WebView source, String url, String userAgent,
                                 String contentDisposition, String mimetype) {
        enqueueDownload(source, url, userAgent, contentDisposition, mimetype, 0L);
    }

    private void enqueueDownload(WebView source, String url, String userAgent,
                                 String contentDisposition, String mimetype, long expectedTotalBytes) {
        enqueueDownloadAdvanced(url, userAgent, contentDisposition, mimetype, "",
                downloadContextHeaders(source, url), false, expectedTotalBytes);
    }

    private boolean enqueueDownloadAdvanced(String url, String userAgent, String contentDisposition,
                                            String mimetype, String preferredName, Map<String, String> extraHeaders) {
        return enqueueDownloadAdvanced(url, userAgent, contentDisposition, mimetype, preferredName, extraHeaders, false);
    }

    private boolean enqueueDownloadAdvanced(String url, String userAgent, String contentDisposition,
                                            String mimetype, String preferredName, Map<String, String> extraHeaders,
                                            boolean publicOnly) {
        return enqueueDownloadAdvanced(url, userAgent, contentDisposition, mimetype, preferredName,
                extraHeaders, publicOnly, 0L);
    }

    private boolean enqueueDownloadAdvanced(String url, String userAgent, String contentDisposition,
                                            String mimetype, String preferredName, Map<String, String> extraHeaders,
                                            boolean publicOnly, long expectedTotalBytes) {
        try {
            url = NetworkSecurity.parseHttpUrl(url).toString();
        } catch (Exception invalidUrl) {
            toast("Seules les ressources HTTP(S) valides peuvent être téléchargées");
            return false;
        }
        Uri directory = DownloadDirectory.selectedTree(this);
        if (directory != null && !DownloadDirectory.hasWriteGrant(this, directory)) {
            toast("L'autorisation du dossier de téléchargement a expiré ; veuillez le rechoisir dans les paramètres de téléchargement");
            return false;
        }
        DownloadStore.Item duplicate = services.downloads().findBlockingDuplicate(url, 15000L);
        if (duplicate != null) {
            if (DownloadStore.STATUS_FAILED.equals(duplicate.status))
                toast("Cette même adresse vient d'échouer, veuillez réessayer dans le centre de téléchargements");
            else if (DownloadStore.STATUS_PAUSED.equals(duplicate.status))
                toast("Cette tâche est en pause, veuillez la reprendre dans le centre de téléchargements");
            else toast("Cette même ressource est déjà en cours de téléchargement");
            return false;
        }
        String filename = uniqueDownloadName(DownloadFileTypes.resolveName(
                url, contentDisposition, mimetype, "", preferredName));
        String resolvedMime = DownloadFileTypes.resolveMime(filename, mimetype, "");
        try {
            long expected = Math.max(0L, expectedTotalBytes);
            enqueueAdaptiveFallback(url, userAgent, filename, resolvedMime, extraHeaders, publicOnly, expected);
            toast("Téléchargement lancé : " + filename + (expected > 0L ? " · " + humanBytes(expected) : ""));
            return true;
        } catch (Exception failure) {
            toast("Échec du démarrage du téléchargement : " + safeMessage(failure));
        }
        return false;
    }

    private void enqueueAdaptiveFallback(String url, String userAgent, String filename, String mime,
                                         Map<String, String> extraHeaders, boolean publicOnly,
                                         long expectedTotalBytes) throws Exception {
        if (Build.VERSION.SDK_INT >= 33 &&
                checkSelfPermission(Manifest.permission.POST_NOTIFICATIONS) != PackageManager.PERMISSION_GRANTED)
            requestPermissions(new String[] { Manifest.permission.POST_NOTIFICATIONS }, 409);
        boolean wifiOnly = prefs.getBoolean("download_wifi_only", false);
        boolean allowRoaming = prefs.getBoolean("download_allow_roaming", false);
        boolean chargingOnly = prefs.getBoolean("download_charging_only", false);
        String persistedHeaders = downloadHeadersJson(extraHeaders);
        long id = services.downloads().addAdaptive(url, filename, mime,
                userAgent == null ? "" : userAgent, persistedHeaders,
                wifiOnly, allowRoaming, chargingOnly, publicOnly, expectedTotalBytes);
        try {
            Intent service = new Intent(this, AdaptiveDownloadService.class);
            service.setAction(AdaptiveDownloadService.ACTION_DOWNLOAD);
            service.putExtra(AdaptiveDownloadService.EXTRA_ID, id);
            service.putExtra(AdaptiveDownloadService.EXTRA_URL, url);
            service.putExtra(AdaptiveDownloadService.EXTRA_NAME, filename);
            service.putExtra(AdaptiveDownloadService.EXTRA_MIME, mime);
            service.putExtra(AdaptiveDownloadService.EXTRA_USER_AGENT, userAgent == null ? "" : userAgent);
            String cookie = CookieManager.getInstance().getCookie(url);
            service.putExtra(AdaptiveDownloadService.EXTRA_COOKIE, cookie == null ? "" : cookie);
            service.putExtra(AdaptiveDownloadService.EXTRA_HEADERS, persistedHeaders);
            service.putExtra(AdaptiveDownloadService.EXTRA_WIFI_ONLY, wifiOnly);
            service.putExtra(AdaptiveDownloadService.EXTRA_ALLOW_ROAMING, allowRoaming);
            service.putExtra(AdaptiveDownloadService.EXTRA_CHARGING_ONLY, chargingOnly);
            service.putExtra(AdaptiveDownloadService.EXTRA_PUBLIC_ONLY, publicOnly);
            service.putExtra(AdaptiveDownloadService.EXTRA_TOTAL_BYTES, expectedTotalBytes);
            startForegroundService(service);
        } catch (Exception error) {
            services.downloads().remove(id);
            throw error;
        }
    }

    private Map<String, String> downloadContextHeaders(WebView source, String downloadUrl) {
        HashMap<String, String> headers = new HashMap<String, String>();
        String pageUrl = source == null || source.getUrl() == null ? "" : source.getUrl();
        try {
            URL page = NetworkSecurity.parseHttpUrl(pageUrl);
            URL download = NetworkSecurity.parseHttpUrl(downloadUrl);
            if (NetworkSecurity.sameOrigin(page, download)) headers.put("Referer", page.toString());
            else if (!"https".equalsIgnoreCase(page.getProtocol()) || "https".equalsIgnoreCase(download.getProtocol())) {
                String origin = page.getProtocol() + "://" + page.getHost();
                int port = page.getPort();
                if (port >= 0 && port != page.getDefaultPort()) origin += ":" + port;
                headers.put("Referer", origin + "/");
            }
        } catch (Exception ignored) {}
        return headers;
    }

    private String uniqueDownloadName(String requested) {
        String name = DownloadFileTypes.sanitize(requested);
        if (name.length() == 0) name = "download.bin";
        HashSet<String> used = new HashSet<String>();
        for (DownloadStore.Item item : services.downloads().getAll()) used.add(item.filename.toLowerCase(Locale.US));
        if (!used.contains(name.toLowerCase(Locale.US))) return name;
        int dot = name.lastIndexOf('.');
        String base = dot > 0 ? name.substring(0, dot) : name;
        String extension = dot > 0 ? name.substring(dot) : "";
        for (int i = 1; i <= 999; i++) {
            String candidate = base + " (" + i + ")" + extension;
            if (!used.contains(candidate.toLowerCase(Locale.US))) return candidate;
        }
        return base + '-' + System.currentTimeMillis() + extension;
    }

    private String downloadHeadersJson(Map<String, String> headers) {
        JSONObject object = new JSONObject();
        if (headers == null) return object.toString();
        for (Map.Entry<String, String> header : headers.entrySet()) {
            String name = header.getKey() == null ? "" : header.getKey().trim();
            String value = header.getValue() == null ? "" : header.getValue();
            if (!NetworkSecurity.validHeader(name, value) || NetworkSecurity.isForbiddenRequestHeader(name) ||
                    NetworkSecurity.isCredentialHeader(name) || "user-agent".equalsIgnoreCase(name)) continue;
            try { object.put(name, value); } catch (Exception ignored) {}
        }
        return object.toString();
    }

    private boolean handleScriptBridgePrompt(final WebView source, String pageUrl, String message, JsPromptResult result) {
        final String prefix = "__MEDIAN_BRIDGE__";
        if (message == null || !message.startsWith(prefix)) return false;
        if (message.length() > SCRIPT_BRIDGE_MAX_MESSAGE_CHARS) {
            result.confirm(bridgeError("request too large"));
            return true;
        }
        String response;
        try {
            JSONObject request = new JSONObject(message.substring(prefix.length()));
            String token = request.optString("t", "");
            final String scriptId = request.optString("s", "");
            String action = request.optString("a", "");
            JSONObject args = request.optJSONObject("p");
            if (args == null) args = new JSONObject();
            String currentUrl = source == null ? "" : source.getUrl();
            String expectedToken = source == null ? null : scriptBridgeTokens.get(source);
            if (source == null || expectedToken == null || token.length() < 32 || !token.equals(expectedToken) ||
                    currentUrl == null || !scriptStore.isRunnable(scriptId) || !scriptStore.matchesUrl(scriptId, currentUrl)) {
                response = bridgeError("unauthorized");
            } else if (!scriptStore.allowsApi(scriptId, action)) {
                response = bridgeError("grant denied");
            } else if ("getValue".equals(action)) {
                String key = args.optString("k", "");
                boolean exists = services.scriptValues().contains(scriptId, key);
                String value = services.scriptValues().getJson(scriptId, key, args.optString("d", "null"));
                response = new JSONObject().put("ok", true).put("exists", exists).put("v", value).toString();
            } else if ("setValue".equals(action)) {
                response = bridgeOk(services.scriptValues().setJson(scriptId, args.optString("k", ""), args.optString("v", "null")));
            } else if ("deleteValue".equals(action)) {
                response = bridgeOk(services.scriptValues().delete(scriptId, args.optString("k", "")));
            } else if ("listValues".equals(action)) {
                response = new JSONObject().put("ok", true).put("v", new JSONArray(services.scriptValues().listJson(scriptId))).toString();
            } else if ("getTab".equals(action)) {
                String tabId = scriptTabIds.get(source);
                String raw = tabId == null ? "{}" : scriptTabValues.get(scriptId + "|" + tabId);
                Object value = new JSONTokener(raw == null ? "{}" : raw).nextValue();
                if (!(value instanceof JSONObject)) value = new JSONObject();
                response = new JSONObject().put("ok", true).put("v", value).toString();
            } else if ("saveTab".equals(action)) {
                String tabId = scriptTabIds.get(source);
                String raw = args.optString("v", "{}");
                Object value = raw.length() <= 1024 * 1024 ? new JSONTokener(raw).nextValue() : null;
                boolean allowed = tabId != null && value instanceof JSONObject;
                if (allowed) allowed = scriptTabValues.put(scriptId + "|" + tabId, raw);
                response = bridgeOk(allowed);
            } else if ("getTabs".equals(action)) {
                JSONObject values = new JSONObject();
                String tabKeyPrefix = scriptId + "|";
                for (Map.Entry<String, String> entry : scriptTabValues.entries()) {
                    if (!entry.getKey().startsWith(tabKeyPrefix)) continue;
                    try {
                        Object value = new JSONTokener(entry.getValue()).nextValue();
                        if (value instanceof JSONObject)
                            values.put(entry.getKey().substring(tabKeyPrefix.length()), value);
                    } catch (Exception ignored) {}
                }
                String currentTab = scriptTabIds.get(source);
                if (currentTab != null && !values.has(currentTab)) values.put(currentTab, new JSONObject());
                response = new JSONObject().put("ok", true).put("v", values).toString();
            } else if ("openTab".equals(action)) {
                String url = args.optString("u", "");
                boolean allowed = isHttpUrl(url);
                if (allowed) openUrlInNewTab(url, args.optBoolean("active", true));
                response = bridgeOk(allowed);
            } else if ("clipboard".equals(action)) {
                android.content.ClipboardManager manager = (android.content.ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
                String value = args.optString("v", "");
                boolean allowed = source == webView && activityResumed && manager != null;
                if (allowed) manager.setPrimaryClip(android.content.ClipData.newPlainText("UserScript", value));
                response = bridgeOk(allowed);
            } else if ("notification".equals(action)) {
                String text = args.optString("text", "");
                String notice = args.optString("title", "Median") + (text.length() == 0 ? "" : "：" + text);
                toast(UiText.ellipsize(notice, 240));
                response = bridgeOk(true);
            } else if ("cookie".equals(action)) {
                response = userScriptNetwork().handleCookie(currentUrl, args);
            } else if ("download".equals(action)) {
                String url = args.optString("u", "");
                boolean allowed = isHttpUrl(url) && scriptStore.canConnect(scriptId, url, currentUrl);
                Map<String, String> headers = jsonStringMap(args.optJSONObject("h"));
                boolean pageIsLocal = false;
                try { pageIsLocal = NetworkSecurity.isObviouslyLocalHost(NetworkSecurity.normalizedHost(NetworkSecurity.parseHttpUrl(currentUrl))); }
                catch (Exception ignored) {}
                response = bridgeOk(allowed && enqueueDownloadAdvanced(url, source.getSettings().getUserAgentString(), null,
                        "application/octet-stream", args.optString("n", ""), headers, !pageIsLocal));
            } else if ("xhr".equals(action)) {
                response = userScriptNetwork().request(source, token, scriptId, args, currentUrl,
                        scriptDocumentGeneration(source));
            } else if ("xhrAbort".equals(action)) {
                userScriptNetwork().abort(token, args.optString("i", ""));
                response = bridgeOk(true);
            } else response = bridgeError("unknown action");
        } catch (Exception e) {
            response = bridgeError("bad request");
        }
        result.confirm(response);
        return true;
    }

    /** Allocate privileged networking only when a userscript actually uses it. */
    private UserScriptNetwork userScriptNetwork() {
        if (userScriptNetwork == null) {
            userScriptNetwork = new UserScriptNetwork(uiHandler, new UserScriptNetwork.Host() {
                @Override public boolean executeNetworkTask(Runnable task) {
                    if (scriptNetworkExecutor == null || scriptNetworkExecutor.isShutdown())
                        throw new RejectedExecutionException("Service réseau des scripts indisponible");
                    return executeTask(scriptNetworkExecutor, task);
                }
                @Override public boolean canConnect(String scriptId, String url, String pageUrl) {
                    return scriptStore.canConnect(scriptId, url, pageUrl);
                }
                @Override public boolean isCurrentRequestDocument(WebView source, String token,
                        String scriptId, long documentGeneration) {
                    if (activityDestroyed || source == null) return false;
                    String expected = scriptBridgeTokens.get(source);
                    String current = source.getUrl();
                    return expected != null && token.equals(expected) &&
                            documentGeneration == scriptDocumentGeneration(source) &&
                            scriptStore.matchesUrl(scriptId, current);
                }
                @Override public void scheduleCookieFlush() { MainActivity.this.scheduleCookieFlush(); }
            });
        }
        return userScriptNetwork;
    }

    private void scheduleCookieFlush() {
        cookieFlushScheduler.schedule();
    }

    private static Map<String, String> jsonStringMap(JSONObject object) {
        HashMap<String, String> result = new HashMap<String, String>();
        if (object == null) return result;
        Iterator<String> keys = object.keys();
        while (keys.hasNext()) {
            String key = keys.next();
            result.put(key, object.optString(key, ""));
        }
        return result;
    }

    private static String bridgeOk(boolean ok) {
        try { return new JSONObject().put("ok", ok).toString(); }
        catch (Exception ignored) { return ok ? "{\"ok\":true}" : "{\"ok\":false}"; }
    }

    private static String bridgeError(String error) {
        try { return new JSONObject().put("ok", false).put("error", error).toString(); }
        catch (Exception ignored) { return "{\"ok\":false}"; }
    }

    private static boolean isHttpUrl(String value) {
        try {
            URL parsed = NetworkSecurity.parseHttpUrl(value);
            return !"median.invalid".equalsIgnoreCase(parsed.getHost());
        } catch (Exception ignored) { return false; }
    }

    private WebResourceResponse interceptRequest(WebView source, String requestUrl) {
        Uri uri = null;
        try { uri = Uri.parse(requestUrl); } catch (RuntimeException ignored) {}
        WebResourceResponse homeAsset = interceptHomeAsset(source, uri);
        if (homeAsset != null) return homeAsset;
        String pageHost = pageHostFor(source);
        if (cachedAdBlockActive(source, pageHost) &&
                (uri == null ? adBlock.shouldBlock(requestUrl, pageHost) : adBlock.shouldBlock(uri, pageHost))) {
            return blockedResponse();
        }
        observeMediaIfLikely(source, uri, "", pageHost);
        return null;
    }

    private WebResourceResponse interceptRequest(WebView source, Uri requestUri) {
        WebResourceResponse homeAsset = interceptHomeAsset(source, requestUri);
        if (homeAsset != null) return homeAsset;
        String pageHost = pageHostFor(source);
        if (cachedAdBlockActive(source, pageHost) && adBlock.shouldBlock(requestUri, pageHost)) {
            return blockedResponse();
        }
        observeMediaIfLikely(source, requestUri, "", pageHost);
        return null;
    }

    private WebResourceResponse interceptRequest(WebView source, WebResourceRequest request) {
        Uri requestUri = request.getUrl();
        boolean mainFrame = request.isForMainFrame();
        WebResourceResponse homeAsset = interceptHomeAsset(source, requestUri);
        if (homeAsset != null) return homeAsset;
        if (customHomeViews.contains(source) && !mainFrame && requestUri != null &&
                ("http".equalsIgnoreCase(requestUri.getScheme()) || "https".equalsIgnoreCase(requestUri.getScheme())) &&
                !"median.invalid".equalsIgnoreCase(requestUri.getHost())) return blockedResponse();
        String pageHost = pageHostFor(source);
        // The context only applies to the main-frame request that starts a navigation. Avoid
        // taking its synchronized lock for every image/script/font/subframe callback; busy pages
        // can dispatch hundreds of those while the navigation ticket remains untouched.
        MainFrameNavigationContext navigationContext = mainFrame ? mainFrameNavigationContexts.get(source) : null;
        MainFrameNavigationContext.Snapshot initiating = mainFrame &&
                navigationContext != null && requestUri != null
                ? navigationContext.take(requestUri.toString(), true) : null;
        NavigationGestureGuard gestureGuard = mainFrame ? navigationGestureGuards.get(source) : null;
        // Request callbacks run off the UI thread. Read only cached source state here;
        // WebView.getUrl() is forbidden and destination settings may already be applied.
        String sourceDocument = "";
        long requestAt = mainFrame ? SystemClock.uptimeMillis() : 0L;
        if (mainFrame) {
            sourceDocument = popupSourceDocuments.get(source);
            if (sourceDocument == null || sourceDocument.length() == 0)
                sourceDocument = navigationSourceDocuments.get(source);
            if (sourceDocument == null) sourceDocument = "";
            if (gestureGuard != null)
                sourceDocument = gestureGuard.navigationSourceDocument(sourceDocument, requestAt);
        }
        String sourceHost = mainFrame ? hostOf(sourceDocument) : "";
        String ruleHost = initiating != null ? initiating.sourceHost :
                mainFrame && sourceHost.length() > 0 ? sourceHost : pageHost;
        boolean adBlockActive = initiating != null ? initiating.protectionEnabled && adBlockEnabled :
                mainFrame && sourceHost.length() > 0 ? navigationProtectionActive(sourceHost) :
                        cachedAdBlockActive(source, pageHost);
        // Request.getRequestHeaders() crosses the WebView provider boundary. Read it for rules
        // that need resource type and for a narrow set of extensionless media endpoints. The
        // performance preset never changes blocking or navigation protection.
        boolean readAccept = shouldReadAcceptHeader(requestUri, mainFrame);
        // Only extensionless media header probes need URL classification before blocking.
        // Reuse that result after blocking; ordinary static assets are scanned just once and
        // blocked assets never pay for optional media discovery.
        boolean mediaUrlClassified = source == webView && !mainFrame && requestUri != null && readAccept;
        boolean inspectMedia = mediaUrlClassified && MediaResourceSniffer.isLikelyMediaRequest(
                requestUri.getEncodedPath(), requestUri.getEncodedQuery(), "");
        boolean mediaHeaderNeeded = mediaUrlClassified && MediaResourceSniffer.shouldProbeMediaHeaders(
                requestUri.getEncodedPath(), requestUri.getEncodedQuery(), inspectMedia);
        boolean needHeaders = mainFrame ||
                (adBlockActive && adBlock.requiresRequestHeaders() && readAccept) ||
                mediaHeaderNeeded;
        Map<String, String> requestHeaders = needHeaders ? request.getRequestHeaders() : null;
        String accept = readAccept ? requestHeader(requestHeaders, "Accept") : "";
        if (adBlockActive && adBlock.shouldBlock(requestUri, ruleHost, accept, mainFrame)) {
            boolean preserveDocument = mainFrame && gestureGuard != null && requestUri != null &&
                    gestureGuard.shouldBlockNavigation(sourceDocument, requestUri.toString(), request.hasGesture(),
                            request.isRedirect(), requestAt);
            if (preserveDocument)
                gestureGuard.onNavigationBlocked(sourceDocument, requestUri.toString(), requestAt);
            return preserveDocument ? blockedNavigationResponse() : blockedResponse();
        }
        if (mainFrame && adBlockActive && gestureGuard != null && requestUri != null) {
            String targetUrl = requestUri.toString();
            if (gestureGuard.shouldBlockNavigation(sourceDocument, targetUrl, request.hasGesture(),
                    request.isRedirect(), requestAt) &&
                    !adBlock.isExplicitlyAllowed(requestUri, ruleHost, "text/html", true)) {
                gestureGuard.onNavigationBlocked(sourceDocument, targetUrl, requestAt);
                return blockedNavigationResponse();
            }
            gestureGuard.onNavigationAccepted(sourceDocument, targetUrl, request.hasGesture(),
                    request.isRedirect(), requestAt);
        }
        if (source == webView && requestUri != null) {
            if (!mediaUrlClassified) inspectMedia = MediaResourceSniffer.isLikelyMediaRequest(
                    requestUri.getEncodedPath(), requestUri.getEncodedQuery(), "");
            String mediaHint = mediaRequestHint(requestHeaders, accept);
            if (inspectMedia || MediaResourceSniffer.isMediaMimeHint(mediaHint))
                observeMediaCandidate(source, requestUri, mediaHint, pageHost);
        }
        return null;
    }

    private boolean cachedAdBlockActive(WebView source, String pageHost) {
        if (source == null) return isAdBlockActiveForHost(pageHost);
        Boolean cached = adBlockActiveByView.get(source);
        if (cached != null) return cached.booleanValue();
        boolean active = isAdBlockActiveForHost(pageHost);
        adBlockActiveByView.put(source, Boolean.valueOf(active));
        return active;
    }

    private static String requestHeader(Map<String, String> headers, String wanted) {
        if (headers == null || headers.size() == 0) return "";
        String exact = headers.get(wanted);
        if (exact != null) return exact;
        for (Map.Entry<String, String> entry : headers.entrySet()) {
            if (wanted.equalsIgnoreCase(entry.getKey())) return entry.getValue() == null ? "" : entry.getValue();
        }
        return "";
    }

    private static String mediaRequestHint(Map<String, String> headers, String accept) {
        String destination = requestHeader(headers, "Sec-Fetch-Dest");
        if ("video".equalsIgnoreCase(destination)) return "video/*";
        if ("audio".equalsIgnoreCase(destination)) return "audio/*";
        String range = requestHeader(headers, "Range");
        if (range.regionMatches(true, 0, "bytes=", 0, 6) &&
                (accept == null || accept.length() == 0 || "*/*".equals(accept.trim())))
            return "application/x-median-range";
        return accept == null ? "" : accept;
    }

    private static boolean shouldReadAcceptHeader(Uri uri, boolean mainFrame) {
        if (mainFrame) return true;
        if (uri == null) return false;
        // Keep this request-interception filter allocation-free for the common static assets.
        // Encoded paths are sufficient for suffix classification and avoid Uri's decode step.
        String path = uri.getEncodedPath();
        if (path == null) return true;
        return !(endsWithIgnoreCase(path, ".png") || endsWithIgnoreCase(path, ".jpg") ||
                endsWithIgnoreCase(path, ".jpeg") || endsWithIgnoreCase(path, ".gif") ||
                endsWithIgnoreCase(path, ".webp") || endsWithIgnoreCase(path, ".svg") ||
                endsWithIgnoreCase(path, ".avif") || endsWithIgnoreCase(path, ".css") ||
                endsWithIgnoreCase(path, ".js") || endsWithIgnoreCase(path, ".mjs") ||
                endsWithIgnoreCase(path, ".woff") || endsWithIgnoreCase(path, ".woff2") ||
                endsWithIgnoreCase(path, ".ttf") || endsWithIgnoreCase(path, ".otf") ||
                endsWithIgnoreCase(path, ".ico") || endsWithIgnoreCase(path, ".json") ||
                endsWithIgnoreCase(path, ".xml") || endsWithIgnoreCase(path, ".rss") ||
                endsWithIgnoreCase(path, ".atom") || endsWithIgnoreCase(path, ".html") ||
                endsWithIgnoreCase(path, ".htm") || endsWithIgnoreCase(path, ".mp4") ||
                endsWithIgnoreCase(path, ".webm") || endsWithIgnoreCase(path, ".m3u8") ||
                endsWithIgnoreCase(path, ".mpd") || endsWithIgnoreCase(path, ".mp3") ||
                endsWithIgnoreCase(path, ".m4a") || endsWithIgnoreCase(path, ".aac") ||
                endsWithIgnoreCase(path, ".ogg") || endsWithIgnoreCase(path, ".opus") ||
                endsWithIgnoreCase(path, ".wav") || endsWithIgnoreCase(path, ".m4s") ||
                endsWithIgnoreCase(path, ".ts"));
    }

    private static boolean endsWithIgnoreCase(String value, String suffix) {
        int start = value.length() - suffix.length();
        return start >= 0 && value.regionMatches(true, start, suffix, 0, suffix.length());
    }

    private void observeMediaIfLikely(WebView source, Uri uri, String accept, String pageHost) {
        if (source != webView || uri == null) return;
        if (!MediaResourceSniffer.isLikelyMediaRequest(uri.getEncodedPath(), uri.getEncodedQuery(), accept)) return;
        observeMediaCandidate(source, uri, accept, pageHost);
    }

    /** Records a candidate after its URL has already passed the cheap path/query filter. */
    private void observeMediaCandidate(WebView source, Uri uri, String accept, String pageHost) {
        if (source != webView || uri == null) return;
        mediaSniffer.observe(uri.toString(), accept, pageHost, "request", 0, 0, 0d);
    }

    private boolean isCurrentLiveMediaDocument(WebView target, String documentUrl, long sequence) {
        if (!isCurrentPageCallback(target, sequence) || !isNetworkPage(documentUrl)) return false;
        String current = target.getUrl();
        String started = startedPageUrls.get(target);
        return isNetworkPage(current) && documentUrl.equals(navigationDocumentUrl(current)) &&
                started != null && documentUrl.equals(navigationDocumentUrl(started));
    }

    /** Small load-state query; no resource/DOM scans or persistent observers before load. */
    private static String liveMediaLoadGateScript(String documentUrl, long sequence, boolean install) {
        String key = JSONObject.quote(sequence + ":" + documentUrl);
        return "(function(){try{var k=" + key + ",u=" + JSONObject.quote(documentUrl) + ";" +
                "function current(){return String(location.href).split('#')[0]===u;}" +
                "function loaded(){if(document.readyState!=='complete')return false;var p=window.performance,n,e;" +
                "if(!p)return false;try{if(typeof p.getEntriesByType==='function')n=p.getEntriesByType('navigation');}catch(_){}" +
                // A modern entry with loadEventEnd=0 is still loading; never replace it with
                // the legacy value. Old providers without navigation entries use Timing 1.
                "if(n&&n.length)e=n[0].loadEventEnd;else e=p.timing&&p.timing.loadEventEnd;" +
                "return typeof e==='number'&&isFinite(e)&&e>0;}" +
                "if(!current()||!loaded())return 0;var g=window.__medianMediaLoadGate;" +
                "if(!g||g.k!==k||g.d!==document){" + (install ? "return 0;" :
                "g={k:k,d:document,ready:false};window.__medianMediaLoadGate=g;" +
                // Deferred JS only signals readiness. Native code rechecks the active view,
                // navigation and Activity before submitting the synchronous install payload.
                "var mark=function(){if(window.__medianMediaLoadGate===g&&g.d===document&&current()&&loaded())g.ready=true;};" +
                "if(typeof window.requestIdleCallback==='function')window.requestIdleCallback(mark,{timeout:1000});" +
                "else if(typeof window.requestAnimationFrame==='function')window.requestAnimationFrame(function(){window.requestAnimationFrame(mark);});" +
                "return 0;") + "}if(!g.ready)return 0;" +
                (install ? MediaProbeScript.install() : "") + "return 1;}catch(e){return 0;}})();";
    }

    private void installLiveMediaCapture(WebView target, String documentUrl, long sequence) {
        if (!isCurrentLiveMediaDocument(target, documentUrl, sequence)) return;
        try { target.evaluateJavascript(liveMediaLoadGateScript(documentUrl, sequence, true), null); }
        catch (RuntimeException ignored) {}
    }

    /** Waits for real load completion and idle/double-rAF, with a finite polling budget. */
    private void scheduleLiveMediaCapture(final WebView target, final String documentUrl,
                                          final long expectedSequence) {
        final String expectedDocument = navigationDocumentUrl(documentUrl);
        if (!isCurrentLiveMediaDocument(target, expectedDocument, expectedSequence) ||
                liveMediaCaptureSequence == expectedSequence) return;
        liveMediaCaptureSequence = expectedSequence;
        uiHandler.postDelayed(new Runnable() {
            private int checks;
            @Override public void run() {
                if (!isCurrentLiveMediaDocument(target, expectedDocument, expectedSequence)) return;
                checks++;
                final Runnable retry = this;
                try {
                    target.evaluateJavascript(liveMediaLoadGateScript(expectedDocument, expectedSequence, false),
                            new ValueCallback<String>() {
                        @Override public void onReceiveValue(String value) {
                            if (!isCurrentLiveMediaDocument(target, expectedDocument, expectedSequence)) return;
                            if ("1".equals(value)) installLiveMediaCapture(target, expectedDocument, expectedSequence);
                            else if ("0".equals(value) && checks < 24) {
                                uiHandler.postDelayed(retry, checks < 4 ? 500L : 2000L);
                            }
                        }
                    });
                } catch (RuntimeException ignored) {}
            }
        }, 250L);
    }

    /** Copies WebView-owned icon pixels before handing the bounded write to the worker queue. */
    private void cacheFavicon(final String host, android.graphics.Bitmap icon) {
        if (icon == null || host == null || host.length() == 0 || favicons == null ||
                scriptNetworkExecutor == null || scriptNetworkExecutor.isShutdown()) return;
        final android.graphics.Bitmap copy;
        try { copy = icon.copy(android.graphics.Bitmap.Config.ARGB_8888, false); }
        catch (RuntimeException error) { return; }
        if (!executeTask(scriptNetworkExecutor, new Runnable() {
            @Override public void run() {
                boolean stored = false;
                try {
                    // File metadata checks can block on cold storage; keep them off the UI
                    // callback that receives the page favicon.
                    if (!activityDestroyed && !favicons.has(host)) stored = favicons.put(host, copy);
                } finally { copy.recycle(); }
                if (stored && !activityDestroyed) uiHandler.post(new Runnable() {
                    @Override public void run() {
                        if (!activityDestroyed && webView != null && isHomeUrl(webView.getUrl()))
                            refreshHomeFavicon(webView, host);
                    }
                });
            }
        })) {
            copy.recycle();
        }
    }

    private WebResourceResponse interceptHomeAsset(WebView source, Uri uri) {
        if (source == null || uri == null || !trustedHomeViews.contains(source) ||
                !"https".equalsIgnoreCase(uri.getScheme()) || !"median.invalid".equalsIgnoreCase(uri.getHost())) return null;
        if ("/home-custom".equals(uri.getPath())) {
            if (!customHomeViews.contains(source)) return blockedResponse();
            String html = prefs == null ? "" : prefs.getString("home_custom_html", "");
            if (!CustomHomeHtml.valid(html)) return blockedResponse();
            byte[] data = CustomHomeHtml.document(html).getBytes(StandardCharsets.UTF_8);
            return new WebResourceResponse("text/html", "UTF-8", new ByteArrayInputStream(data));
        }
        if ("/favicon".equals(uri.getPath())) {
            InputStream input = favicons == null ? null : favicons.open(uri.getQueryParameter("host"));
            if (input == null) return new WebResourceResponse("text/plain", "UTF-8", 404, "Not Found",
                    Collections.<String, String>emptyMap(), new ByteArrayInputStream(EMPTY_RESPONSE));
            return new WebResourceResponse("image/png", null, input);
        }
        if (homeImages == null) return blockedResponse();
        HomeImageStore.Kind kind;
        if ("/home-wallpaper".equals(uri.getPath())) kind = HomeImageStore.Kind.WALLPAPER;
        else if ("/home-logo".equals(uri.getPath())) kind = HomeImageStore.Kind.LOGO;
        else return null;
        try {
            InputStream input = homeImages.open(kind);
            return input == null ? blockedResponse() : new WebResourceResponse(homeImages.mime(kind), null, input);
        } catch (Exception ignored) {
            return blockedResponse();
        }
    }

    private void scheduleCosmeticInjection(final WebView source, final String pageHost) {
        if (source == null || pageHost == null || pageHost.length() == 0) return;
        // YouTube is intentionally excluded from cosmetic filtering because generic selectors
        // can interfere with its player. Avoid even scheduling an empty cleanup script there.
        if (!adBlock.cosmeticFilteringAllowed(pageHost)) return;
        final String documentUrl = startedPageUrls.get(source);
        if (documentUrl == null || !isNetworkPage(documentUrl)) return;
        // Generic subscription selectors are useful after the document has painted, but a large
        // CSS payload can compete with the first interactive frame. Explicit user selectors keep
        // their document-start path; generic selectors yield briefly to first paint.
        final long uiDelay = adBlock.requiresEarlyCosmetic(pageHost) ? 0L : 120L;
        final Object ticket = new Object();
        if (cosmeticInjected.putIfAbsent(source, ticket) != null) return;
        if (!executeTask(navigationExecutor, new Runnable() {
            @Override public void run() {
                if (cosmeticInjected.get(source) != ticket || activityDestroyed ||
                        !documentUrl.equals(startedPageUrls.get(source)) ||
                        !pageHost.equalsIgnoreCase(pageHostFor(source))) {
                    cosmeticInjected.remove(source, ticket);
                    return;
                }
                final String css = adBlock.cosmeticCssForHost(pageHost);
                // Quote and assemble the payload off the UI thread. JSONObject.quote scans the
                // whole CSS string and was visible as a main-thread hitch on large subscriptions.
                final String script = "(function(){var u=" + JSONObject.quote(documentUrl) + ",c=" + JSONObject.quote(css) +
                        ",n=0;function f(){if(location.href.split('#')[0]!==u)return;var p=document.head||document.documentElement;" +
                        "if(!p){if(++n<10)setTimeout(f,30);return;}var s=document.getElementById('__median_adblock');" +
                        "if(!c){if(s)s.remove();return;}if(!s){s=document.createElement('style');s.id='__median_adblock';p.appendChild(s);}if(s.textContent!==c)s.textContent=c;}f();})();";
                Runnable apply = new Runnable() {
                    @Override public void run() {
                        if (cosmeticInjected.get(source) != ticket) return;
                        if (activityDestroyed || tabForView(source) == null ||
                                !documentUrl.equals(startedPageUrls.get(source)) ||
                                !documentUrl.equals(navigationDocumentUrl(source.getUrl())) ||
                                !pageHost.equalsIgnoreCase(pageHostFor(source)) || !isAdBlockActiveForHost(pageHost)) {
                            cosmeticInjected.remove(source, ticket);
                            return;
                        }
                        try { source.evaluateJavascript(script, null); }
                        catch (RuntimeException ignored) { cosmeticInjected.remove(source, ticket); }
                        // Keep the ticket settled for this document so blocked subresources do not
                        // enqueue another CSS build.
                    }
                };
                if (uiDelay == 0L) uiHandler.post(apply); else uiHandler.postDelayed(apply, uiDelay);
            }
        })) cosmeticInjected.remove(source, ticket);
    }

    private void refreshCosmeticFilters() {
        if (activityDestroyed) return;
        for (BrowserTab tab : tabs) {
            WebView source = tab.liveView;
            if (source == null || !isNetworkPage(source.getUrl())) continue;
            String host = hostOf(source.getUrl());
            if (!isAdBlockActiveForHost(host)) continue;
            cosmeticInjected.remove(source);
            scheduleCosmeticInjection(source, host);
        }
    }

    private WebResourceResponse blockedResponse() {
        return new WebResourceResponse("text/plain", "UTF-8", new ByteArrayInputStream(EMPTY_RESPONSE));
    }

    private WebResourceResponse blockedNavigationResponse() {
        // A 204 cancels main-frame navigation without committing an empty replacement
        // document. This also covers POST requests that skip the override callback.
        return new WebResourceResponse("text/plain", "UTF-8", 204, "No Content",
                Collections.<String, String>emptyMap(), new ByteArrayInputStream(EMPTY_RESPONSE));
    }

    private void observeNavigationTouch(WebView source, MotionEvent event) {
        NavigationGestureGuard guard = navigationGestureGuards.get(source);
        if (guard == null || event == null) return;
        String document = navigationSourceDocument(source);
        long now = SystemClock.uptimeMillis();
        int action = event.getActionMasked();
        int pointers = event.getPointerCount();
        if (action == MotionEvent.ACTION_DOWN) {
            guard.onDown(document, now, event.getX(), event.getY(), pointers);
        } else if (action == MotionEvent.ACTION_MOVE) {
            guard.onMove(document, now, event.getX(), event.getY(), pointers);
        } else if (action == MotionEvent.ACTION_POINTER_DOWN || action == MotionEvent.ACTION_POINTER_UP) {
            guard.reset();
        } else if (action == MotionEvent.ACTION_UP) {
            guard.onUp(document, now, pointers);
        } else if (action == MotionEvent.ACTION_CANCEL) {
            guard.onCancel(document, now);
        }
    }

    private String navigationSourceDocument(WebView source) {
        if (source == null) return "";
        String opener = popupSourceDocuments.get(source);
        if (opener != null && opener.length() > 0) return opener;
        String remembered = navigationSourceDocuments.get(source);
        if (remembered != null && remembered.length() > 0) return remembered;
        String current = source.getUrl();
        return current == null ? "" : navigationDocumentUrl(current);
    }

    private void rememberNavigationSourceDocument(WebView source, String url) {
        String document = navigationDocumentUrl(url);
        String previous = navigationSourceDocuments.put(source, document);
        if (document.equals(previous)) return;
        NavigationGestureGuard guard = navigationGestureGuards.get(source);
        if (guard != null) guard.migrateDocument(previous, document);
    }

    private String protectedNavigationSourceDocument(WebView source) {
        String document = navigationSourceDocument(source);
        NavigationGestureGuard guard = navigationGestureGuards.get(source);
        return guard == null ? document : guard.navigationSourceDocument(document, SystemClock.uptimeMillis());
    }

    private void rememberAcceptedTouchNavigation(WebView source, String targetUrl,
                                                  boolean hasGesture, boolean serverRedirect) {
        NavigationGestureGuard guard = navigationGestureGuards.get(source);
        if (guard == null) return;
        String document = protectedNavigationSourceDocument(source);
        if (navigationProtectionActive(navigationSourceHost(source, document)))
            guard.onNavigationAccepted(document, targetUrl, hasGesture, serverRedirect, SystemClock.uptimeMillis());
    }

    private String navigationSourceHost(WebView source, String document) {
        String host = hostOf(document);
        if (host.length() > 0) return host;
        return pageHostFor(source);
    }

    private boolean navigationProtectionActive(String sourceHost) {
        return sourceHost != null && sourceHost.length() > 0 && isAdBlockActiveForHost(sourceHost);
    }

    private void rememberMainFrameNavigation(WebView source, String targetUrl) {
        String sourceHost = navigationSourceHost(source, protectedNavigationSourceDocument(source));
        rememberMainFrameNavigation(source, targetUrl, sourceHost, navigationProtectionActive(sourceHost));
    }

    private void rememberMainFrameNavigation(WebView source, String targetUrl, String sourceHost,
                                              boolean protectionEnabled) {
        MainFrameNavigationContext context = mainFrameNavigationContexts.get(source);
        if (context != null) context.arm(targetUrl, sourceHost, protectionEnabled);
    }

    private void clearMainFrameRequest(WebView source) {
        MainFrameNavigationContext context = mainFrameNavigationContexts.get(source);
        if (context != null) context.clear();
    }

    private void clearMainFrameNavigation(WebView source) {
        clearMainFrameRequest(source);
        NavigationGestureGuard guard = navigationGestureGuards.get(source);
        if (guard != null) guard.reset();
    }

    private void retireMainFrameNavigation(WebView source, String url) {
        MainFrameNavigationContext context = mainFrameNavigationContexts.get(source);
        if (context != null) context.clearForUrl(url);
    }

    private void reloadWebView(WebView target) {
        clearMainFrameNavigation(target);
        prepareHistoryConnectionHints(target, 0);
        target.reload();
    }

    private void goBackWebView(WebView target) {
        clearMainFrameNavigation(target);
        prepareHistoryConnectionHints(target, -1);
        target.goBack();
    }

    private void goForwardWebView(WebView target) {
        clearMainFrameNavigation(target);
        prepareHistoryConnectionHints(target, 1);
        target.goForward();
    }

    private void prepareHistoryConnectionHints(WebView target, int offset) {
        if (target == null) return;
        String url = null;
        if (offset == 0) url = target.getUrl();
        else {
            android.webkit.WebBackForwardList history = target.copyBackForwardList();
            int index = history.getCurrentIndex() + offset;
            if (index >= 0 && index < history.getSize()) url = history.getItemAtIndex(index).getUrl();
        }
        if (isNetworkPage(url)) {
            prepareNavigationConnections(url);
            installConnectionHintScript(target, url);
        } else removeConnectionHintScript(target);
    }

    private boolean shouldBlockPageNavigation(WebView source, String targetUrl, boolean hasGesture,
                                               boolean serverRedirect) {
        if (source == null || !isNetworkPage(targetUrl)) return false;
        String sourceDocument = protectedNavigationSourceDocument(source);
        String sourceHost = navigationSourceHost(source, sourceDocument);
        if (!navigationProtectionActive(sourceHost)) return false;
        Uri target;
        try { target = Uri.parse(targetUrl); } catch (RuntimeException ignored) { return false; }
        NavigationGestureGuard guard = navigationGestureGuards.get(source);
        long navigationAt = SystemClock.uptimeMillis();
        // Main-frame document rules are evaluated against the page that initiated the request.
        if (adBlock.shouldBlock(target, sourceHost, "text/html", true)) {
            if (guard != null && guard.shouldBlockNavigation(sourceDocument, targetUrl, hasGesture,
                    serverRedirect, navigationAt))
                guard.onNavigationBlocked(sourceDocument, targetUrl, navigationAt);
            return true;
        }
        if (guard == null ||
                !guard.shouldBlockNavigation(sourceDocument, targetUrl, hasGesture, serverRedirect,
                        navigationAt)) return false;
        // A navigation heuristic must also respect scoped @@ document allow rules.
        boolean navigationAllowed = adBlock.isExplicitlyAllowed(target, sourceHost, "text/html", true);
        if (!navigationAllowed)
            guard.onNavigationBlocked(sourceDocument, targetUrl, navigationAt);
        return !navigationAllowed;
    }

    private boolean handleNavigation(WebView source, String url) {
        if (url == null) return false;
        if (!startupReady && url.startsWith("median://")) {
            requireStartupReady();
            return true;
        }
        Uri parsed;
        try { parsed = Uri.parse(url); } catch (RuntimeException ignored) { return true; }
        if ("median".equalsIgnoreCase(parsed.getScheme())) {
            if (!InternalNavigationPolicy.canHandleCommand(
                    source != null && trustedHomeViews.contains(source),
                    source != null && customHomeViews.contains(source))) {
                // Internal schemes from ordinary webpages are blocked silently. A legitimate
                // homepage click must never punish the user because WebView exposed a pending URL.
                return true;
            }
            Uri uri = Uri.parse(url);
            String host = uri.getHost();
            if ("engine".equals(host)) {
                setSearchEngine(uri.getQueryParameter("name"));
            } else if ("search".equals(host)) {
                String engine = uri.getQueryParameter("engine");
                String query = uri.getQueryParameter("q");
                setSearchEngine(engine);
                loadInput(query);
            } else if ("open".equals(host)) {
                loadInput(uri.getQueryParameter("url"));
            } else if ("bookmarks".equals(host)) {
                openBookmarkManager(null);
            } else if ("folders".equals(host)) {
                openBookmarkManager(null);
            } else if ("folder".equals(host)) {
                bookmarkFolderRootBackAction = null;
                showBookmarkFolder(uri.getQueryParameter("id"));
            }
            return true;
        }
        if (isReservedInternalHost(url)) {
            retireMainFrameNavigation(source, url);
            // Only pages rendered by Median itself may occupy the private internal origin.
            return !isHomeUrl(url) && !isQrScannerUrl(url);
        }
        if (looksLikeUserScript(url)) {
            retireMainFrameNavigation(source, url);
            installScriptFromUrl(url);
            return true;
        }
        if (isNetworkPage(url)) {
            String cleaned = shouldCleanTracking(hostOf(url)) ? UrlCleaner.cleanTracking(url) : url;
            if (!url.equals(cleaned)) {
                loadNetworkUrlFromPage(source, cleaned);
                toast("Paramètres de suivi supprimés");
                return true;
            }
        }
        if (shouldUpgradeHttp(url)) {
            loadNetworkUrlFromPage(source, "https://" + url.substring(7));
            return true;
        }
        if (isNetworkPage(url) || "about:blank".equalsIgnoreCase(url) || isOfflineUrl(url)) return false;
        if (url.regionMatches(true, 0, "data:", 0, 5) || url.regionMatches(true, 0, "about:", 0, 6)) { toast("Redirection de la page vers une adresse interne opaque bloquée"); return true; }
        confirmExternalNavigation(url);
        return true;
    }

    private boolean isOfflineUrl(String url) {
        try {
            Uri uri = Uri.parse(url);
            String name = uri.getLastPathSegment();
            return "content".equalsIgnoreCase(uri.getScheme()) && OfflineContentProvider.AUTHORITY.equals(uri.getAuthority()) &&
                    name != null && name.matches("[A-Za-z0-9._-]+") && name.endsWith(".mht");
        } catch (RuntimeException ignored) { return false; }
    }

    private String homeOpenMode() {
        return HomeOpenPolicy.normalize(prefs.getString("home_open_mode", ""),
                prefs.getBoolean("restore_tabs", false));
    }

    private String normalizeConfiguredHomeUrl(String raw) {
        String value = raw == null ? "" : raw.trim();
        if (value.length() == 0 || value.length() > 2048) return "";
        if (!OmniboxInput.isExplicitHttpUrl(value)) {
            if (!OmniboxInput.looksLikeWebAddress(value)) return "";
            value = OmniboxInput.withDefaultHttpsScheme(value);
        }
        try { value = NetworkSecurity.parseHttpUrl(value).toString(); }
        catch (Exception invalid) { return ""; }
        if ("median.invalid".equalsIgnoreCase(Uri.parse(value).getHost())) return "";
        if (shouldUpgradeHttp(value)) value = "https://" + value.substring(7);
        try { return NetworkSecurity.parseHttpUrl(value).toString(); }
        catch (Exception invalid) { return ""; }
    }

    private String configuredHomeUrl() {
        String custom = normalizeConfiguredHomeUrl(prefs.getString("home_custom_url", ""));
        return HomeOpenPolicy.usesCustomUrl(homeOpenMode(), false, custom) ? custom : HOME_URL;
    }

    private String homeOpenBehaviorLabel() {
        String mode = homeOpenMode();
        if (HomeOpenPolicy.KEEP_LAST.equals(mode)) return "Conserver le contenu de la dernière visite";
        if (HomeOpenPolicy.OPEN_CUSTOM_URL.equals(mode)) {
            String custom = normalizeConfiguredHomeUrl(prefs.getString("home_custom_url", ""));
            return custom.length() == 0 ? "Page personnalisée (non configurée)" : "Page personnalisée · " + hostOf(custom);
        }
        return "Ouvrir la page d'accueil";
    }

    private void openConfiguredHome() {
        String target = configuredHomeUrl();
        if (isHomeUrl(target)) showHome();
        else {
            updateCurrentTab(target, "Accueil");
            loadInput(target);
        }
    }

    /** Applies page-type access independently from performance tuning or the previously visible URL. */
    private void applyPageAccessPolicy(WebView target, String url) {
        if (target == null) return;
        boolean offline = isOfflineUrl(url);
        WebSettings settings = target.getSettings();
        settings.setAllowContentAccess(offline);
        settings.setBlockNetworkLoads(offline);
    }

    /** Restores the trusted local homepage baseline after restrictive site or MHTML settings. */
    private void prepareHomeDestination(WebView target) {
        if (target == null) return;
        removeConnectionHintScript(target);
        clearMainFrameNavigation(target);
        applyPageAccessPolicy(target, HOME_URL);
        appliedSiteSettings.remove(target);
        WebSettings settings = target.getSettings();
        target.setBackgroundColor(nightMode ? DARK_WEB : WHITE);
        if (WebViewFeature.isFeatureSupported(WebViewFeature.ALGORITHMIC_DARKENING)) {
            try { WebSettingsCompat.setAlgorithmicDarkeningAllowed(settings, false); }
            catch (RuntimeException ignored) {}
        }
        if (Build.VERSION.SDK_INT >= 29) {
            try { settings.setForceDark(WebSettings.FORCE_DARK_OFF); }
            catch (RuntimeException ignored) {}
        }
        settings.setJavaScriptEnabled(true);
        settings.setLoadsImagesAutomatically(true);
        settings.setBlockNetworkImage(false);
        settings.setMixedContentMode(WebSettings.MIXED_CONTENT_NEVER_ALLOW);
        settings.setTextZoom(100);
    }

    /** MHTML can read only its own provider content and cannot execute archived JavaScript. */
    private void prepareOfflineDestination(WebView target, String url) {
        if (target == null || !isOfflineUrl(url)) return;
        removeConnectionHintScript(target);
        clearMainFrameNavigation(target);
        applyPageAccessPolicy(target, url);
        // A cached settings key must never suppress re-applying JavaScript/image policy when the
        // user returns to the same online host.
        appliedSiteSettings.remove(target);
        WebSettings settings = target.getSettings();
        settings.setJavaScriptEnabled(false);
        settings.setLoadsImagesAutomatically(true);
        settings.setBlockNetworkImage(false);
    }

    /** Clears any offline-page state before WebView accepts an HTTP(S) main-frame request. */
    private void prepareNetworkDestination(WebView target, String url) {
        if (target == null || !isNetworkPage(url)) return;
        prepareNetworkDestination(target, url, hostOf(url));
    }

    private void prepareNetworkDestination(WebView target, String url, String host) {
        trustedHomeViews.remove(target);
        customHomeViews.remove(target);
        applyPageAccessPolicy(target, url);
        applySiteSettings(target, host);
        installConnectionHintScript(target, url);
    }

    private void removeConnectionHintScript(WebView target) {
        connectionHints.removeConnectionHintScript(target);
    }

    private void installConnectionHintScript(WebView target, String url) {
        connectionHints.installConnectionHintScript(target, url);
    }

    private void installConnectionHintScript(WebView target, String url, boolean applyToCurrentDocument) {
        connectionHints.installConnectionHintScript(target, url, applyToCurrentDocument);
    }

    private void collectConnectionHints(WebView source, String url, long sequence) {
        connectionHints.collectConnectionHints(source, url, sequence);
    }

    private void clearConnectionHints() {
        connectionHints.clearConnectionHints();
    }

    private void prepareNavigationConnections(String url) {
        connectionHints.prepareNavigationConnections(url);
    }

    /** Prepares the destination settings before issuing an HTTP(S) navigation. */
    private void loadNetworkUrl(WebView target, String url) {
        clearMainFrameNavigation(target);
        String host = hostOf(url);
        loadNetworkUrl(target, url, host, navigationProtectionActive(host));
    }

    private void loadNetworkUrlFromPage(WebView source, String url) {
        String sourceHost = navigationSourceHost(source, protectedNavigationSourceDocument(source));
        rememberAcceptedTouchNavigation(source, url, false, false);
        loadNetworkUrl(source, url, sourceHost, navigationProtectionActive(sourceHost));
    }

    private void loadNetworkUrl(WebView target, String url, String sourceHost, boolean protectionEnabled) {
        if (target == null || url == null) return;
        String host = hostOf(url);
        if (host.length() == 0 || !(url.regionMatches(true, 0, "https://", 0, 8) ||
                url.regionMatches(true, 0, "http://", 0, 7))) return;

        // Let Chromium prepare its own reusable connection while the destination's settings and
        // navigation bookkeeping are applied. This is an origin hint for an accepted navigation.
        prepareNavigationConnections(url);

        // Mark that user has navigated when loading a network URL
        if (target == webView && !isHomeUrl(url)) {
            userHasNavigated = true;
        }

        rememberMainFrameNavigation(target, url, sourceHost, protectionEnabled);
        prepareNetworkDestination(target, url, host);
        watchInitialNetworkNavigation(target, url);
        if (target == webView) {
            currentPageUrl = url;
            currentPageHost = host;
        }
        startedPageUrls.remove(target);
        target.loadUrl(url);
    }

    private void watchInitialNetworkNavigation(final WebView target, String url) {
        if (target == null || target != webView || !startupReady) return;
        // Every caller has already accepted an HTTP(S) main-frame destination. Re-parsing it into
        // java.net.URL here only allocates on the first-navigation path and cannot make loadUrl safer.
        InitialNavigationGuard guard = initialNavigationGuards.get(target);
        if (guard == null) {
            InitialNavigationGuard created = new InitialNavigationGuard();
            InitialNavigationGuard existing = initialNavigationGuards.putIfAbsent(target, created);
            guard = existing == null ? created : existing;
        }
        long generation = guard.arm(url);
        if (generation != 0L) {
            if (startupNavigationAt == 0L) startupNavigationAt = SystemClock.elapsedRealtime();
            // A cold Chromium provider can spend a short interval before it dispatches
            // onPageStarted. Recovery remains bounded, while startedPageUrls prevents a second
            // socket once the provider has accepted the request.
            scheduleInitialNavigationRetry(target, generation, INITIAL_NAVIGATION_ACK_MS);
        }
    }

    private void scheduleInitialNavigationRetry(final WebView target, final long generation, long delayMs) {
        if (generation == 0L) return;
        uiHandler.postDelayed(new Runnable() {
            @Override public void run() {
                if (activityDestroyed || target != webView) return;
                InitialNavigationGuard guard = initialNavigationGuards.get(target);
                if (guard == null || guard.pendingGeneration() != generation || !activityResumed) return;
                // onPageStarted means the provider accepted the document, but it can remain at
                // the initial 10% progress for a slow origin. Reloading an already-started page
                // here creates a second connection and is the main source of cold-start stalls.
                if (startedPageUrls.get(target) != null) return;
                String providerUrl = target.getUrl();
                if (target.getProgress() > 10 && providerUrl != null &&
                        providerUrl.equals(currentPageUrl) && isNetworkPage(providerUrl)) {
                    // Some WebView versions update getUrl() before dispatching onPageStarted.
                    // Treat that state as an acknowledgement instead of issuing a duplicate
                    // socket request during the cold provider window.
                    if (guard.acknowledge(providerUrl))
                        recordStartupNavigation("Première navigation : acceptée", providerUrl);
                    return;
                }
                // Several System WebView builds publish the destination URL before their first
                // progress callback. That is already an accepted navigation; reloading it here
                // creates a second socket and can make a cold page appear to take several
                // seconds. Retire the watchdog and let the provider finish its queued request.
                if (providerUrl != null && providerUrl.equals(currentPageUrl) &&
                        isNetworkPage(providerUrl)) {
                    if (guard.acknowledge(providerUrl))
                        recordStartupNavigation("Première navigation : acceptée", providerUrl);
                    return;
                }
                if (!target.isAttachedToWindow()) {
                    scheduleInitialNavigationRetry(target, generation, 220L);
                    return;
                }
                String retryUrl = guard.claimRetry(generation);
                if (retryUrl.length() == 0) return;
                recordStartupNavigation("Rechargement de la première navigation", retryUrl);
                String retryHost = hostOf(retryUrl);
                clearMainFrameNavigation(target);
                prepareNetworkDestination(target, retryUrl, retryHost);
                currentPageUrl = retryUrl;
                currentPageHost = retryHost;
                if (retryUrl.equals(target.getUrl())) reloadWebView(target);
                else target.loadUrl(retryUrl);
            }
        }, Math.max(0L, delayMs));
    }

    /** Persists one privacy-safe cold-start record for the built-in compatibility report. */
    private void recordStartupNavigation(String result, String url) {
        if (prefs == null || startupNavigationAt == 0L) return;
        long now = SystemClock.elapsedRealtime();
        PackageInfo provider = WebView.getCurrentWebViewPackage();
        String webViewVersion = provider == null ? "Inconnu" : provider.packageName + " " + provider.versionName;
        String report = result + "\nPrêt : " + Math.max(0L, startupReadyAt - startupStartedAt) +
                " ms · première navigation : " + Math.max(0L, startupNavigationAt - startupStartedAt) +
                " ms · actuel : " + Math.max(0L, now - startupStartedAt) + " ms\nSite cible : " +
                hostOf(url) + "\nSystem WebView：" + webViewVersion + "\nPréparation du moteur : " + webViewStartupDiagnostic +
                "\nPréparation des connexions : " + WebViewNavigationWarmupCompat.getDiagnosticReport();
        prefs.edit().putString(PREF_STARTUP_DIAGNOSTIC, report).apply();
    }

    private void loadInput(String input) {
        if (input == null) return;
        if (!startupReady) {
            pendingStartupInput = input;
            return;
        }
        startupSessionPending = false;
        String text = input.trim();
        if (text.length() == 0) return;
        boolean explicitHttp = OmniboxInput.isExplicitHttpUrl(text);
        if (explicitHttp) {
            try { text = NetworkSecurity.parseHttpUrl(text).toString(); }
            catch (Exception invalidUrl) { toast("Adresse web invalide"); return; }
        }
        if (shouldUpgradeHttp(text)) text = "https://" + text.substring(7);
        if (explicitHttp || "about:blank".equals(text)) {
            if (explicitHttp) {
                if (shouldCleanTracking(hostOf(text))) text = UrlCleaner.cleanTracking(text);
                loadNetworkUrl(webView, text);
            } else {
                clearMainFrameNavigation(webView);
                trustedHomeViews.remove(webView);
                customHomeViews.remove(webView);
                applyPageAccessPolicy(webView, text);
                currentPageUrl = text;
                currentPageHost = "";
                webView.loadUrl(text);
            }
        } else if (OmniboxInput.looksLikeWebAddress(text)) {
            String candidate;
            try { candidate = NetworkSecurity.parseHttpsUrl(OmniboxInput.withDefaultHttpsScheme(text)).toString(); }
            catch (Exception invalidUrl) { toast("Adresse web invalide"); return; }
            loadNetworkUrl(webView, candidate);
        } else {
            loadSearch(text, searchEngine);
        }
    }

    private void loadSearch(String query, String engine) {
        if (query == null || query.trim().length() == 0) return;
        try {
            String q = URLEncoder.encode(query.trim(), "UTF-8");
            String url = searchEngines.template(engine).replace("%s", q);
            loadNetworkUrl(webView, url);
        } catch (Exception e) {
            toast("Impossible de créer l'adresse de recherche");
        }
    }

    private void showHome() {
        showHome(false);
    }

    /** Renders the local home page, optionally resetting stale themed history. */
    private void showHome(boolean resetHistory) {
        if (webView == null) return;
        prepareHomeDestination(webView);
        currentPageUrl = HOME_URL;
        trustedHomeViews.add(webView);
        HomePageConfig config = homePageConfig();
        if (config.customHtmlEnabled) customHomeViews.add(webView);
        else customHomeViews.remove(webView);
        List<BrowserDataStore.Bookmark> bookmarks = dataStore == null
                ? Collections.<BrowserDataStore.Bookmark>emptyList() : dataStore.bookmarks();
        List<HomePage.Shortcut> shortcuts = homeShortcuts(bookmarks);
        String renderKey = homeRenderKey(config, shortcuts);
        boolean alreadyRendered = renderKey.equals(renderedHomeKeys.get(webView)) &&
                isHomeUrl(webView.getUrl()) && trustedHomeViews.contains(webView);
        if (!alreadyRendered) {
            if (!renderKey.equals(cachedHomeKey)) {
                cachedHomeHtml = HomePage.html(searchEngine, bookmarks, nightMode, homeToken(), config,
                        searchEngines.customEngines(), shortcuts);
                cachedHomeKey = renderKey;
            }
            renderedHomeKeys.put(webView, renderKey);

            if (resetHistory) {
                // A theme switch rebuilds the local document. WebView otherwise keeps the
                // previous themed home entry in its back stack, so an edge-back immediately
                // after the switch resurrects the old black/white document behind the new
                // native chrome. Only that explicit transition resets history; ordinary home
                // refreshes keep the user's navigation stack intact.
                try {
                    webView.stopLoading();
                    webView.clearHistory();
                } catch (RuntimeException ignored) {
                }
            }
            // A null history URL becomes about:blank. On back, the visible home still has
            // its search form but fails the native home-origin check, so commands are lost.
            webView.loadDataWithBaseURL(HOME_URL, cachedHomeHtml, "text/html", "UTF-8", HOME_URL);
        }
        // Optional icon downloads are best-effort and never part of the render critical path.
        if (startupReady) scheduleHomeFaviconPrefetch(webView, shortcuts, renderKey);
        currentPageHost = "";
        if (webView != null) pageHosts.put(webView, "");
        homeThemeRepairPending = false;
        updateCurrentTab(HOME_URL, "Accueil");
        requestChromeUpdate();
    }

    private List<HomePage.Shortcut> homeShortcuts(List<BrowserDataStore.Bookmark> bookmarks) {
        ArrayList<HomePage.Shortcut> result = new ArrayList<HomePage.Shortcut>();
        if (bookmarks != null) for (BrowserDataStore.Bookmark item : bookmarks) {
            String parent = bookmarkFolders == null ? BookmarkFolderStore.ROOT : bookmarkFolders.parentForUrl(item.url);
            if (parent.length() == 0)
                result.add(new HomePage.Shortcut(false, "", item.title, item.url, item.createdAt));
        }
        if (bookmarkFolders != null) for (BookmarkFolderStore.Folder folder : bookmarkFolders.homeFolders())
            result.add(new HomePage.Shortcut(true, folder.id, folder.name, "", folder.createdAt));
        Collections.sort(result, new java.util.Comparator<HomePage.Shortcut>() {
            @Override public int compare(HomePage.Shortcut a, HomePage.Shortcut b) {
                return a.createdAt == b.createdAt ? 0 : (a.createdAt > b.createdAt ? -1 : 1);
            }
        });
        return result;
    }

    /** Favicon downloads are deliberately lazy and bounded so opening the home page never waits. */
    private void scheduleHomeFaviconPrefetch(final WebView target, List<HomePage.Shortcut> shortcuts,
                                             final String renderKey) {
        if (target == null || shortcuts == null || favicons == null || scriptNetworkExecutor == null ||
                scriptNetworkExecutor.isShutdown() || activityDestroyed) return;
        int scheduled = 0;
        for (HomePage.Shortcut item : shortcuts) {
            if (scheduled >= 12) break;
            if (item == null || item.folder) continue;
            final String host = HomePage.faviconHostForUrl(item.url);
            if (host.length() == 0 || favicons.has(host) || !faviconFetchQueued.add(host)) continue;
            scheduled++;
            if (!executeTask(scriptNetworkExecutor, new Runnable() {
                @Override public void run() {
                    boolean stored = false;
                    try { stored = favicons.fetchAndStore(host); }
                    finally { faviconFetchQueued.remove(host); }
                    if (!stored || activityDestroyed) return;
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            if (activityDestroyed || target != webView || !isHomeUrl(target.getUrl()) ||
                                    !trustedHomeViews.contains(target) ||
                                    !renderKey.equals(renderedHomeKeys.get(target))) return;
                            refreshHomeFavicon(target, host);
                        }
                    });
                }
            })) faviconFetchQueued.remove(host);
        }
    }

    private void refreshHomeFavicon(WebView target, String host) {
        if (target == null || host == null || host.length() == 0) return;
        String script = "(function(h){var a=document.querySelectorAll('img[data-favicon-host]'),i,x,f;" +
                "for(i=0;i<a.length;i++){x=a[i];if(x.getAttribute('data-favicon-host')===h){" +
                "x.hidden=false;x.src='/favicon?host='+encodeURIComponent(h)+'&v=1';" +
                "f=x.nextElementSibling;if(f)f.hidden=true;}}})(" + JSONObject.quote(host) + ");";
        try { target.evaluateJavascript(script, null); } catch (RuntimeException ignored) {}
    }

    private String homeRenderKey(HomePageConfig value, List<HomePage.Shortcut> shortcuts) {
        StringBuilder key = new StringBuilder(512);
        key.append(searchEngine).append('|').append(searchEngines.signature()).append('|').append(nightMode).append('|')
                .append(value.title).append('|').append(value.subtitle).append('|')
                .append(value.logoStyle).append('|').append(value.logoCode).append('|')
                .append(value.logoMode).append('|').append(value.logoLetterSpacing).append('|')
                .append(value.logoGradientAngle).append('|').append(value.logoFontSize).append('|')
                .append(value.logoFontWeight).append('|').append(value.logoImageWidth).append('|')
                .append(value.logoImageHeight).append('|').append(value.logoImageRadius).append('|')
                .append(value.accent).append('|').append(value.wallpaperDim).append('|')
                .append(value.wallpaperBlur).append('|').append(value.wallpaperFit).append('|')
                .append(value.searchStyle).append('|').append(value.layout).append('|')
                .append(value.tileShape).append('|').append(value.shortcutColumns).append('|')
                .append(value.showSearch).append('|').append(value.showEngines).append('|')
                .append(value.showShortcuts).append('|').append(value.showCornerBrand).append('|')
                .append(value.showClock).append('|').append(value.customHtmlEnabled).append('|')
                .append(value.hasWallpaper).append('|').append(value.hasLogo).append('|')
                .append(value.customHtmlVersion).append('|').append(value.wallpaperVersion).append('|')
                .append(value.logoVersion).append('|').append(value.customCss.length()).append(':')
                .append(value.customCss.hashCode());
        int count = Math.min(12, shortcuts == null ? 0 : shortcuts.size());
        for (int i = 0; i < count; i++) {
            HomePage.Shortcut item = shortcuts.get(i);
            key.append('|').append(item.folder).append(':').append(item.id).append('\u001f')
                    .append(item.title).append('\u001f').append(item.url);
        }
        return key.toString();
    }

    private boolean isHomeRenderCurrent(WebView view) {
        if (view == null) return false;
        String rendered = renderedHomeKeys.get(view);
        if (rendered == null) return false;
        List<BrowserDataStore.Bookmark> bookmarks = dataStore == null
                ? Collections.<BrowserDataStore.Bookmark>emptyList() : dataStore.bookmarks();
        return rendered.equals(homeRenderKey(homePageConfig(), homeShortcuts(bookmarks)));
    }

    private void scheduleRestoredHomeRepair(final WebView target) {
        if (target == null || target != webView || activityDestroyed) return;
        Runnable repair = new Runnable() {
            @Override public void run() {
                if (activityDestroyed || webView != target || !isHomeUrl(target.getUrl())) return;
                verifyTrustedHome(target);
                if (!homeThemeRepairPending && isHomeRenderCurrent(target)) return;
                showHome(true);
            }
        };
        target.postDelayed(repair, 180L);
        target.postDelayed(repair, 520L);
    }

    private HomePageConfig homePageConfig() {
        String customHtml = prefs.getString("home_custom_html", "");
        boolean customHtmlEnabled = prefs.getBoolean("home_custom_html_enabled", false) &&
                CustomHomeHtml.valid(customHtml);
        boolean hasLogo = homeImages != null && homeImages.has(HomeImageStore.Kind.LOGO);
        String logoMode = prefs.getString("home_logo_mode", "");
        if (!"text".equals(logoMode) && !"image".equals(logoMode) && !"none".equals(logoMode))
            logoMode = hasLogo ? "image" : "text";
        return HomePageConfig.createPersonalized(
                prefs.getString("home_title", HomePageConfig.DEFAULT_TITLE),
                prefs.getString("home_subtitle", ""),
                prefs.getString("home_logo_style", "median"),
                prefs.getString("home_logo_code", ""),
                prefs.getInt("home_logo_letter_spacing", 0),
                prefs.getInt("home_logo_gradient_angle", 90),
                prefs.getString("home_accent", "blue"),
                prefs.getInt("home_wallpaper_dim", 28),
                prefs.getInt("home_wallpaper_blur", 0),
                prefs.getString("home_wallpaper_fit", "cover"),
                prefs.getString("home_search_style", "solid"),
                prefs.getString("home_layout", "center"),
                prefs.getString("home_tile_shape", "rounded"),
                prefs.getInt("home_shortcut_columns", 4),
                prefs.getBoolean("home_show_search", true),
                prefs.getBoolean("home_show_engines", true),
                prefs.getBoolean("home_show_shortcuts", true),
                prefs.getBoolean("home_show_corner", true),
                prefs.getBoolean("home_show_clock", false),
                customHtmlEnabled,
                homeImages != null && homeImages.has(HomeImageStore.Kind.WALLPAPER),
                hasLogo,
                prefs.getLong("home_custom_html_version", 0L),
                homeImages == null ? 0L : homeImages.version(HomeImageStore.Kind.WALLPAPER),
                homeImages == null ? 0L : homeImages.version(HomeImageStore.Kind.LOGO),
                logoMode,
                prefs.getInt("home_logo_font_size", 47),
                prefs.getInt("home_logo_font_weight", 720),
                prefs.getInt("home_logo_image_width", 132),
                prefs.getInt("home_logo_image_height", 96),
                prefs.getInt("home_logo_image_radius", 0),
                prefs.getString("home_custom_css", ""));
    }

    private void verifyTrustedHome(final WebView view) {
        if (view == null || activityDestroyed || tabForView(view) == null) return;
        String probe = "(function(){var m=document.querySelector('meta[name=median-home-token]');return !!m&&m.content===" +
                JSONObject.quote(homeToken()) + ";})();";
        view.evaluateJavascript(probe, new ValueCallback<String>() {
            @Override public void onReceiveValue(String value) {
                try {
                    // The renderer may finish the probe after this tab was switched, frozen,
                    // or closed. Ignore that result instead of resurrecting a stale trusted view.
                    if (activityDestroyed || tabForView(view) == null) {
                        trustedHomeViews.remove(view);
                        customHomeViews.remove(view);
                        return;
                    }
                    if ("true".equals(value) && isHomeUrl(view.getUrl())) {
                        trustedHomeViews.add(view);
                        if (homePageConfig().customHtmlEnabled) customHomeViews.add(view);
                        else customHomeViews.remove(view);
                    } else {
                        trustedHomeViews.remove(view);
                        customHomeViews.remove(view);
                    }
                } catch (RuntimeException ignored) {
                    trustedHomeViews.remove(view);
                    customHomeViews.remove(view);
                }
            }
        });
    }

    private void schedulePageEnhancements(final String url, final long sequence) {
        if (!isNetworkPage(url)) return;
        final WebView target = webView;
        final boolean ensureScripts = scriptStore != null && scriptStore.hasEnabledScripts();
        final String bridgeToken = target == null || scriptBridgeTokens.get(target) == null ? "" :
                scriptBridgeTokens.get(target);
        // Cosmetic CSS has its own document-scoped path; this worker only prepares userscripts.
        if (!ensureScripts) return;
        navigationExecutor.execute(new Runnable() {
            @Override public void run() {
                if (sequence != navigationSequence) return;
                try { Process.setThreadPriority(scriptThreadPriority()); } catch (RuntimeException ignored) {}
                StringBuilder start = new StringBuilder(4096);
                // A number of OEM providers advertise document-start support and accept a
                // registration, but occasionally fail to execute it. Every registered payload
                // sets a per-script page marker; this post-commit payload only runs missing
                // scripts, so working providers stay fast while broken providers recover.
                String startScripts = ensureScripts ? scriptStore.buildInjection(url, true, bridgeToken) : "";
                if (startScripts.length() > 0) start.append(startScripts);
                if (sequence != navigationSequence) return;
                final PreparedInjection prepared = new PreparedInjection(sequence, url, start.toString(),
                        ensureScripts ? scriptStore.buildInjection(url, false, bridgeToken) : "");
                uiHandler.post(new Runnable() {
                    @Override public void run() {
                        if (sequence != navigationSequence || webView == null) return;
                        preparedInjection = prepared;
                        if (pageCommitted) injectPreparedStart(sequence);
                        if (pageFinished) injectPreparedEnd(sequence);
                    }
                });
            }
        });
    }

    private long advanceNavigationSequence() {
        long next = ++navigationSequence;
        if (navigationExecutor != null) navigationExecutor.getQueue().clear();
        return next;
    }

    private void injectPreparedStart(long sequence) {
        PreparedInjection prepared = preparedInjection;
        if (prepared == null || prepared.sequence != sequence || injectedStartSequence == sequence) return;
        injectedStartSequence = sequence;
        if (prepared.startScript.length() > 0) executeUserScriptPayload(prepared.startScript);
    }

    private void injectPreparedEnd(final long sequence) {
        final PreparedInjection prepared = preparedInjection;
        if (prepared == null || prepared.sequence != sequence || injectedEndSequence == sequence) return;
        injectedEndSequence = sequence;
        Runnable inject = new Runnable() {
            @Override public void run() {
                if (sequence == navigationSequence && prepared.endScript.length() > 0 && webView != null) {
                    executeUserScriptPayload(prepared.endScript);
                }
                if (sequence == navigationSequence) preparedInjection = null;
            }
        };
        if (MODE_POWER_SAVE.equals(performanceMode)) uiHandler.postDelayed(inject, 160L); else inject.run();
    }

    private void executeUserScriptPayload(String payload) {
        final WebView active = webView;
        if (active == null || payload == null || payload.length() == 0) return;
        try {
            active.evaluateJavascript(payload, null);
        } catch (RuntimeException ignored) {
        }
    }

    private boolean isAdBlockActive(String url) {
        return isAdBlockActiveForHost(hostOf(url));
    }

    private boolean isAdBlockActiveForHost(String host) {
        if (!adBlockEnabled) return false;
        SiteSettingsStore.SiteSettings site = siteSettingsStore == null ? null : siteSettingsStore.forHost(host);
        if (site != null && site.compatibilityMode()) return false;
        return matchingSiteException(host) == null;
    }

    private String matchingSiteException(String host) {
        Set<String> exceptions = siteExceptions;
        if (host == null || host.length() == 0) return null;
        String candidate = host.toLowerCase(Locale.US);
        while (candidate.length() > 0) {
            if (exceptions.contains(candidate)) return candidate;
            int dot = candidate.indexOf('.');
            if (dot < 0) break;
            candidate = candidate.substring(dot + 1);
        }
        return null;
    }

    private void startAdPicker() {
        if (webView == null || !isNetworkPage(currentPageUrl) || currentHost().length() == 0) {
            toast("Veuillez d'abord ouvrir la page dont vous souhaitez marquer la publicité");
            return;
        }
        if (!validAdPickerHost(currentHost())) {
            toast("Impossible de créer une règle publicitaire propre à ce site pour l'adresse actuelle");
            return;
        }
        if (!isAdBlockActiveForHost(currentHost())) {
            toast("Veuillez d'abord activer le blocage de publicités pour ce site");
            return;
        }
        dismissOverlayForNavigation();
        final WebView source = webView;
        final AdPickerSession session = new AdPickerSession(source.getUrl());
        adPickerSessions.put(source, session);
        adPickerViews.add(source);
        try {
            source.evaluateJavascript(AdPickerScript.build(adPickToken()), new ValueCallback<String>() {
                @Override public void onReceiveValue(String result) {
                    if (adPickerSessions.get(source) != session) return;
                    if (!"true".equals(result)) {
                        finishAdPickerSession(source, session);
                        if (!"false".equals(result)) toast("Impossible d'activer le mode de marquage publicitaire sur cette page");
                    }
                }
            });
            source.performHapticFeedback(android.view.HapticFeedbackConstants.CLOCK_TICK);
        } catch (RuntimeException error) {
            finishAdPickerSession(source, session);
            toast("Impossible d'activer le mode de marquage publicitaire sur cette page");
        }
    }

    private boolean isAdPickerSessionCurrent(WebView source, AdPickerSession session) {
        return !activityDestroyed && source != null && source == webView && session != null &&
                adPickerSessions.get(source) == session &&
                session.documentUrl.equals(navigationDocumentUrl(source.getUrl()));
    }

    private void finishAdPickerSession(WebView source, AdPickerSession session) {
        if (source == null || session == null || !adPickerSessions.remove(source, session)) return;
        adPickerViews.remove(source);
        try { source.evaluateJavascript("if(window.__medianAdPicker)window.__medianAdPicker.cancel();delete window.__medianAdSelection;", null); }
        catch (RuntimeException ignored) {}
    }

    private boolean handleAdPickerPrompt(final WebView source, String message, String value,
                                         JsPromptResult result) {
        if (!adPickToken().equals(message)) return false;
        final AdPickerSession session = source == null ? null : adPickerSessions.get(source);
        boolean accepted = result != null && isAdPickerSessionCurrent(source, session) &&
                adPickerViews.remove(source) && isNetworkPage(source.getUrl());
        if (result != null) result.confirm("");
        if (!accepted) { finishAdPickerSession(source, session); return true; }
        try {
            JSONObject picked = new JSONObject(value == null ? "{}" : value);
            if (picked.optBoolean("cancel", false)) { finishAdPickerSession(source, session); return true; }
            final String selector = picked.optString("selector", "").trim();
            final String label = picked.optString("text", "").trim();
            final String host = hostOf(source.getUrl());
            if (!validAdPickerHost(host)) {
                toast("Impossible de générer une règle stable pour cet élément");
                finishAdPickerSession(source, session);
                return true;
            }
            if (picked.optBoolean("manual", false)) {
                showManualAdPickerDialog(source, host, session);
                return true;
            }
            if (selector.length() == 0 || selector.length() > 512 ||
                    selector.indexOf('\n') >= 0 || selector.indexOf('\r') >= 0) {
                toast("Impossible de générer une règle stable pour cet élément");
                finishAdPickerSession(source, session);
                return true;
            }
            validateAdPickerSelector(source, host, selector, label, true, session);
        } catch (Exception error) {
            finishAdPickerSession(source, session);
            toast("Impossible de lire le résultat du marquage publicitaire");
        }
        return true;
    }

    private void showManualAdPickerDialog(final WebView source, final String host, final AdPickerSession session) {
        if (!isAdPickerSessionCurrent(source, session)) { finishAdPickerSession(source, session); return; }
        final boolean[] advancing = { false };
        final EditText input = new EditText(this);
        input.setSingleLine(true);
        input.setTextSize(15f);
        input.setHint("Exemple : .ad-banner ou #sponsor");
        input.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_FLAG_NO_SUGGESTIONS);
        input.setPadding(dp(14), dp(10), dp(14), dp(10));
        input.setTextColor(nightMode ? DARK_TEXT : TEXT);
        input.setHintTextColor(nightMode ? DARK_MUTED : MUTED);
        input.setBackground(roundRect(nightMode ? DARK_SURFACE : SURFACE, 10));
        final AlertDialog dialog = new AlertDialog.Builder(this,
                nightMode ? R.style.MedianAlertDialogDark : R.style.MedianAlertDialogLight)
                .setTitle("Saisir manuellement un sélecteur CSS")
                .setMessage("Utile pour les pages où le sélecteur ne peut pas être généré automatiquement. Vérifiez d'abord le nombre de correspondances, puis enregistrez la règle pour ce site.")
                .setView(input)
                .setPositiveButton("Vérifier et continuer", null)
                .setNegativeButton("Annuler", null)
                .create();
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) {
                        String selector = input.getText().toString().trim();
                        if (selector.length() == 0 || selector.length() > 512 ||
                                selector.indexOf('\n') >= 0 || selector.indexOf('\r') >= 0) {
                            input.setError("Veuillez saisir un sélecteur CSS d'une ligne de 1 à 512 caractères");
                            return;
                        }
                        advancing[0] = true;
                        dialog.dismiss();
                        validateAdPickerSelector(source, host, selector, "Sélecteur manuel", false, session);
                    }
                });
            }
        });
        dialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
            @Override public void onDismiss(DialogInterface ignored) {
                if (!advancing[0]) finishAdPickerSession(source, session);
            }
        });
        dialog.show();
    }

    private void validateAdPickerSelector(final WebView source, final String host,
                                          final String selector, final String label,
                                          final boolean requirePickedIdentity, final AdPickerSession session) {
        if (!isAdPickerSessionCurrent(source, session)) { finishAdPickerSession(source, session); return; }
        try {
            source.evaluateJavascript(AdPickerScript.validate(selector, requirePickedIdentity), new ValueCallback<String>() {
                @Override public void onReceiveValue(String rawCount) {
                    if (!isAdPickerSessionCurrent(source, session)) { finishAdPickerSession(source, session); return; }
                    int count = parseJavascriptInt(rawCount);
                    if (count < 1) {
                        finishAdPickerSession(source, session);
                        toast(count < 0 ? "Sélecteur CSS invalide, veuillez réessayer" :
                                (requirePickedIdentity ? "L'élément de la page a changé, veuillez sélectionner à nouveau" : "Aucun élément correspondant ou plus de 200 correspondances ; veuillez saisir une règle plus précise"));
                        return;
                    }
                    // A broad manual selector is useful, but cap it so an accidental `div` or
                    // `*` cannot turn one tap into a page-wide blank screen.
                    if (count > 200) {
                        finishAdPickerSession(source, session);
                        toast("Le sélecteur correspond à " + count + " élément(s). Veuillez saisir une règle plus précise.");
                        return;
                    }
                    confirmAdPickerRule(source, host, selector, label, count, requirePickedIdentity, session);
                }
            });
        } catch (RuntimeException error) {
            finishAdPickerSession(source, session);
            toast("Impossible de vérifier ce sélecteur sur la page actuelle");
        }
    }

    private static int parseJavascriptInt(String raw) {
        if (raw == null) return -1;
        try { return Integer.parseInt(raw.trim()); }
        catch (NumberFormatException ignored) { return -1; }
    }

    private boolean validAdPickerHost(String host) {
        if (host == null || host.length() == 0 || host.length() > 253 ||
                "median.invalid".equalsIgnoreCase(host)) return false;
        for (int i = 0; i < host.length(); i++) {
            char c = host.charAt(i);
            if (!(Character.isLetterOrDigit(c) || c == '.' || c == '-' || c == '_' || c == ':')) return false;
        }
        return true;
    }

    private void confirmAdPickerRule(final WebView source, final String host, final String selector,
                                     String label, int matchCount, final boolean requirePickedIdentity,
                                     final AdPickerSession session) {
        String preview = label.length() == 0 ? "Élément de page sélectionné" : label;
        preview = UiText.ellipsize(preview, 80);
        final boolean[] saving = { false };
        AlertDialog confirmation = new AlertDialog.Builder(this,
                nightMode ? R.style.MedianAlertDialogDark : R.style.MedianAlertDialogLight)
                .setTitle("Marquer cet élément comme publicité ?")
                .setMessage(preview + "\n\nRègle : " + host + "##" + selector +
                        "\n\nCorrespondances actuelles : " + matchCount + " élément(s). La règle ne s'applique qu'à ce site et peut être modifiée dans le centre de filtres.")
                .setPositiveButton("Marquer et masquer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        if (!isAdPickerSessionCurrent(source, session)) {
                            toast("La page a changé, veuillez sélectionner à nouveau l'élément publicitaire");
                            finishAdPickerSession(source, session);
                            return;
                        }
                        saving[0] = true;
                        try {
                            source.evaluateJavascript(AdPickerScript.hide(selector, requirePickedIdentity), new ValueCallback<String>() {
                                @Override public void onReceiveValue(String rawCount) {
                                    boolean current = isAdPickerSessionCurrent(source, session);
                                    finishAdPickerSession(source, session);
                                    if (!current) return;
                                    int hidden = parseJavascriptInt(rawCount);
                                    if (hidden < 1 || hidden > 200) {
                                        toast("L'élément de la page a changé, veuillez sélectionner à nouveau l'élément publicitaire");
                                        return;
                                    }
                                    if (!appendCustomFilterRule(host + "##" + selector)) {
                                        toast("L'élément est masqué, mais la règle n'a pas été enregistrée ; veuillez réduire les règles personnalisées et réessayer");
                                        return;
                                    }
                                    rebuildAdBlockRulesAsync(false);
                                    toast("Masqué(s) : " + hidden + " élément(s) masqués, règle de ce site enregistrée");
                                }
                            });
                        } catch (RuntimeException error) {
                            finishAdPickerSession(source, session);
                            toast("Impossible d'appliquer le masquage sur cette page, veuillez sélectionner à nouveau");
                        }
                    }
                })
                .setNegativeButton("Annuler", null)
                .create();
        confirmation.setOnDismissListener(new DialogInterface.OnDismissListener() {
            @Override public void onDismiss(DialogInterface ignored) {
                if (!saving[0]) finishAdPickerSession(source, session);
            }
        });
        confirmation.show();
    }

    private boolean appendCustomFilterRule(String rule) {
        String raw = prefs.getString("custom_filter_rules", "");
        String[] lines = raw.split("\\r?\\n");
        for (String line : lines) {
            if (rule.equals(line.trim())) {
                return true;
            }
        }
        String next = raw.trim().length() == 0 ? rule : raw.replaceFirst("\\s+$", "") + "\n" + rule;
        if (next.getBytes(StandardCharsets.UTF_8).length > 256 * 1024) {
            toast("Les règles personnalisées ont atteint la limite de 256 Ko");
            return false;
        }
        prefs.edit().putString("custom_filter_rules", next).apply();
        return true;
    }

    private void showProtectionPanel() {
        showProtectionPanel(null);
    }

    private void showProtectionPanel(final Runnable backAction) {
        if (!requireStartupReady()) return;
        final String host = currentHost();
        final String matchedException = matchingSiteException(host);
        final boolean sitePaused = host.length() > 0 && matchedException != null;
        final boolean blockingActive = adBlockEnabled;
        int pageBlocked = Math.max(0, adBlock.getBlockedCount() - blockedAtPageStart);
        String subtitle = host.length() == 0 ? "Page d'accueil actuelle" : host + (blockingActive ? " · bloqués sur cette page : " + pageBlocked + " élément(s)" : " · le blocage de publicités est désactivé");
        String[] items = new String[] {
                "Blocage de publicités global : " + (adBlockEnabled ? "Activé" : "Désactivé"),
                host.length() == 0 ? "Aucun paramètre de site pour la page actuelle" : (!blockingActive ? "Blocage pour ce site : le blocage global est désactivé" : (sitePaused ? "Réactiver le blocage pour ce site" : "Suspendre le blocage pour ce site")),
                host.length() == 0 ? "Impossible de marquer la publicité sur cette page\nVeuillez d'abord ouvrir une page web normale" :
                        "Marquer la publicité de la page\nTouchez un élément pour générer une règle de masquage propre à ce site",
                "Centre de filtres · " + services.filters().enabledCount() + " abonnements" + (blockingActive ? "" : "(hors blocage)"),
                "Scripts utilisateur · Activés : " + enabledScriptCount() + "",
                "Parcourir les scripts pour le site actuel",
                "Règles de blocage personnalisées"
        };
        int[] icons = new int[] { BrowserIconView.SHIELD, BrowserIconView.SHIELD,
                BrowserIconView.CLEAN, BrowserIconView.STORAGE, BrowserIconView.SCRIPT,
                BrowserIconView.SEARCH, BrowserIconView.STORAGE };
        int[] kinds = new int[] {
                adBlockEnabled ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                host.length() == 0 || !blockingActive ? SHEET_ROW_ACTION :
                        (sitePaused ? SHEET_ROW_TOGGLE_OFF : SHEET_ROW_TOGGLE_ON),
                SHEET_ROW_ACTION, SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE,
                SHEET_ROW_ACTION, SHEET_ROW_NAVIGATE
        };
        showActionSheet("Protection et scripts", subtitle, items, icons, kinds, null, backAction, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) {
                    adBlockEnabled = !adBlockEnabled;
                    prefs.edit().putBoolean("adblock", adBlockEnabled).apply();
                    adBlockActiveByView.clear();
                    dismissOverlayForNavigation();
                    if (webView != null && isNetworkPage(currentPageUrl)) reloadWebView(webView);
                    showProtectionPanel(backAction);
                } else if (which == 1 && host.length() > 0 && blockingActive) {
                    HashSet<String> updated = new HashSet<String>(siteExceptions);
                    if (matchedException != null) updated.remove(matchedException); else updated.add(host);
                    siteExceptions = updated;
                    prefs.edit().putStringSet("site_exceptions", new HashSet<String>(updated)).apply();
                    adBlockActiveByView.clear();
                    dismissOverlayForNavigation();
                    if (webView != null && isNetworkPage(currentPageUrl)) reloadWebView(webView);
                    showProtectionPanel(backAction);
                } else if (which == 1) {
                    toast(host.length() == 0 ? "Ouvrez d'abord une page web pour configurer une exception de site" : "Veuillez d'abord activer le blocage de publicités global");
                    showProtectionPanel(backAction);
                } else if (which == 2) {
                    if (host.length() == 0) {
                        toast("Veuillez d'abord ouvrir une page web normale avant de marquer la publicité");
                        showProtectionPanel(backAction);
                    } else startAdPicker();
                } else if (which == 3) {
                    showFilterCenter(new Runnable() {
                        @Override public void run() { showProtectionPanel(backAction); }
                    });
                } else if (which == 4) {
                    showScriptCenter(new Runnable() {
                        @Override public void run() { showProtectionPanel(backAction); }
                    });
                } else if (which == 5) {
                    String target = host.length() == 0 ? "https://greasyfork.org/zh-CN/scripts" : "https://greasyfork.org/zh-CN/scripts/by-site/" + host;
                    loadNetworkUrl(webView, target);
                } else if (which == 6) {
                    showCustomFilterRules(new Runnable() {
                        @Override public void run() { showProtectionPanel(backAction); }
                    });
                }
            }
        });
    }

    private void rebuildAdBlockRulesAsync(final boolean notifyUser) {
        if (!activityDestroyed) adBlockRuleLoader.request(!startupReady, notifyUser);
    }

    /** Rule loader dispatches only current-generation results on the UI thread. */
    private void onAdBlockRulesLoaded(final boolean notifyUser) {
        if (!startupCustomRulesReady) {
            startupCustomRulesReady = true;
            startupReadiness.set(StartupReadiness.FILTERS, true);
            maybeStartFastStartup();
            maybeCompleteStartup();
        }
        refreshCosmeticFilters();
        if (notifyUser) {
            AdBlockEngine.Stats stats = adBlock.getStats();
            toast("Filtres compilés : " + stats.networkRules + " règles réseau, " + stats.cosmeticRules + " règles cosmétiques");
            if (webView != null) reloadWebView(webView);
        }
    }

    private void onAdBlockRulesLoadFailed() {
        // Keep the last published rules and release the startup gate on an explicit failure.
        startupCustomRulesReady = true;
        startupReadiness.set(StartupReadiness.FILTERS, true);
        toast("Les règles de filtrage locales n'ont pas pu être chargées ; la protection existante est conservée, veuillez réessayer plus tard");
        maybeStartFastStartup();
        maybeCompleteStartup();
    }

    private void updateFilterSubscriptions(final boolean automatic) {
        if (filterUpdateInProgress) {
            if (!automatic) toast("La mise à jour des abonnements de filtres est déjà en cours, inutile de la relancer");
            return;
        }
        filterUpdateInProgress = true;
        if (!automatic) toast("Mise à jour des abonnements de filtres…");
        services.filters().updateEnabled(automatic, new FilterSubscriptionStore.Callback() {
            @Override public void onComplete(int updated, int unchanged, int failed, String message) {
                filterUpdateInProgress = false;
                if (updated > 0) rebuildAdBlockRulesAsync(false);
                if (!automatic) {
                    String result = "Mise à jour des abonnements terminée : " + updated + " mis à jour, " + unchanged + " inchangé(s)";
                    if (failed > 0) result += "，" + failed + " en échec" + (message.length() == 0 ? "" : "（" + message + "）");
                    if (updated > 0) result += " ; règles cosmétiques mises à jour";
                    toast(result);
                }
            }
        });
    }

    private void showFilterCenter() {
        showFilterCenter(filterCenterBackAction);
    }

    private void showFilterCenter(final Runnable backAction) {
        filterCenterBackAction = backAction;
        final List<FilterSubscriptionStore.Subscription> subscriptions = services.filters().getAll();
        final AdBlockEngine.Stats stats = adBlock.getStats();
        String[] items = new String[subscriptions.size() + 4];
        int[] icons = new int[items.length];
        items[0] = filterUpdateInProgress ? "Mise à jour des abonnements de filtres en cours" : "Mettre à jour tous les abonnements activés maintenant";
        items[1] = "Ajouter un abonnement de filtres HTTPS";
        items[2] = "Modifier les règles personnalisées";
        for (int i = 0; i < subscriptions.size(); i++) {
            FilterSubscriptionStore.Subscription item = subscriptions.get(i);
            String state = item.enabled ? "Activé" : "Désactivé";
            String count = item.ruleCount > 0 ? " · " + item.ruleCount + " lignes" : " · pas encore téléchargé";
            items[i + 3] = item.name + "：" + state + count + (item.error.length() == 0 ? "" : " · échec précédent");
        }
        items[items.length - 1] = "Diagnostic des filtres · " + stats.networkRules + " règles réseau / " + stats.cosmeticRules + " règles cosmétiques";
        for (int i = 0; i < icons.length; i++) icons[i] = i == 1 ? BrowserIconView.PLUS : (i == items.length - 1 ? BrowserIconView.INFO : BrowserIconView.SHIELD);
        showActionSheet("Centre de filtres", "Abonnements HTTPS et règles locales",
                items, icons, null, null, backAction, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) {
                    updateFilterSubscriptions(false);
                    showFilterCenter();
                }
                else if (which == 1) showAddFilterSubscription();
                else if (which == 2) showCustomFilterRules();
                else if (which == subscriptions.size() + 3) showFilterDiagnostics();
                else {
                    int index = which - 3;
                    if (index >= 0 && index < subscriptions.size()) showFilterSubscriptionActions(subscriptions.get(index));
                }
            }
        });
    }

    private void showFilterSubscriptionActions(final FilterSubscriptionStore.Subscription item) {
        boolean custom = item.id.startsWith("custom-");
        String[] actions = custom
                ? new String[] { item.enabled ? "Désactiver cet abonnement" : "Activer cet abonnement", "Mettre à jour tous les abonnements activés maintenant", "Supprimer cet abonnement" }
                : new String[] { item.enabled ? "Désactiver cet abonnement" : "Activer cet abonnement", "Mettre à jour tous les abonnements activés maintenant" };
        int[] icons = custom
                ? new int[] { BrowserIconView.SHIELD, BrowserIconView.RELOAD, BrowserIconView.CLOSE }
                : new int[] { BrowserIconView.SHIELD, BrowserIconView.RELOAD };
        int[] kinds = custom
                ? new int[] { item.enabled ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                        SHEET_ROW_ACTION, SHEET_ROW_ACTION }
                : new int[] { item.enabled ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                        SHEET_ROW_ACTION };
        String subtitle = item.url + (item.error.length() == 0 ? "" : "\nDernière erreur : " + item.error);
        showActionSheet(item.name, subtitle, actions, icons, kinds, null,
                new Runnable() { @Override public void run() { showFilterCenter(); } }, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) {
                    dismissOverlayForNavigation();
                    services.filters().setEnabled(item.id, !item.enabled);
                    rebuildAdBlockRulesAsync(true);
                    showFilterCenter();
                } else if (which == 1) {
                    updateFilterSubscriptions(false);
                    showFilterCenter();
                } else {
                    confirmDeleteFilterSubscription(item);
                }
            }
        });
    }

    private void confirmDeleteFilterSubscription(final FilterSubscriptionStore.Subscription item) {
        final SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
            @Override public void run() { showFilterSubscriptionActions(item); }
        });
        new AlertDialog.Builder(this).setTitle("Supprimer l'abonnement de filtres ?")
                .setMessage(item.name + "\n" + item.url)
                .setPositiveButton("Supprimer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        services.filters().remove(item.id);
                        rebuildAdBlockRulesAsync(true);
                        showFilterCenter();
                    }
                }).setNegativeButton("Annuler", back).setOnCancelListener(back).show();
    }

    private void showAddFilterSubscription() {
        final EditText name = new EditText(this);
        name.setHint("Nom (facultatif)");
        name.setSingleLine(true);
        final EditText url = new EditText(this);
        url.setHint("https://example.com/filter.txt");
        url.setSingleLine(true);
        url.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_URI);
        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);
        content.setPadding(dp(18), 0, dp(18), 0);
        content.addView(name);
        content.addView(url);
        final AlertDialog dialog = new AlertDialog.Builder(this).setTitle("Ajouter un abonnement de filtres")
                .setMessage("Seules les règles texte HTTPS sont acceptées, 12 Mo maximum par abonnement.")
                .setView(content).setPositiveButton("Ajouter et mettre à jour", null)
                .setNegativeButton("Annuler", null).create();
        dialog.setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface ignored) { showFilterCenter(); }
        });
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_NEGATIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) { dialog.dismiss(); showFilterCenter(); }
                });
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) {
                        try {
                            services.filters().add(name.getText().toString(), url.getText().toString().trim());
                            dialog.dismiss();
                            showFilterCenter();
                            updateFilterSubscriptions(false);
                        } catch (Exception e) { url.setError(safeMessage(e)); }
                    }
                });
            }
        });
        dialog.show();
    }

    private void showFilterDiagnostics() {
        AdBlockEngine.Stats stats = adBlock.getStats();
        SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
            @Override public void run() { showFilterCenter(); }
        });
        new AlertDialog.Builder(this).setTitle("Diagnostic des filtres")
                .setMessage("Règles réseau compilées : " + stats.networkRules +
                        "\nRègles cosmétiques compilées : " + stats.cosmeticRules +
                        "\nLignes sources lues : " + stats.sourceLines +
                        "\nÉtat des capacités : " + (stats.capacityLimited ? "Certaines règles n'ont pas été chargées en raison des limites de sécurité" : "Tout est dans les limites de sécurité") +
                        "\nRequêtes inspectées (session) : " + stats.inspectedRequests +
                        "\nRequêtes bloquées : " + stats.blockedRequests +
                        "\nRequêtes autorisées par exception : " + stats.allowedRequests +
                        "\n\nPrend en charge les fichiers hosts, les règles réseau ABP et les règles cosmétiques ## / #@# ; les scripts contenus dans les listes ne sont pas exécutés.")
                .setPositiveButton("OK", back).setOnCancelListener(back).show();
    }

    private void showCustomFilterRules() {
        showCustomFilterRules(new Runnable() {
            @Override public void run() { showFilterCenter(); }
        });
    }

    private void showCustomFilterRules(final Runnable returnAction) {
        final EditText input = new EditText(this);
        input.setText(prefs.getString("custom_filter_rules", ""));
        input.setHint("Une règle par ligne, par exemple :
||ads.example.com^
@@||trusted.example.com^");
        input.setGravity(Gravity.TOP | Gravity.START);
        input.setMinLines(8);
        input.setMaxLines(14);
        input.setHorizontallyScrolling(false);
        input.setPadding(dp(14), dp(10), dp(14), dp(10));
        final AlertDialog dialog = new AlertDialog.Builder(this).setTitle("Règles de blocage personnalisées")
                .setMessage("Prend en charge les fichiers hosts, les règles réseau et cosmétiques ABP, jusqu'à 256 Ko.")
                .setView(input).setPositiveButton("Enregistrer", null)
                .setNegativeButton("Annuler", null).create();
        dialog.setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface ignored) { continueSettingsPanel(returnAction); }
        });
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_NEGATIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) { dialog.dismiss(); continueSettingsPanel(returnAction); }
                });
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) {
                        String raw = input.getText().toString();
                        if (raw.getBytes(StandardCharsets.UTF_8).length > 256 * 1024) {
                            input.setError("Les règles ne peuvent pas dépasser 256 Ko");
                            return;
                        }
                        prefs.edit().putString("custom_filter_rules", raw).apply();
                        dialog.dismiss();
                        rebuildAdBlockRulesAsync(true);
                        continueSettingsPanel(returnAction);
                    }
                });
            }
        });
        dialog.show();
    }

    /** A compact icon dashboard for the browser menu and settings root. */
    private void showDashboardSheet(String title, String subtitle, String[] items, int[] icons,
                                   int[] rowKinds, int columns, int[] sectionStarts,
                                   String[] sectionTitles, final Runnable backAction,
                                   final Runnable footerAction, String footerText, int footerIcon,
                                   final SheetHandler handler) {
        dismissOverlayForNavigation();
        final int sheetSurface = nightMode ? DARK_SHEET : WHITE;
        final int sheetText = nightMode ? DARK_TEXT : TEXT;
        final int sheetMuted = nightMode ? DARK_MUTED : MUTED;
        final int tileSurface = nightMode ? DARK_CARD : SURFACE;
        final FrameLayout overlay = new FrameLayout(this);
        overlay.setBackgroundColor(Color.argb(104, 0, 0, 0));
        overlay.setClickable(true);
        overlay.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View view) { dismissOverlay(); }
        });

        LinearLayout panel = new LinearLayout(this);
        panel.setTag(SHEET_TAG_SURFACE);
        panel.setOrientation(LinearLayout.VERTICAL);
        panel.setBackground(roundRect(sheetSurface, 20));
        panel.setPadding(dp(10), dp(7), dp(10), dp(10));
        panel.setClickable(true);
        panel.setElevation(dp(12));

        View handle = new View(this);
        handle.setTag(SHEET_TAG_HANDLE);
        handle.setBackground(sheetHandleDrawable());
        LinearLayout.LayoutParams handleParams = new LinearLayout.LayoutParams(dp(48), dp(30));
        handleParams.gravity = Gravity.CENTER_HORIZONTAL;
        panel.addView(handle, handleParams);
        handle.setContentDescription("Faites glisser vers le bas pour fermer");
        installSheetDrag(handle, panel);

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.CENTER_VERTICAL);
        if (backAction != null) {
            BrowserIconView back = iconButton(BrowserIconView.BACK, "Retour au niveau précédent");
            back.setTintColor(sheetText);
            header.addView(back, new LinearLayout.LayoutParams(dp(44), dp(48)));
            back.setOnClickListener(new View.OnClickListener() {
                @Override public void onClick(View view) { navigateOverlayBack(); }
            });
        }
        LinearLayout titles = new LinearLayout(this);
        titles.setOrientation(LinearLayout.VERTICAL);
        TextView heading = new TextView(this);
        heading.setTag(SHEET_TAG_PRIMARY);
        heading.setText(title);
        heading.setTextColor(sheetText);
        heading.setTextSize(18f);
        heading.setTypeface(android.graphics.Typeface.DEFAULT_BOLD);
        titles.addView(heading);
        if (subtitle != null && subtitle.length() > 0) {
            TextView sub = new TextView(this);
            sub.setTag(SHEET_TAG_MUTED);
            sub.setText(subtitle);
            sub.setTextColor(sheetMuted);
            sub.setTextSize(12f);
            sub.setSingleLine(true);
            sub.setEllipsize(android.text.TextUtils.TruncateAt.END);
            sub.setPadding(0, dp(2), 0, 0);
            titles.addView(sub);
        }
        header.addView(titles, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
        BrowserIconView close = iconButton(BrowserIconView.CLOSE, "Fermer");
        close.setTintColor(sheetText);
        header.addView(close, new LinearLayout.LayoutParams(dp(44), dp(48)));
        panel.addView(header, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));
        installSheetDrag(header, panel);

        ScrollView scroll = new ScrollView(this);
        scroll.setTag(SHEET_TAG_PLAIN_SURFACE);
        scroll.setFillViewport(false);
        scroll.setVerticalScrollBarEnabled(true);
        scroll.setScrollbarFadingEnabled(false);
        scroll.setBackgroundColor(sheetSurface);
        LinearLayout content = new LinearLayout(this);
        content.setTag(SHEET_TAG_PLAIN_SURFACE);
        content.setOrientation(LinearLayout.VERTICAL);
        content.setPadding(dp(1), dp(5), dp(1), dp(2));
        content.setBackgroundColor(sheetSurface);
        scroll.addView(content);

        final float extraFontScale = Math.max(0f, getResources().getConfiguration().fontScale - 1f);
        final int tileHeightDp = Math.round((columns == 2 ? 82 : 98) + extraFontScale * 44);
        final int sectionHeightDp = Math.round(27 + extraFontScale * 16);
        int contentHeightDp = 0;
        LinearLayout row = null;
        int itemsInRow = 0;
        int sectionIndex = 0;
        for (int i = 0; i < items.length; i++) {
            boolean startsSection = sectionStarts != null && sectionIndex < sectionStarts.length &&
                    i == sectionStarts[sectionIndex];
            if (startsSection) {
                if (row != null && itemsInRow > 0) {
                    while (itemsInRow < columns) {
                        row.addView(new View(this), new LinearLayout.LayoutParams(0, dp(tileHeightDp), 1f));
                        itemsInRow++;
                    }
                    content.addView(row, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                            dp(tileHeightDp)));
                    contentHeightDp += tileHeightDp;
                    row = null;
                    itemsInRow = 0;
                }
                String section = sectionTitles != null && sectionIndex < sectionTitles.length
                        ? sectionTitles[sectionIndex] : "";
                sectionIndex++;
                TextView label = new TextView(this);
                label.setTag(SHEET_TAG_ACCENT);
                label.setText(section);
                label.setTextColor(nightMode ? DARK_ACCENT : BLUE);
                label.setTextSize(12f);
                label.setTypeface(android.graphics.Typeface.DEFAULT_BOLD);
                label.setGravity(Gravity.CENTER_VERTICAL);
                label.setPadding(dp(5), dp(5), dp(5), dp(2));
                content.addView(label, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(sectionHeightDp)));
                contentHeightDp += sectionHeightDp;
            }

            if (row == null) {
                row = new LinearLayout(this);
                row.setOrientation(LinearLayout.HORIZONTAL);
                row.setGravity(Gravity.CENTER_VERTICAL);
            }
            final int index = i;
            String item = items[i] == null ? "" : items[i];
            int detailBreak = item.indexOf('\n');
            String primary = detailBreak < 0 ? item : item.substring(0, detailBreak);
            String detail = detailBreak < 0 ? "" : item.substring(detailBreak + 1).trim();
            int kind = rowKinds != null && i < rowKinds.length ? rowKinds[i] : SHEET_ROW_NAVIGATE;
            boolean toggle = kind == SHEET_ROW_TOGGLE_ON || kind == SHEET_ROW_TOGGLE_OFF;
            boolean checked = kind == SHEET_ROW_TOGGLE_ON;

            LinearLayout tile = new LinearLayout(this);
            tile.setOrientation(columns == 2 ? LinearLayout.HORIZONTAL : LinearLayout.VERTICAL);
            tile.setGravity(columns == 2 ? Gravity.CENTER_VERTICAL : Gravity.CENTER);
            tile.setPadding(columns == 2 ? dp(10) : dp(5), dp(7), columns == 2 ? dp(8) : dp(5), dp(7));
            int tileColor = toggle && checked ? (nightMode ? 0xff203654 : 0xffe8f0fe) : tileSurface;
            tile.setBackground(roundRect(tileColor, 15));
            tile.setForeground(new android.graphics.drawable.RippleDrawable(
                    ColorStateList.valueOf(nightMode ? 0x356b9bea : 0x2e1a73e8),
                    null, roundRect(Color.WHITE, 15)));
            tile.setClickable(true);
            tile.setFocusable(true);
            tile.setMinimumWidth(dp(48));
            tile.setMinimumHeight(dp(48));
            boolean detailShowsState = detail.contains("Activé") || detail.contains("Désactivé");
            tile.setContentDescription(primary + (detail.length() == 0 ? "" : "，" + detail) +
                    (toggle && !detailShowsState ? (checked ? ", activé" : ", désactivé") : ""));

            BrowserIconView icon = iconButton(icons != null && i < icons.length
                    ? icons[i] : BrowserIconView.MENU, primary);
            icon.setClickable(false);
            icon.setFocusable(false);
            if (toggle && checked) icon.setTag(SHEET_TAG_ACCENT);
            icon.setTintColor(toggle && checked ? (nightMode ? DARK_ACCENT : BLUE) : sheetText);
            LinearLayout.LayoutParams iconParams = columns == 2
                    ? new LinearLayout.LayoutParams(dp(32), dp(32))
                    : new LinearLayout.LayoutParams(dp(29), dp(29));
            if (columns == 3) iconParams.gravity = Gravity.CENTER_HORIZONTAL;
            if (columns != 2 || !toggle) tile.addView(icon, iconParams);

            LinearLayout labels = new LinearLayout(this);
            labels.setOrientation(LinearLayout.VERTICAL);
            labels.setGravity(columns == 2 ? Gravity.CENTER_VERTICAL : Gravity.CENTER_HORIZONTAL);
            labels.setPadding(columns == 2 && !toggle ? dp(9) : 0, 0, 0, 0);
            LinearLayout.LayoutParams labelsParams = columns == 2
                    ? new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
                    : new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                            ViewGroup.LayoutParams.WRAP_CONTENT);
            if (columns == 3) labelsParams.topMargin = dp(5);

            TextView label = new TextView(this);
            label.setTag(SHEET_TAG_PRIMARY);
            label.setText(primary);
            label.setTextColor(sheetText);
            label.setTextSize(columns == 2 ? 13.5f : 12.5f);
            label.setTypeface(android.graphics.Typeface.DEFAULT, android.graphics.Typeface.BOLD);
            label.setGravity(columns == 2 ? Gravity.START : Gravity.CENTER);
            label.setMaxLines(2);
            label.setEllipsize(android.text.TextUtils.TruncateAt.END);
            labels.addView(label, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT));
            if (detail.length() > 0) {
                TextView detailLabel = new TextView(this);
                detailLabel.setTag(SHEET_TAG_MUTED);
                detailLabel.setText(detail);
                detailLabel.setTextColor(sheetMuted);
                detailLabel.setTextSize(columns == 2 ? 11.5f : 10.5f);
                detailLabel.setGravity(columns == 2 ? Gravity.START : Gravity.CENTER);
                detailLabel.setSingleLine(true);
                detailLabel.setEllipsize(android.text.TextUtils.TruncateAt.END);
                detailLabel.setPadding(0, dp(2), 0, 0);
                labels.addView(detailLabel, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                        ViewGroup.LayoutParams.WRAP_CONTENT));
            } else if (toggle) {
                TextView state = new TextView(this);
                state.setTag(SHEET_TAG_MUTED);
                state.setText(checked ? "Activé" : "Désactivé");
                state.setTextColor(sheetMuted);
                state.setTextSize(10.5f);
                state.setGravity(columns == 2 ? Gravity.START : Gravity.CENTER);
                state.setPadding(0, dp(2), 0, 0);
                labels.addView(state, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                        ViewGroup.LayoutParams.WRAP_CONTENT));
            }
            tile.addView(labels, labelsParams);
            if (toggle && columns == 2) {
                Switch stateSwitch = new Switch(this);
                stateSwitch.setChecked(checked);
                stateSwitch.setShowText(false);
                stateSwitch.setClickable(false);
                stateSwitch.setFocusable(false);
                stateSwitch.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
                stateSwitch.setMinimumWidth(0);
                int[][] states = new int[][] {
                        new int[] { android.R.attr.state_checked }, new int[] {}
                };
                stateSwitch.setThumbTintList(new ColorStateList(states, new int[] {
                        nightMode ? DARK_ACCENT : BLUE,
                        nightMode ? 0xffbdc1c6 : 0xff757575
                }));
                stateSwitch.setTrackTintList(new ColorStateList(states, new int[] {
                        nightMode ? 0x796b9bea : 0x761a73e8,
                        nightMode ? 0xff505459 : 0xffbdc1c6
                }));
                tile.addView(stateSwitch, new LinearLayout.LayoutParams(dp(54), dp(48)));
            }
            tile.setOnClickListener(new View.OnClickListener() {
                @Override public void onClick(View view) {
                    dismissOverlayForNavigation();
                    handler.onItem(index);
                }
            });

            LinearLayout.LayoutParams tileParams = new LinearLayout.LayoutParams(0, dp(tileHeightDp - 6), 1f);
            int horizontalGap = dp(columns == 2 ? 5 : 4);
            tileParams.setMargins(horizontalGap, dp(3), horizontalGap, dp(3));
            row.addView(tile, tileParams);
            itemsInRow++;
            if (itemsInRow == columns || i == items.length - 1) {
                while (itemsInRow < columns) {
                    row.addView(new View(this), new LinearLayout.LayoutParams(0, dp(tileHeightDp), 1f));
                    itemsInRow++;
                }
                content.addView(row, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                        dp(tileHeightDp)));
                contentHeightDp += tileHeightDp;
                row = null;
                itemsInRow = 0;
            }
        }
        panel.addView(scroll, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f));

        if (footerAction != null) {
            LinearLayout footer = new LinearLayout(this);
            footer.setOrientation(LinearLayout.HORIZONTAL);
            footer.setGravity(Gravity.CENTER_VERTICAL);
            footer.setPadding(dp(12), 0, dp(12), 0);
            footer.setBackground(roundRect(nightMode ? 0xff203654 : 0xffe8f0fe, 14));
            footer.setForeground(new android.graphics.drawable.RippleDrawable(
                    ColorStateList.valueOf(nightMode ? 0x356b9bea : 0x2e1a73e8),
                    null, roundRect(Color.WHITE, 14)));
            footer.setClickable(true);
            footer.setFocusable(true);
            footer.setMinimumHeight(dp(50));
            footer.setContentDescription(footerText);
            BrowserIconView footerImage = iconButton(footerIcon, footerText);
            footerImage.setTag(SHEET_TAG_ACCENT);
            footerImage.setClickable(false);
            footerImage.setFocusable(false);
            footerImage.setTintColor(nightMode ? DARK_ACCENT : BLUE);
            footer.addView(footerImage, new LinearLayout.LayoutParams(dp(30), dp(30)));
            TextView footerLabel = new TextView(this);
            footerLabel.setTag(SHEET_TAG_PRIMARY);
            footerLabel.setText(footerText);
            footerLabel.setTextColor(sheetText);
            footerLabel.setTextSize(14f);
            footerLabel.setTypeface(android.graphics.Typeface.DEFAULT, android.graphics.Typeface.BOLD);
            footerLabel.setPadding(dp(10), 0, 0, 0);
            footer.addView(footerLabel, new LinearLayout.LayoutParams(0,
                    ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
            TextView chevron = new TextView(this);
            chevron.setTag(SHEET_TAG_MUTED);
            chevron.setText("›");
            chevron.setTextColor(sheetMuted);
            chevron.setTextSize(27f);
            footer.addView(chevron);
            LinearLayout.LayoutParams footerParams = new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, dp(50));
            footerParams.setMargins(dp(4), dp(7), dp(4), 0);
            panel.addView(footer, footerParams);
            footer.setOnClickListener(new View.OnClickListener() {
                @Override public void onClick(View view) {
                    dismissOverlayForNavigation();
                    footerAction.run();
                }
            });
        }

        int safeTop = Math.max(0, systemInsetTop - rootFrame.getPaddingTop());
        int safeBottom = Math.max(0, systemInsetBottom - rootFrame.getPaddingBottom());
        int maxHeight = Math.round(getResources().getDisplayMetrics().heightPixels * .90f) - safeTop - safeBottom;
        int desiredHeight = dp(120 + contentHeightDp + (footerAction == null ? 0 : 57));
        int panelHeight = Math.min(maxHeight, desiredHeight);
        FrameLayout.LayoutParams panelParams = new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, panelHeight, Gravity.BOTTOM);
        panelParams.setMargins(dp(6), safeTop, dp(6), dp(6) + safeBottom);
        overlay.addView(panel, panelParams);
        rootFrame.addView(overlay, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        activeOverlay = overlay;
        activeOverlayPanel = panel;
        activeOverlaySheet = true;
        activeOverlayBackAction = backAction;
        activeOverlayDismissAction = null;
        overlayDismissInProgress = false;
        themeSheetTree(panel);
        Motion.showSheet(overlay, panel, reduceMotion());
        close.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View view) { dismissOverlay(); }
        });
    }

    private void showMainMenu() {
        if (!requireStartupReady()) return;
        startupSessionPending = false;
        String subtitle = currentHost().length() == 0 ? modeLabel() : currentHost() + " · " + modeLabel();
        boolean bookmarked = dataStore != null && dataStore.isBookmarked(currentPageUrl);
        String[] items = new String[] {
                "Nouvel onglet",
                "Outils des onglets",
                "Signets et historique",
                "Centre de téléchargements",
                bookmarked ? "Gérer le favori actuel" : "Ajouter la page actuelle aux favoris",
                "Protection et scripts",
                "Site de bureau",
                "Mode sombre",
                "Blocage de publicités",
                "Outils de page",
                "Scanner un QR code",
                "Nouvelle fenêtre privée"
        };
        int[] icons = new int[] {
                BrowserIconView.PLUS, BrowserIconView.TABS, BrowserIconView.HISTORY,
                BrowserIconView.DOWNLOAD, BrowserIconView.BOOKMARK, BrowserIconView.SHIELD,
                BrowserIconView.DESKTOP, BrowserIconView.APPEARANCE, BrowserIconView.SHIELD,
                BrowserIconView.MENU, BrowserIconView.QR, BrowserIconView.SHIELD
        };
        int[] kinds = new int[] {
                SHEET_ROW_ACTION, SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE,
                SHEET_ROW_ACTION, SHEET_ROW_NAVIGATE,
                desktopMode ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                nightMode ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                adBlockEnabled ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                SHEET_ROW_NAVIGATE, SHEET_ROW_ACTION, SHEET_ROW_ACTION
        };
        showDashboardSheet("Median", subtitle, items, icons, kinds, 3,
                new int[] { 0, 6, 9 }, new String[] { "Frequents", "Interrupteurs rapides", "Outils" },
                null, new Runnable() {
                    @Override public void run() { showBrowserSettings(); }
                }, "Paramètres du navigateur", BrowserIconView.SETTINGS, new SheetHandler() {
            @Override public void onItem(int which) {
                switch (which) {
                    case 0: newTab(); break;
                    case 1: showTabTools(); break;
                    case 2: showBrowserLibrary(); break;
                    case 3: showDownloadCenter(); break;
                    case 4: toggleCurrentBookmark(); break;
                    case 5:
                        showProtectionPanel(new Runnable() {
                            @Override public void run() { showMainMenu(); }
                        });
                        break;
                    case 6:
                        desktopMode = !desktopMode;
                        prefs.edit().putBoolean("desktop", desktopMode).apply();
                        applyDesktopMode();
                        reloadWebView(webView);
                        showMainMenu();
                        break;
                    case 7:
                        toggleNightMode();
                        showMainMenu();
                        break;
                    case 8:
                        adBlockEnabled = !adBlockEnabled;
                        prefs.edit().putBoolean("adblock", adBlockEnabled).apply();
                        adBlockActiveByView.clear();
                        if (webView != null && isNetworkPage(currentPageUrl)) reloadWebView(webView);
                        toast(adBlockEnabled ? "Blocage de publicités activé" : "Blocage de publicités désactivé");
                        showMainMenu();
                        break;
                    case 9: showPageTools(); break;
                    case 10: startQrScan(); break;
                    case 11: openPrivateWindow(); break;
                    default: break;
                }
            }
        });
    }

    private void showPrivacyTools() {
        String[] items = new String[] {
                "Filtres publicitaires et de confidentialité\nAbonnements, exceptions et diagnostic des règles",
                "Scripts utilisateur\nInstallation, mise à jour, activation et commandes",
                "Gestionnaire de mots de passe\nEnregistrement et remplissage chiffrés localement"
        };
        int[] icons = new int[] { BrowserIconView.SHIELD, BrowserIconView.SCRIPT, BrowserIconView.KEY };
        showActionSheet("Confidentialité et extensions", "Toutes les données sont enregistrées localement par défaut", items, icons,
                null, null, new Runnable() {
                    @Override public void run() { showMainMenu(); }
                }, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) showFilterCenter(new Runnable() {
                            @Override public void run() { showPrivacyTools(); }
                        });
                        else if (which == 1) showScriptCenter(new Runnable() {
                            @Override public void run() { showPrivacyTools(); }
                        });
                        else showPasswordMenu(new Runnable() {
                            @Override public void run() { showPrivacyTools(); }
                        });
                    }
                });
    }

    private void openPrivateWindow() {
        if (Build.VERSION.SDK_INT < 28) {
            toast("La WebView système d'Android 8 ne prend pas en charge l'isolation fiable des répertoires de données ; pour éviter un mode privé factice, la fenêtre privée n'est pas disponible sur cet appareil.");
            return;
        }
        try { startActivity(new Intent(this, PrivateActivity.class)); }
        catch (Exception e) { toast("Impossible de lancer la fenêtre privée"); }
    }

    private void toggleCurrentBookmark() {
        String url = currentPageUrl;
        if (!isNetworkPage(url)) {
            toast("Cette page ne peut pas être ajoutée aux favoris");
            return;
        }
        BrowserDataStore.Bookmark existing = dataStore.bookmark(url);
        if (existing != null) {
            showBookmarkActions(existing, bookmarkFolders == null ? BookmarkFolderStore.ROOT : bookmarkFolders.parentForUrl(url));
            return;
        }
        showBookmarkEditor(null, webView.getTitle(), url, BookmarkFolderStore.ROOT);
    }

    private void showBrowserLibrary() {
        String[] items = new String[] {
                "Favoris et dossiers (" + dataStore.bookmarks().size() + ")\nSites personnalisés, renommage et dossiers multiniveaux",
                "Historique (" + dataStore.historyCount() + ")\nGroupé par date, avec recherche et gestion individuelle",
                "Pages hors ligne (" + services.offlinePages().getAll().size() + "）",
                "Exporter une sauvegarde de signets",
                "Importer une sauvegarde de signets",
                "Exporter une sauvegarde complète chiffrée",
                "Importer une sauvegarde complète chiffrée"
        };
        int[] icons = new int[] { BrowserIconView.PLUS, BrowserIconView.HISTORY,
                BrowserIconView.STORAGE, BrowserIconView.SHARE, BrowserIconView.STORAGE,
                BrowserIconView.KEY, BrowserIconView.KEY };
        showActionSheet("Signets et historique", "Enregistré localement · aucun envoi vers le cloud", items, icons, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) openBookmarkManager(new Runnable() {
                    @Override public void run() { showBrowserLibrary(); }
                });
                else if (which == 1) showHistoryList("");
                else if (which == 2) showOfflinePages();
                else if (which == 3) beginBackupExport();
                else if (which == 4) beginBackupImport();
                else if (which == 5) beginFullBackupExport();
                else beginFullBackupImport();
            }
        });
    }

    private void showBookmarkList(boolean ignored) { openBookmarkManager(null); }

    private void openBookmarkManager(Runnable rootBackAction) {
        bookmarkFolderRootBackAction = rootBackAction;
        showBookmarkFolder(BookmarkFolderStore.ROOT);
    }

    private void showBookmarkFolder(String requestedId) {
        if (dataStore == null || bookmarkFolders == null) return;
        final BookmarkFolderStore.Folder current = bookmarkFolders.folder(requestedId);
        final String folderId = current == null ? BookmarkFolderStore.ROOT : current.id;
        final List<BookmarkFolderStore.Folder> childFolders = bookmarkFolders.foldersIn(folderId);
        final ArrayList<BrowserDataStore.Bookmark> childBookmarks = new ArrayList<BrowserDataStore.Bookmark>();
        for (BrowserDataStore.Bookmark item : dataStore.bookmarks())
            if (folderId.equals(bookmarkFolders.parentForUrl(item.url))) childBookmarks.add(item);

        ArrayList<String> labels = new ArrayList<String>();
        ArrayList<Integer> iconList = new ArrayList<Integer>();
        ArrayList<Integer> kindList = new ArrayList<Integer>();
        labels.add("Nouveau site favori\nInutile d'ouvrir d'abord la page"); iconList.add(BrowserIconView.PLUS); kindList.add(SHEET_ROW_ACTION);
        labels.add("Nouveau sous-dossier"); iconList.add(BrowserIconView.STORAGE); kindList.add(SHEET_ROW_ACTION);
        if (current != null) {
            labels.add("Paramètres du dossier actuel\nRenommage et affichage sur l'accueil"); iconList.add(BrowserIconView.SETTINGS); kindList.add(SHEET_ROW_ACTION);
            labels.add("Supprimer le dossier actuel\nLes sous-dossiers seront également supprimés, les sites reviendront dans Tous les favoris"); iconList.add(BrowserIconView.CLOSE); kindList.add(SHEET_ROW_ACTION);
        }
        final int actionCount = labels.size();
        for (BookmarkFolderStore.Folder folder : childFolders) {
            labels.add(folder.name + "\nDossier" + (folder.showOnHome ? " · affiché sur la page d'accueil" : ""));
            iconList.add(BrowserIconView.STORAGE); kindList.add(SHEET_ROW_NAVIGATE);
        }
        for (BrowserDataStore.Bookmark item : childBookmarks) {
            labels.add(item.title + "\n" + hostOf(item.url));
            iconList.add(BrowserIconView.BOOKMARK); kindList.add(SHEET_ROW_NAVIGATE);
        }
        String[] items = labels.toArray(new String[labels.size()]);
        int[] icons = new int[iconList.size()];
        int[] kinds = new int[kindList.size()];
        String[] sections = new String[items.length];
        for (int i = 0; i < icons.length; i++) { icons[i] = iconList.get(i).intValue(); kinds[i] = kindList.get(i).intValue(); }
        if (items.length > 0) sections[0] = "Actions";
        if (!childFolders.isEmpty()) sections[actionCount] = "Dossier";
        if (!childBookmarks.isEmpty()) sections[actionCount + childFolders.size()] = "Site";
        Runnable back = current == null ? bookmarkFolderRootBackAction : new Runnable() {
            @Override public void run() { showBookmarkFolder(current.parentId); }
        };
        showActionSheet(current == null ? "Favoris et dossiers" : current.name,
                bookmarkFolders.path(folderId), items, icons, kinds, sections, back, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) showBookmarkEditor(null, "", "", folderId);
                else if (which == 1) showBookmarkFolderEditor(null, folderId);
                else if (current != null && which == 2) showBookmarkFolderEditor(current, current.parentId);
                else if (current != null && which == 3) confirmDeleteBookmarkFolder(current, false);
                else {
                    int index = which - actionCount;
                    if (index < childFolders.size()) showBookmarkFolder(childFolders.get(index).id);
                    else showBookmarkActions(childBookmarks.get(index - childFolders.size()), folderId);
                }
            }
        });
    }

    private void showBookmarkActions(final BrowserDataStore.Bookmark item, final String returnFolder) {
        showActionSheet(item.title, item.url,
                new String[] { "Ouvrir le site", "Modifier le nom, l'adresse et le dossier", "Supprimer le favori" },
                new int[] { BrowserIconView.SEARCH, BrowserIconView.SETTINGS, BrowserIconView.CLOSE },
                new int[] { SHEET_ROW_ACTION, SHEET_ROW_NAVIGATE, SHEET_ROW_ACTION }, null,
                new Runnable() { @Override public void run() { showBookmarkFolder(returnFolder); } },
                new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) loadInput(item.url);
                        else if (which == 1) showBookmarkEditor(item, item.title, item.url,
                                bookmarkFolders.parentForUrl(item.url));
                        else confirmDeleteBookmark(item, returnFolder);
                    }
                });
    }

    private void confirmDeleteBookmark(final BrowserDataStore.Bookmark item, final String returnFolder) {
        new AlertDialog.Builder(this).setTitle("Supprimer le favori ?").setMessage(item.title)
                .setPositiveButton("Supprimer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        dataStore.removeBookmark(item.url);
                        bookmarkFolders.removeUrl(item.url);
                        refreshHomeAfterLibraryChange();
                        showBookmarkFolder(returnFolder);
                    }
                }).setNegativeButton("Annuler", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) { showBookmarkActions(item, returnFolder); }
                }).setOnCancelListener(new DialogInterface.OnCancelListener() {
                    @Override public void onCancel(DialogInterface dialog) { showBookmarkActions(item, returnFolder); }
                }).show();
    }

    private void showBookmarkEditor(final BrowserDataStore.Bookmark existing, String initialTitle,
                                    String initialUrl, final String initialFolder) {
        final EditText title = new EditText(this);
        title.setHint("Nom"); title.setSingleLine(true); title.setText(initialTitle == null ? "" : initialTitle);
        final EditText url = new EditText(this);
        url.setHint("Adresse, par exemple example.com"); url.setSingleLine(true); url.setText(initialUrl == null ? "" : initialUrl);
        final String[] selectedFolder = new String[] { bookmarkFolders.folder(initialFolder) == null ? BookmarkFolderStore.ROOT : initialFolder };
        final Button folder = new Button(this);
        folder.setAllCaps(false); folder.setText("Emplacement : " + bookmarkFolders.path(selectedFolder[0]));
        LinearLayout fields = new LinearLayout(this);
        fields.setOrientation(LinearLayout.VERTICAL); fields.setPadding(dp(18), 0, dp(18), 0);
        fields.addView(title); fields.addView(url); fields.addView(folder);
        folder.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { showBookmarkFolderPicker(selectedFolder, folder); }
        });
        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle(existing == null ? "Nouveau site favori" : "Modifier le favori")
                .setView(fields).setPositiveButton("Enregistrer", null)
                .setNegativeButton("Annuler", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface d, int which) { showBookmarkFolder(initialFolder); }
                }).create();
        dialog.setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface ignored) { showBookmarkFolder(initialFolder); }
        });
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) {
                        String normalized = normalizeConfiguredHomeUrl(url.getText().toString());
                        if (normalized.length() == 0) { url.setError("Veuillez saisir une adresse HTTP(S) valide"); return; }
                        String name = title.getText().toString().trim();
                        if (name.length() == 0) name = hostOf(normalized);
                        if (existing == null) {
                            BrowserDataStore.Bookmark added = dataStore.addBookmark(name, normalized);
                            if (added == null) { url.setError("Cette adresse est déjà dans les favoris"); return; }
                            bookmarkFolders.setParentForUrl(added.url, selectedFolder[0]);
                        } else {
                            if (!dataStore.updateBookmark(existing.url, name, normalized)) {
                                url.setError("Adresse invalide ou déjà existante"); return;
                            }
                            bookmarkFolders.updateUrl(existing.url, normalized);
                            bookmarkFolders.setParentForUrl(normalized, selectedFolder[0]);
                        }
                        dialog.dismiss();
                        refreshHomeAfterLibraryChange();
                        showBookmarkFolder(selectedFolder[0]);
                    }
                });
            }
        });
        dialog.show();
    }

    private void showBookmarkFolderPicker(final String[] selected, final Button label) {
        final ArrayList<BookmarkFolderStore.Folder> folders = new ArrayList<BookmarkFolderStore.Folder>(bookmarkFolders.allFolders());
        Collections.sort(folders, new java.util.Comparator<BookmarkFolderStore.Folder>() {
            @Override public int compare(BookmarkFolderStore.Folder a, BookmarkFolderStore.Folder b) {
                return bookmarkFolders.path(a.id).compareToIgnoreCase(bookmarkFolders.path(b.id));
            }
        });
        String[] names = new String[folders.size() + 1];
        names[0] = "Tous les favoris (barre de raccourcis de l'accueil)";
        int checked = 0;
        for (int i = 0; i < folders.size(); i++) {
            names[i + 1] = bookmarkFolders.path(folders.get(i).id);
            if (folders.get(i).id.equals(selected[0])) checked = i + 1;
        }
        new AlertDialog.Builder(this).setTitle("Choisir un dossier").setSingleChoiceItems(names, checked,
                new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        selected[0] = which == 0 ? BookmarkFolderStore.ROOT : folders.get(which - 1).id;
                        label.setText("Emplacement : " + bookmarkFolders.path(selected[0]));
                        dialog.dismiss();
                    }
                }).setNegativeButton("Annuler", null).show();
    }

    private void showBookmarkFolderEditor(final BookmarkFolderStore.Folder existing, final String parentId) {
        final EditText name = new EditText(this);
        name.setHint("Nom du dossier"); name.setSingleLine(true); name.setText(existing == null ? "" : existing.name);
        final CheckBox home = new CheckBox(this);
        home.setText("Afficher dans la barre de raccourcis de l'accueil"); home.setChecked(existing != null && existing.showOnHome);
        LinearLayout fields = new LinearLayout(this);
        fields.setOrientation(LinearLayout.VERTICAL); fields.setPadding(dp(18), 0, dp(18), 0);
        fields.addView(name); fields.addView(home);
        final AlertDialog dialog = new AlertDialog.Builder(this).setTitle(existing == null ? "Nouveau sous-dossier" : "Modifier le dossier")
                .setView(fields).setPositiveButton("Enregistrer", null)
                .setNegativeButton("Annuler", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface d, int which) { showBookmarkFolder(parentId); }
                }).create();
        dialog.setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface ignored) { showBookmarkFolder(parentId); }
        });
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) {
                        String title = name.getText().toString().trim();
                        if (title.length() == 0) { name.setError("Veuillez saisir le nom du dossier"); return; }
                        boolean saved = existing == null
                                ? bookmarkFolders.create(title, parentId, home.isChecked()) != null
                                : bookmarkFolders.update(existing.id, title, existing.parentId, home.isChecked());
                        if (!saved) { name.setError("Impossible d'enregistrer le dossier"); return; }
                        dialog.dismiss(); refreshHomeAfterLibraryChange(); showBookmarkFolder(parentId);
                    }
                });
            }
        });
        dialog.show();
    }

    private void showBookmarkFolderActions(final BookmarkFolderStore.Folder folder) {
        showActionSheet(folder.name, bookmarkFolders.path(folder.id),
                new String[] { "Renommer et affichage sur l'accueil", "Supprimer le dossier\nLes sous-dossiers seront supprimés, les sites reviendront dans Tous les favoris" },
                new int[] { BrowserIconView.SETTINGS, BrowserIconView.CLOSE },
                new int[] { SHEET_ROW_NAVIGATE, SHEET_ROW_ACTION }, null,
                new Runnable() { @Override public void run() { showBookmarkFolder(folder.id); } },
                new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) showBookmarkFolderEditor(folder, folder.parentId);
                        else confirmDeleteBookmarkFolder(folder, true);
                    }
                });
    }

    private void confirmDeleteBookmarkFolder(final BookmarkFolderStore.Folder folder, final boolean returnToActions) {
        if (folder == null || bookmarkFolders.folder(folder.id) == null) {
            toast("Le dossier n'existe plus");
            showBookmarkFolder(folder == null ? BookmarkFolderStore.ROOT : folder.parentId);
            return;
        }
        int nested = bookmarkFolders.descendantFolderCount(folder.id);
        int bookmarks = bookmarkFolders.bookmarkCountInTree(folder.id);
        StringBuilder message = new StringBuilder("“").append(folder.name).append(" » sera supprimé");
        if (nested > 0) message.append(", ainsi que ").append(nested).append(" sous-dossiers");
        if (bookmarks > 0) message.append(". Parmi eux, ").append(bookmarks).append(" sites ne seront pas supprimés, ils seront déplacés dans Tous les favoris");
        message.append("。");
        new AlertDialog.Builder(this).setTitle("Supprimer le dossier ?").setMessage(message.toString())
                .setPositiveButton("Supprimer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        if (!bookmarkFolders.remove(folder.id)) {
                            toast("Échec de la suppression : le dossier n'existe plus");
                        } else {
                            refreshHomeAfterLibraryChange();
                            toast("Dossier supprimé");
                        }
                        showBookmarkFolder(folder.parentId);
                    }
                }).setNegativeButton("Annuler", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        if (returnToActions) showBookmarkFolderActions(folder); else showBookmarkFolder(folder.id);
                    }
                }).setOnCancelListener(new DialogInterface.OnCancelListener() {
                    @Override public void onCancel(DialogInterface dialog) {
                        if (returnToActions) showBookmarkFolderActions(folder); else showBookmarkFolder(folder.id);
                    }
                }).show();
    }

    private void refreshHomeAfterLibraryChange() {
        cachedHomeKey = "";
        renderedHomeKeys.clear();
        if (isHomeUrl(currentPageUrl)) showHome();
    }

    private void showHistoryList(final String query) {
        if (dataStore == null) return;
        dismissOverlayForNavigation();
        final int pageBackground = nightMode ? DARK_BACKGROUND : WHITE;
        final int cardBackground = nightMode ? DARK_CARD : WHITE;
        final int pageText = nightMode ? DARK_TEXT : TEXT;
        final int pageMuted = nightMode ? DARK_MUTED : MUTED;
        final FrameLayout overlay = new FrameLayout(this);
        overlay.setBackgroundColor(pageBackground);
        overlay.setClickable(true);
        overlay.setFocusableInTouchMode(true);

        LinearLayout page = new LinearLayout(this);
        page.setOrientation(LinearLayout.VERTICAL);
        page.setPadding(dp(14), dp(8), dp(14), dp(12));
        overlay.addView(page, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.CENTER_VERTICAL);
        BrowserIconView back = iconButton(BrowserIconView.BACK, "Retour aux signets et à l'historique");
        back.setTintColor(pageText);
        header.addView(back, new LinearLayout.LayoutParams(dp(46), dp(48)));
        final TextView title = new TextView(this);
        title.setTextSize(22f);
        title.setTextColor(pageText);
        title.setTypeface(android.graphics.Typeface.DEFAULT_BOLD);
        header.addView(title, new LinearLayout.LayoutParams(0, dp(54), 1f));
        BrowserIconView clear = iconButton(BrowserIconView.DELETE, "Vider l'historique");
        BrowserIconView close = iconButton(BrowserIconView.CLOSE, "Retour à la page");
        clear.setTintColor(pageText);
        close.setTintColor(pageText);
        header.addView(clear, new LinearLayout.LayoutParams(dp(46), dp(48)));
        header.addView(close, new LinearLayout.LayoutParams(dp(46), dp(48)));
        page.addView(header, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(58)));

        LinearLayout searchPill = new LinearLayout(this);
        searchPill.setOrientation(LinearLayout.HORIZONTAL);
        searchPill.setGravity(Gravity.CENTER_VERTICAL);
        searchPill.setPadding(dp(12), 0, dp(4), 0);
        searchPill.setBackground(roundRect(nightMode ? 0xff303337 : SURFACE, 20));
        final EditText search = new EditText(this);
        search.setSingleLine(true);
        search.setText(query == null ? "" : query);
        search.setHint("Rechercher par titre ou adresse");
        search.setHintTextColor(pageMuted);
        search.setTextColor(pageText);
        search.setTextSize(14.5f);
        search.setImeOptions(EditorInfo.IME_ACTION_SEARCH);
        search.setBackgroundColor(Color.TRANSPARENT);
        search.setPadding(0, 0, dp(6), 0);
        searchPill.addView(search, new LinearLayout.LayoutParams(0, dp(46), 1f));
        BrowserIconView runSearch = iconButton(BrowserIconView.SEARCH, "Rechercher dans l'historique");
        runSearch.setTintColor(pageText);
        searchPill.addView(runSearch, new LinearLayout.LayoutParams(dp(44), dp(44)));
        LinearLayout.LayoutParams searchParams = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, dp(46));
        searchParams.setMargins(dp(2), 0, dp(2), dp(10));
        page.addView(searchPill, searchParams);

        final ArrayList<Object> rows = new ArrayList<Object>();
        final BaseAdapter[] adapterHolder = new BaseAdapter[1];
        final String[] activeQuery = new String[] { query == null ? "" : query.trim() };
        final FrameLayout body = new FrameLayout(this);
        final TextView empty = new TextView(this);
        empty.setTextColor(pageMuted);
        empty.setTextSize(14f);
        empty.setGravity(Gravity.CENTER);
        empty.setPadding(dp(24), dp(24), dp(24), dp(24));

        final class HistoryRow {
            final LinearLayout root;
            final TextView primary;
            final TextView secondary;
            final BrowserIconView more;

            HistoryRow() {
                root = new LinearLayout(MainActivity.this);
                root.setOrientation(LinearLayout.HORIZONTAL);
                root.setGravity(Gravity.CENTER_VERTICAL);
                root.setPadding(dp(16), dp(7), dp(7), dp(7));
                root.setElevation(dp(1));
                root.setClickable(true);
                LinearLayout labels = new LinearLayout(MainActivity.this);
                labels.setOrientation(LinearLayout.VERTICAL);
                labels.setGravity(Gravity.CENTER_VERTICAL);
                primary = new TextView(MainActivity.this);
                primary.setTextColor(pageText);
                primary.setTextSize(15.5f);
                primary.setSingleLine(true);
                primary.setEllipsize(android.text.TextUtils.TruncateAt.END);
                secondary = new TextView(MainActivity.this);
                secondary.setTextColor(pageMuted);
                secondary.setTextSize(12.5f);
                secondary.setSingleLine(true);
                secondary.setEllipsize(android.text.TextUtils.TruncateAt.END);
                labels.addView(primary, new LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT, dp(27)));
                labels.addView(secondary, new LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT, dp(23)));
                root.addView(labels, new LinearLayout.LayoutParams(0, dp(58), 1f));
                more = iconButton(BrowserIconView.MENU, "Actions sur l'historique");
                more.setTintColor(pageText);
                more.setFocusable(false);
                root.addView(more, new LinearLayout.LayoutParams(dp(46), dp(46)));
            }

            void bind(final BrowserDataStore.HistoryItem item) {
                root.setBackground(roundRect(cardBackground, 18));
                primary.setText(item.title);
                CharSequence relative = android.text.format.DateUtils.getRelativeTimeSpanString(
                        item.visitedAt, System.currentTimeMillis(), android.text.format.DateUtils.MINUTE_IN_MILLIS);
                String visits = item.visits > 1 ? " · " + item.visits + " visites" : "";
                secondary.setText(hostOf(item.url) + " · " + relative + visits);
                root.setContentDescription(item.title + "，" + hostOf(item.url));
                root.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View view) {
                        dismissOverlayForNavigation();
                        loadInput(item.url);
                    }
                });
                more.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View view) {
                        showHistoryItemActions(item, activeQuery[0]);
                    }
                });
            }
        }

        final BaseAdapter adapter = new BaseAdapter() {
            @Override public int getCount() { return rows.size(); }
            @Override public Object getItem(int position) { return rows.get(position); }
            @Override public long getItemId(int position) { return position; }
            @Override public int getViewTypeCount() { return 2; }
            @Override public int getItemViewType(int position) { return rows.get(position) instanceof String ? 0 : 1; }
            @Override public boolean isEnabled(int position) { return !(rows.get(position) instanceof String); }
            @Override public View getView(int position, View convertView, ViewGroup parent) {
                Object value = rows.get(position);
                if (value instanceof String) {
                    TextView section = convertView instanceof TextView ? (TextView) convertView : new TextView(MainActivity.this);
                    section.setText((String) value);
                    section.setTextColor(BLUE);
                    section.setTextSize(12f);
                    section.setTypeface(android.graphics.Typeface.DEFAULT_BOLD);
                    section.setGravity(Gravity.BOTTOM | Gravity.START);
                    section.setPadding(dp(8), 0, dp(8), dp(7));
                    return section;
                }
                HistoryRow row;
                if (convertView == null || !(convertView.getTag() instanceof HistoryRow)) {
                    row = new HistoryRow();
                    row.root.setTag(row);
                    convertView = row.root;
                } else row = (HistoryRow) convertView.getTag();
                row.bind((BrowserDataStore.HistoryItem) value);
                return convertView;
            }
        };
        adapterHolder[0] = adapter;
        ListView list = new ListView(this);
        list.setAdapter(adapter);
        list.setBackgroundColor(Color.TRANSPARENT);
        list.setDivider(new android.graphics.drawable.ColorDrawable(Color.TRANSPARENT));
        list.setDividerHeight(dp(9));
        list.setPadding(0, 0, 0, dp(20));
        list.setClipToPadding(false);
        list.setVerticalScrollBarEnabled(false);
        body.addView(list, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        body.addView(empty, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        page.addView(body, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f));

        final Runnable rebuild = new Runnable() {
            @Override public void run() {
                rows.clear();
                List<BrowserDataStore.HistoryItem> items = dataStore.recentHistory(200, activeQuery[0]);
                java.util.Calendar today = java.util.Calendar.getInstance();
                today.set(java.util.Calendar.HOUR_OF_DAY, 0);
                today.set(java.util.Calendar.MINUTE, 0);
                today.set(java.util.Calendar.SECOND, 0);
                today.set(java.util.Calendar.MILLISECOND, 0);
                long todayStart = today.getTimeInMillis();
                today.add(java.util.Calendar.DAY_OF_YEAR, -1);
                long yesterdayStart = today.getTimeInMillis();
                String lastSection = "";
                for (BrowserDataStore.HistoryItem item : items) {
                    String section;
                    if (item.visitedAt >= todayStart) section = "Aujourd'hui";
                    else if (item.visitedAt >= yesterdayStart) section = "Hier";
                    else section = android.text.format.DateFormat.getMediumDateFormat(MainActivity.this)
                            .format(new java.util.Date(item.visitedAt));
                    if (!section.equals(lastSection)) {
                        rows.add(section);
                        lastSection = section;
                    }
                    rows.add(item);
                }
                boolean noResults = items.size() == 0;
                empty.setText(activeQuery[0].length() == 0 ?
                        "Pas encore d'historique\nLes pages visitées s'afficheront ici par date" : "Aucun historique correspondant");
                empty.setVisibility(noResults ? View.VISIBLE : View.GONE);
                title.setText(activeQuery[0].length() == 0 ?
                        "Historique  " + dataStore.historyCount() : "Résultats  " + items.size());
                if (adapterHolder[0] != null) adapterHolder[0].notifyDataSetChanged();
            }
        };
        rebuild.run();

        View.OnClickListener searchAction = new View.OnClickListener() {
            @Override public void onClick(View view) {
                activeQuery[0] = search.getText().toString().trim();
                rebuild.run();
                hideKeyboard();
                search.clearFocus();
            }
        };
        runSearch.setOnClickListener(searchAction);
        search.setOnEditorActionListener(new TextView.OnEditorActionListener() {
            @Override public boolean onEditorAction(TextView view, int actionId, KeyEvent event) {
                if (actionId == EditorInfo.IME_ACTION_SEARCH ||
                        (event != null && event.getKeyCode() == KeyEvent.KEYCODE_ENTER)) {
                    activeQuery[0] = search.getText().toString().trim();
                    rebuild.run();
                    hideKeyboard();
                    search.clearFocus();
                    return true;
                }
                return false;
            }
        });
        back.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View view) { navigateOverlayBack(); }
        });
        close.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View view) { dismissOverlay(); }
        });
        clear.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View view) {
                if (dataStore.historyCount() == 0) { toast("L'historique est déjà vide"); return; }
                confirmClearHistory(new Runnable() {
                    @Override public void run() { showHistoryList(""); }
                });
            }
        });

        rootFrame.addView(overlay, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        activeOverlay = overlay;
        activeOverlayPanel = page;
        activeOverlaySheet = false;
        activeOverlayBackAction = new Runnable() {
            @Override public void run() { showBrowserLibrary(); }
        };
        activeOverlayDismissAction = null;
        Motion.showPage(overlay, page, reduceMotion());
    }

    private void showHistoryItemActions(final BrowserDataStore.HistoryItem item, final String query) {
        String relative = android.text.format.DateUtils.getRelativeTimeSpanString(item.visitedAt,
                System.currentTimeMillis(), android.text.format.DateUtils.MINUTE_IN_MILLIS).toString();
        showActionSheet(item.title, hostOf(item.url) + " · " + relative,
                new String[] { "Ouvrir la page", "Ouvrir dans un nouvel onglet", "Copier l'adresse", "Supprimer cette entrée" },
                new int[] { BrowserIconView.SEARCH, BrowserIconView.PLUS,
                        BrowserIconView.SHARE, BrowserIconView.DELETE },
                new int[] { SHEET_ROW_ACTION, SHEET_ROW_ACTION, SHEET_ROW_ACTION, SHEET_ROW_ACTION },
                null, new Runnable() {
                    @Override public void run() { showHistoryList(query); }
                }, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) loadInput(item.url);
                        else if (which == 1) openUrlInNewTab(item.url, true);
                        else if (which == 2) {
                            ClipboardManager manager = (ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
                            if (manager != null) manager.setPrimaryClip(ClipData.newPlainText("Adresse de l'historique", item.url));
                            toast("Adresse copiée");
                            showHistoryList(query);
                        } else {
                            dataStore.removeHistory(item.url);
                            toast("Cette entrée de l'historique a été supprimée");
                            showHistoryList(query);
                        }
                    }
                });
    }

    private void confirmClearHistory() {
        confirmClearHistory(null);
    }

    private void confirmClearHistory(final Runnable returnAction) {
        SettingsDialogReturn back = new SettingsDialogReturn(returnAction);
        new AlertDialog.Builder(this).setTitle("Vider l'historique ?").setMessage("Les signets, mots de passe et sessions de connexion ne seront pas supprimés.")
                .setPositiveButton("Vider", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        dataStore.clearHistory();
                        webView.clearHistory();
                        clearConnectionHints();
                        toast("Historique effacé");
                        continueSettingsPanel(returnAction);
                    }
                }).setNegativeButton("Annuler", back).setOnCancelListener(back).show();
    }

    private void beginBackupExport() {
        try {
            Intent intent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
            intent.addCategory(Intent.CATEGORY_OPENABLE);
            intent.setType("application/json");
            intent.putExtra(Intent.EXTRA_TITLE, "Median-bookmarks.json");
            startActivityForResult(intent, BACKUP_EXPORT_REQUEST);
        } catch (Exception e) { toast("Aucune application d'enregistrement de fichiers disponible"); }
    }

    private void beginBackupImport() {
        try {
            Intent intent = new Intent(Intent.ACTION_OPEN_DOCUMENT);
            intent.addCategory(Intent.CATEGORY_OPENABLE);
            intent.setType("*/*");
            intent.putExtra(Intent.EXTRA_MIME_TYPES, new String[] {
                    "application/json", "text/html", "application/xhtml+xml",
                    "application/x-netscape-bookmark", "text/plain"
            });
            startActivityForResult(intent, BACKUP_IMPORT_REQUEST);
        } catch (Exception e) { toast("Aucun sélecteur de fichiers disponible"); }
    }

    private void beginFullBackupExport() {
        persistSession();
        try {
            Intent intent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
            intent.addCategory(Intent.CATEGORY_OPENABLE);
            intent.setType("application/json");
            intent.putExtra(Intent.EXTRA_TITLE, "Median-encrypted-backup.json");
            startActivityForResult(intent, FULL_BACKUP_EXPORT_REQUEST);
        } catch (Exception e) { toast("Aucune application d'enregistrement de fichiers disponible"); }
    }

    private void beginFullBackupImport() {
        if (filterUpdateInProgress || scriptDownloadInProgress) { toast("Veuillez attendre la fin des tâches de filtres ou de scripts avant de restaurer"); return; }
        try {
            Intent intent = new Intent(Intent.ACTION_OPEN_DOCUMENT);
            intent.addCategory(Intent.CATEGORY_OPENABLE);
            intent.setType("application/json");
            startActivityForResult(intent, FULL_BACKUP_IMPORT_REQUEST);
        } catch (Exception e) { toast("Aucun sélecteur de fichiers disponible"); }
    }

    private void showSiteSettings() {
        final String host = currentHost();
        if (host.length() == 0) { toast("Cette page n'a pas de paramètres de site"); return; }
        final SiteSettingsStore.SiteSettings settings = siteSettingsStore.forHost(host);
        String[] items = new String[] {
                "Mode de compatibilité\nAssouplit les restrictions et suspend le filtrage pour ce site",
                "Contenu et confidentialité\nJavaScript, images, cookies, popups et nettoyage du suivi",
                "Autorisations du site\nPosition, caméra et microphone",
                "Affichage\nMode bureau, mode sombre et zoom du texte",
                "Réinitialiser les paramètres de ce site",
                "Effacer les cookies et le stockage de ce site"
        };
        int[] icons = new int[] { BrowserIconView.SPEED, BrowserIconView.SHIELD,
                BrowserIconView.KEY, BrowserIconView.APPEARANCE, BrowserIconView.RELOAD, BrowserIconView.CLOSE };
        int[] kinds = new int[] {
                settings.compatibilityMode() ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE,
                SHEET_ROW_ACTION, SHEET_ROW_ACTION
        };
        showActionSheet("Paramètres du site", host + " · affecte uniquement ce site", items, icons,
                kinds, null, null, new SheetHandler() {
            @Override public void onItem(int which) {
                if (!host.equalsIgnoreCase(currentHost())) {
                    dismissOverlayForNavigation();
                    toast("La page a changé, veuillez rouvrir les paramètres du site");
                    return;
                }
                if (which == 0) {
                    toggleCompatibilityMode(host, settings);
                    postAfterUiTransition(new Runnable() {
                        @Override public void run() { showSiteSettings(); }
                    });
                }
                else if (which == 1) showSiteContentSettings(host);
                else if (which == 2) showSitePermissionSettings(host);
                else if (which == 3) showSiteDisplaySettings(host);
                else if (which == 4) {
                    siteSettingsStore.clear(host);
                    adBlockActiveByView.clear();
                    applySiteSettings(webView, host);
                    reloadWebView(webView);
                    toast("Paramètres de ce site réinitialisés");
                } else confirmClearCurrentSiteData();
            }
        });
    }

    private void showSiteContentSettings(final String host) {
        final SiteSettingsStore.SiteSettings settings = siteSettingsStore.forHost(host);
        String[] items = new String[] {
                "JavaScript：" + triStateLabel(settings.get(SiteSettingsStore.JAVASCRIPT), "Hérité"),
                "Chargement des images : " + triStateLabel(settings.get(SiteSettingsStore.IMAGES), "Hérité"),
                "Cookies tiers : " + triStateLabel(settings.get(SiteSettingsStore.THIRD_PARTY_COOKIES), "Hérité"),
                "Fenêtres popup : " + triStateLabel(settings.get(SiteSettingsStore.POPUPS), "Déclenchement par l'utilisateur uniquement"),
                "Lecture automatique des médias : " + triStateLabel(settings.get(SiteSettingsStore.AUTOPLAY), "Nécessite une action de l'utilisateur"),
                "Nettoyage des paramètres de suivi : " + triStateLabel(settings.get(SiteSettingsStore.TRACKING_PROTECTION),
                        cleanTrackingParameters ? "Hérité (activé)" : "Hérité (désactivé)")
        };
        int[] icons = new int[] { BrowserIconView.SCRIPT, BrowserIconView.INFO, BrowserIconView.COOKIE,
                BrowserIconView.SHIELD, BrowserIconView.SPEED, BrowserIconView.CLEAN };
        int[] kinds = actionKinds(items.length);
        showActionSheet("Contenu et confidentialité", host + " · touchez pour basculer : hérité, autoriser, bloquer", items, icons,
                kinds, null, new Runnable() {
                    @Override public void run() { showSiteSettings(); }
                }, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (!host.equalsIgnoreCase(currentHost())) {
                            dismissOverlayForNavigation();
                            toast("La page a changé, veuillez rouvrir les paramètres du site");
                            return;
                        }
                        int key = which == 0 ? SiteSettingsStore.JAVASCRIPT :
                                which == 1 ? SiteSettingsStore.IMAGES :
                                which == 2 ? SiteSettingsStore.THIRD_PARTY_COOKIES :
                                which == 3 ? SiteSettingsStore.POPUPS :
                                which == 4 ? SiteSettingsStore.AUTOPLAY : SiteSettingsStore.TRACKING_PROTECTION;
                        settings.set(key, nextTriState(settings.get(key)));
                        saveSiteSettingsAndReturn(host, settings, new Runnable() {
                            @Override public void run() { showSiteContentSettings(host); }
                        });
                    }
                });
    }

    private void showSitePermissionSettings(final String host) {
        final SiteSettingsStore.SiteSettings settings = siteSettingsStore.forHost(host);
        String[] items = new String[] {
                "Position : " + triStateLabel(settings.get(SiteSettingsStore.LOCATION), "Demander à chaque fois"),
                "Caméra : " + triStateLabel(settings.get(SiteSettingsStore.CAMERA), "Demander à chaque fois"),
                "Microphone : " + triStateLabel(settings.get(SiteSettingsStore.MICROPHONE), "Demander à chaque fois")
        };
        int[] icons = new int[] { BrowserIconView.SHIELD, BrowserIconView.SHIELD, BrowserIconView.SHIELD };
        showActionSheet("Autorisations du site", host + " · « hérité » signifie demander à chaque fois", items, icons,
                actionKinds(items.length), null, new Runnable() {
                    @Override public void run() { showSiteSettings(); }
                }, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (!host.equalsIgnoreCase(currentHost())) {
                            dismissOverlayForNavigation();
                            toast("La page a changé, veuillez rouvrir les paramètres du site");
                            return;
                        }
                        int key = which == 0 ? SiteSettingsStore.LOCATION :
                                which == 1 ? SiteSettingsStore.CAMERA : SiteSettingsStore.MICROPHONE;
                        settings.set(key, nextTriState(settings.get(key)));
                        saveSiteSettingsAndReturn(host, settings, new Runnable() {
                            @Override public void run() { showSitePermissionSettings(host); }
                        });
                    }
                });
    }

    private void showSiteDisplaySettings(final String host) {
        final SiteSettingsStore.SiteSettings settings = siteSettingsStore.forHost(host);
        String[] items = new String[] {
                "Mode bureau : " + triStateLabel(settings.get(SiteSettingsStore.DESKTOP), "Hérité"),
                "Mode sombre : " + triStateLabel(settings.get(SiteSettingsStore.DARK), "Hérité"),
                "Zoom du texte : " + settings.textZoom() + "%"
        };
        int[] icons = new int[] { BrowserIconView.DESKTOP, BrowserIconView.APPEARANCE, BrowserIconView.SEARCH };
        showActionSheet("Affichage", host, items, icons, actionKinds(items.length), null,
                new Runnable() {
                    @Override public void run() { showSiteSettings(); }
                }, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (!host.equalsIgnoreCase(currentHost())) {
                            dismissOverlayForNavigation();
                            toast("La page a changé, veuillez rouvrir les paramètres du site");
                            return;
                        }
                        if (which < 2) {
                            int key = which == 0 ? SiteSettingsStore.DESKTOP : SiteSettingsStore.DARK;
                            settings.set(key, nextTriState(settings.get(key)));
                        }
                        else {
                            showTextZoomDialog(host, settings, new Runnable() {
                                @Override public void run() { showSiteDisplaySettings(host); }
                            });
                            return;
                        }
                        if (which == 1) {
                            siteSettingsStore.save(host, settings);
                            appliedSiteSettings.remove(webView);
                            applySiteSettings(webView, host);
                            postAfterUiTransition(new Runnable() {
                                @Override public void run() { showSiteDisplaySettings(host); }
                            });
                            return;
                        }
                        saveSiteSettingsAndReturn(host, settings, new Runnable() {
                            @Override public void run() { showSiteDisplaySettings(host); }
                        });
                    }
                });
    }

    private static int[] actionKinds(int count) {
        int[] result = new int[Math.max(0, count)];
        java.util.Arrays.fill(result, SHEET_ROW_ACTION);
        return result;
    }

    private void saveSiteSettingsAndReturn(String host, SiteSettingsStore.SiteSettings settings,
                                           Runnable returnAction) {
        if (!host.equalsIgnoreCase(currentHost())) {
            toast("La page a changé, veuillez rouvrir les paramètres du site");
            return;
        }
        siteSettingsStore.save(host, settings);
        adBlockActiveByView.clear();
        applySiteSettings(webView, host);
        reloadWebView(webView);
        postAfterUiTransition(returnAction);
    }


    private void toggleCompatibilityMode(String host, SiteSettingsStore.SiteSettings settings) {
        if (host == null || host.length() == 0 || settings == null) return;
        if (settings.compatibilityMode()) {
            settings.compatibilityMode(false);
            siteSettingsStore.save(host, settings);
            adBlockActiveByView.clear();
            applySiteSettings(webView, host);
            reloadWebView(webView);
            toast("Mode de compatibilité désactivé");
            return;
        }
        enableCompatibilityForHost(host, true);
    }

    private void enableCompatibilityForHost(String host, boolean reload) {
        if (host == null || host.length() == 0 || siteSettingsStore == null) return;
        SiteSettingsStore.SiteSettings settings = siteSettingsStore.forHost(host);
        settings.compatibilityMode(true);
        siteSettingsStore.save(host, settings);
        adBlockActiveByView.clear();
        if (webView != null) applySiteSettings(webView, host);
        if (reload && webView != null) reloadWebView(webView);
        toast("Mode de compatibilité activé pour ce site");
    }

    private static boolean compatibilityRelevantError(int errorCode) {
        return errorCode == WebViewClient.ERROR_FAILED_SSL_HANDSHAKE ||
                errorCode == WebViewClient.ERROR_REDIRECT_LOOP ||
                errorCode == WebViewClient.ERROR_UNSUPPORTED_SCHEME ||
                errorCode == WebViewClient.ERROR_UNKNOWN;
    }

    private void maybeOfferCompatibilityMode(final String failedUrl, String reason) {
        if (isFinishing() || !activityResumed || compatibilityDialogShowing ||
                failedUrl == null || failedUrl.length() == 0 || !isNetworkPage(failedUrl)) return;
        final String host = hostOf(failedUrl);
        if (host.length() == 0 || siteSettingsStore == null) return;
        SiteSettingsStore.SiteSettings existing = siteSettingsStore.forHost(host);
        if (existing.compatibilityMode()) return;
        long now = SystemClock.uptimeMillis();
        if (host.equals(lastCompatibilityOfferHost) && now - lastCompatibilityOfferAt < 15000L) return;
        lastCompatibilityOfferHost = host;
        lastCompatibilityOfferAt = now;
        AlertDialog.Builder builder = new AlertDialog.Builder(this)
                .setTitle("Réessayer en mode de compatibilité ?")
                .setMessage(reason + "：" + host + "\n\nLes cookies tiers, les popups déclenchés par l'utilisateur et le contenu mixte seront assouplis uniquement pour ce site, et le filtrage publicitaire/de suivi sera suspendu pour ce site.")
                .setPositiveButton("Nouvelle tentative en mode compatibilité", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        enableCompatibilityForHost(host, false);
                        if (webView != null) loadNetworkUrl(webView, failedUrl);
                    }
                })
                .setNegativeButton("Annuler", null);
        if (failedUrl.regionMatches(true, 0, "https://", 0, 8)) {
            builder.setNeutralButton("Réessayer en HTTP (non sécurisé)", new DialogInterface.OnClickListener() {
                @Override public void onClick(DialogInterface dialog, int which) {
                    enableCompatibilityForHost(host, false);
                    if (webView != null) loadNetworkUrl(webView, "http://" + failedUrl.substring(8));
                }
            });
        }
        AlertDialog dialog = builder.create();
        dialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
            @Override public void onDismiss(DialogInterface dialog) { compatibilityDialogShowing = false; }
        });
        compatibilityDialogShowing = true;
        dialog.show();
    }

    private void showTextZoomDialog(final String host, final SiteSettingsStore.SiteSettings settings,
                                    final Runnable returnAction) {
        SettingsDialogReturn back = new SettingsDialogReturn(returnAction);
        final int[] values = new int[] { 80, 90, 100, 110, 125, 150, 175, 200 };
        String[] labels = new String[values.length];
        int checked = 2;
        for (int i = 0; i < values.length; i++) { labels[i] = values[i] + "%"; if (values[i] == settings.textZoom()) checked = i; }
        new AlertDialog.Builder(this).setTitle("Zoom du texte").setSingleChoiceItems(labels, checked, new DialogInterface.OnClickListener() {
            @Override public void onClick(DialogInterface dialog, int which) {
                if (!host.equalsIgnoreCase(currentHost())) {
                    dialog.dismiss();
                    toast("La page a changé, veuillez rouvrir les paramètres du site");
                    return;
                }
                settings.textZoom(values[which]);
                siteSettingsStore.save(host, settings);
                applySiteSettings(webView, host);
                reloadWebView(webView);
                dialog.dismiss();
                continueSettingsPanel(returnAction);
            }
        }).setNegativeButton("Annuler", back).setOnCancelListener(back).show();
    }

    private void confirmClearCurrentSiteData() {
        final String url = currentPageUrl;
        final String host = currentHost();
        if (url == null || host.length() == 0) return;
        SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
            @Override public void run() { showSiteSettings(); }
        });
        new AlertDialog.Builder(this).setTitle("Effacer les données de ce site ?").setMessage("Les cookies et le stockage local de " + host + " seront supprimés ; vous pourrez être déconnecté du site.")
                .setPositiveButton("Effacer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        CookieManager cookies = CookieManager.getInstance();
                        String raw = cookies.getCookie(url);
                        if (raw != null) {
                            String[] pairs = raw.split(";");
                            for (String pair : pairs) {
                                int equals = pair.indexOf('=');
                                String name = (equals < 0 ? pair : pair.substring(0, equals)).trim();
                                if (name.length() > 0) {
                                    String expired = name + "=; Max-Age=0; Expires=Thu, 01 Jan 1970 00:00:00 GMT; Path=/";
                                    cookies.setCookie(url, expired);
                                    cookies.setCookie(url, expired + "; Secure");
                                    String domain = host;
                                    while (domain.indexOf('.') > 0) {
                                        cookies.setCookie(url, expired + "; Domain=" + domain);
                                        cookies.setCookie(url, expired + "; Domain=." + domain);
                                        cookies.setCookie(url, expired + "; Secure; Domain=." + domain);
                                        domain = domain.substring(domain.indexOf('.') + 1);
                                    }
                                }
                            }
                            cookies.flush();
                        }
                        Uri uri = null;
                        try { uri = Uri.parse(url); } catch (RuntimeException ignored) {}
                        if (uri != null) {
                            String origin = uri.getScheme() + "://" + uri.getAuthority();
                            android.webkit.WebStorage.getInstance().deleteOrigin(origin);
                            android.webkit.GeolocationPermissions.getInstance().clear(origin);
                        }
                        if (webView != null && host.equalsIgnoreCase(currentHost())) reloadWebView(webView);
                        toast("Les données de ce site ont été effacées");
                    }
                }).setNegativeButton("Annuler", back).setOnCancelListener(back).show();
    }

    private void startQrScan() {
        if (!requireStartupReady()) return;
        dismissOverlayForNavigation();
        showQrScannerPage();
    }

    private void showQrScannerPage() {
        if (webView == null) return;
        WebView source = webView;
        prepareHomeDestination(source);
        currentPageUrl = QR_URL;
        currentPageHost = "";
        pageHosts.put(source, "");
        qrScannerViews.add(source);
        trustedHomeViews.remove(source);
        customHomeViews.remove(source);
        renderedHomeKeys.remove(source);
        source.loadDataWithBaseURL(QR_URL, QrScannerPage.html(qrToken(), nightMode),
                "text/html", "UTF-8", QR_URL);
        updateCurrentTab(QR_URL, "Scanner un QR code");
        requestChromeUpdate();
    }

    private boolean handleQrScannerPrompt(final WebView source, String message, String value,
                                          JsPromptResult result) {
        if (!qrToken().equals(message)) return false;
        boolean accepted = result != null && source != null && source == webView &&
                isQrScannerUrl(source.getUrl()) && qrScannerViews.contains(source);
        if (result != null) result.confirm("");
        if (!accepted) return true;
        try {
            JSONObject payload = new JSONObject(value == null ? "{}" : value);
            if (payload.optBoolean("cancel", false)) {
                qrScannerViews.remove(source);
                source.post(new Runnable() {
                    @Override public void run() { returnFromQrScanner(); }
                });
            } else if (payload.optBoolean("external", false)) {
                qrScannerViews.remove(source);
                source.post(new Runnable() {
                    @Override public void run() {
                        if (!launchExternalQrScanner()) {
                            toast("Aucune application système ne peut retourner de résultat de scan ; retour au scan intégré");
                            showQrScannerPage();
                        }
                    }
                });
            } else {
                final String scanned = payload.optString("value", "").trim();
                if (scanned.length() == 0 || scanned.length() > 16 * 1024) {
                    toast("Le contenu du QR code est vide ou anormalement long");
                    source.post(new Runnable() {
                        @Override public void run() { if (source == webView) showQrScannerPage(); }
                    });
                } else {
                    qrScannerViews.remove(source);
                    source.post(new Runnable() {
                        @Override public void run() { showQrResult(scanned); }
                    });
                }
            }
        } catch (Exception error) {
            toast("Impossible de lire le résultat du scan");
            if (source != null) source.post(new Runnable() {
                @Override public void run() { if (source == webView) showQrScannerPage(); }
            });
        }
        return true;
    }

    private boolean launchExternalQrScanner() {
        String[] actions = new String[] {
                "com.google.zxing.client.android.SCAN",
                "com.srowen.bs.android.SCAN"
        };
        for (String action : actions) {
            Intent scan = new Intent(action);
            scan.putExtra("SCAN_MODE", "QR_CODE_MODE");
            scan.putExtra("PROMPT_MESSAGE", "Scanner un QR code");
            try {
                startActivityForResult(scan, QR_SCAN_REQUEST);
                return true;
            } catch (Exception ignored) {}
        }
        return false;
    }

    private void showQrResult(final String value) {
        String preview = value.replace('\n', ' ').replace('\r', ' ');
        preview = UiText.ellipsize(preview, 180);
        final boolean link = isHttpUrl(value);
        String[] items = link
                ? new String[] { "Ouvrir le lien", "Ouvrir dans un nouvel onglet", "Copier le contenu", "Rechercher avec un moteur de recherche" }
                : new String[] { "Rechercher avec un moteur de recherche", "Copier le contenu", "Scanner à nouveau" };
        int[] icons = link
                ? new int[] { BrowserIconView.SEARCH, BrowserIconView.PLUS,
                        BrowserIconView.SHARE, BrowserIconView.SEARCH }
                : new int[] { BrowserIconView.SEARCH, BrowserIconView.SHARE, BrowserIconView.QR };
        final Runnable rescan = new Runnable() {
            @Override public void run() { showQrScannerPage(); }
        };
        showActionSheet("Contenu du QR code", preview, items, icons, null, null, rescan, rescan, new SheetHandler() {
            @Override public void onItem(int which) {
                if (link && which == 0) loadInput(value);
                else if (link && which == 1) openUrlInNewTab(value, true);
                else if ((link && which == 2) || (!link && which == 1)) {
                    ClipboardManager manager = (ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
                    if (manager != null) manager.setPrimaryClip(ClipData.newPlainText("Contenu du QR code", value));
                    toast("Contenu du QR code copié");
                    returnFromQrScanner();
                } else if (!link && which == 2) {
                    showQrScannerPage();
                } else {
                    loadInput(value);
                }
            }
        });
    }

    private void returnFromQrScanner() {
        if (webView == null) return;
        qrScannerViews.remove(webView);
        if (isQrScannerUrl(webView.getUrl()) && webView.canGoBack()) goBackWebView(webView);
        else if (isQrScannerUrl(webView.getUrl())) showHome();
    }

    private void resumeQrScannerIfNeeded() {
        if (webView == null || !isQrScannerUrl(webView.getUrl()) || !qrScannerViews.contains(webView)) return;
        try { webView.evaluateJavascript("window.__medianRestartScanner&&window.__medianRestartScanner();", null); }
        catch (RuntimeException ignored) {}
    }

    private void showPageTools() {
        if (isInternalBrowserUrl(currentPageUrl)) { toast("Aucun outil de page pour la page actuelle"); return; }
        int offlineCount = services.offlinePages().getAll().size();
        PageAssistant assistant = services.assistant();
        String[] items = new String[] {
                "Rechercher dans la page", "Basculer en mode lecture immersif", assistant.isSpeaking() ? "Arrêter la lecture" : "Lire le contenu à voix haute",
                "Structure et statistiques de la page", "Certificat TLS et SHA-256", "Enregistrer la page hors ligne complète", "Bibliothèque de pages hors ligne · " + offlineCount + " pages",
                "Partager la page actuelle", "Copier l'adresse de la page", "Copier l'adresse sans paramètres de suivi", "Traduire en français",
                "Imprimer ou enregistrer en PDF", "Centre multimédia · " + mediaSniffer.size() + " élément(s)", "Commandes de script de la page",
                "Ouvrir dans le navigateur système\nUtile pour les connexions avec Passkey ou identifiants système",
                "Replier la barre d'outils\nNavigation plein écran, glissez vers le bas pour réafficher"
        };
        int[] icons = new int[] { BrowserIconView.SEARCH, BrowserIconView.INFO, BrowserIconView.SPEED, BrowserIconView.INFO,
                BrowserIconView.SHIELD, BrowserIconView.STORAGE, BrowserIconView.STORAGE, BrowserIconView.SHARE, BrowserIconView.PLUS,
                BrowserIconView.SHIELD, BrowserIconView.INFO, BrowserIconView.STORAGE,
                BrowserIconView.SPEED, BrowserIconView.SCRIPT, BrowserIconView.PLUS, BrowserIconView.APPEARANCE };
        showActionSheet("Outils de page", currentHost(), items, icons, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) showFindDialog();
                else if (which == 1) toggleReaderMode();
                else if (which == 2) toggleReadAloud();
                else if (which == 3) showPageInfo();
                else if (which == 4) showTlsInfo();
                else if (which == 5) saveOfflinePage();
                else if (which == 6) showOfflinePages();
                else if (which == 7) sharePage();
                else if (which == 8) copyPageUrl();
                else if (which == 9) copyCleanPageUrl();
                else if (which == 10) translatePage();
                else if (which == 11) printPage();
                else if (which == 12) probeAndShowMediaCenter();
                else if (which == 13) showPageScriptCommands();
                else if (which == 14) openCurrentPageInSystemBrowser();
                else {
                    immersiveScrollChrome = true;
                    prefs.edit().putBoolean("immersive_scroll_chrome", true).apply();
                    updateImmersivePageLayout();
                    hideBrowserChrome();
                }
            }
        });
    }

    private void openCurrentPageInSystemBrowser() {
        if (!isNetworkPage(currentPageUrl)) { toast("Aucune page web ouvrable sur cette page"); return; }
        try {
            Intent intent = new Intent(Intent.ACTION_VIEW, Uri.parse(currentPageUrl));
            intent.addCategory(Intent.CATEGORY_BROWSABLE);
            startActivity(intent);
        } catch (Exception e) { toast("Aucun navigateur système disponible"); }
    }

    private void toggleReaderMode() {
        if (webView == null || !isNetworkPage(currentPageUrl)) { toast("Cette page ne prend pas en charge le mode lecture"); return; }
        final WebView source = webView;
        final long sequence = navigationSequence;
        services.assistant().toggleReader(source, nightMode, new PageAssistant.Callback<String>() {
            @Override public void onResult(String value, Exception error) {
                if (!isCurrentPageCallback(source, sequence)) return;
                if (error != null) toast("Échec du mode lecture : " + safeMessage(error));
                else if ("none".equals(value)) toast("Aucun contenu suffisamment long détecté");
                else toast("on".equals(value) ? "Mode lecture activé" : "Mode lecture désactivé");
            }
        });
    }

    private void toggleReadAloud() {
        final PageAssistant assistant = services.assistant();
        if (assistant.isSpeaking()) { assistant.stop(); toast("Lecture arrêtée"); return; }
        final WebView source = webView;
        final long sequence = navigationSequence;
        assistant.speak(source, new PageAssistant.Callback<Boolean>() {
            @Override public void onResult(Boolean value, Exception error) {
                if (!isCurrentPageCallback(source, sequence)) {
                    assistant.stop();
                    return;
                }
                if (error == null && Boolean.TRUE.equals(value)) toast("Lecture du texte démarrée");
                else toast(error == null ? "Impossible de démarrer la lecture" : "Échec de la lecture : " + safeMessage(error));
            }
        });
    }

    private void showPageInfo() {
        if (webView == null) return;
        final WebView source = webView;
        final long sequence = navigationSequence;
        services.assistant().pageInfo(source, new PageAssistant.Callback<JSONObject>() {
            @Override public void onResult(JSONObject info, Exception error) {
                if (!isCurrentPageCallback(source, sequence)) return;
                if (error != null || info == null) { toast("Impossible d'analyser la page"); return; }
                new AlertDialog.Builder(MainActivity.this).setTitle("Informations sur la page")
                        .setMessage("Titre : " + info.optString("title", "") +
                                "\nLangue : " + info.optString("lang", "Non déclaré") +
                                "\nEncodage : " + info.optString("charset", "") +
                                "\nCaractères : " + info.optLong("characters", 0L) +
                                "\nMots (estimation) : " + info.optLong("words", 0L) +
                                "\nLiens : " + info.optInt("links", 0) +
                                "\nImages : " + info.optInt("images", 0) +
                                "\nFormulaires : " + info.optInt("forms", 0) +
                                "\nScripts : " + info.optInt("scripts", 0) + "\n\n" + info.optString("url", ""))
                        .setPositiveButton("OK", null).show();
            }
        });
    }

    private void showTlsInfo() {
        final String url = currentPageUrl;
        final WebView source = webView;
        final long sequence = navigationSequence;
        if (url == null || !url.regionMatches(true, 0, "https://", 0, 8) ||
                scriptExecutor == null || scriptExecutor.isShutdown()) {
            toast("La page actuelle n'est pas une page HTTPS vérifiable");
            return;
        }
        final String userAgent = source == null ? null : source.getSettings().getUserAgentString();
        toast("Sondage indépendant du certificat du serveur (le résultat ne reflète pas la réponse de chargement de la page)…");
        executeTask(scriptExecutor, new Runnable() {
            @Override public void run() {
                TlsInspector.Result value = null;
                Exception failure = null;
                try { value = TlsInspector.inspect(url, userAgent); } catch (Exception e) { failure = e; }
                final TlsInspector.Result result = value;
                final Exception error = failure;
                uiHandler.post(new Runnable() {
                    @Override public void run() {
                        if (!isCurrentPageCallback(source, sequence) || !url.equals(currentPageUrl)) return;
                        if (error != null) { toast("Échec de la vérification du certificat : " + safeMessage(error)); return; }
                        new AlertDialog.Builder(MainActivity.this).setTitle("Certificat TLS")
                                .setMessage(result.summary()).setPositiveButton("OK", null).show();
                    }
                });
            }
        });
    }

    private void saveOfflinePage() {
        if (webView == null || !isNetworkPage(currentPageUrl)) { toast("Seules les pages HTTP(S) peuvent être enregistrées"); return; }
        toast("Enregistrement de la page hors ligne complète…");
        services.offlinePages().save(webView, webView.getTitle(), currentPageUrl, new OfflinePageStore.Callback() {
            @Override public void onComplete(OfflinePageStore.Entry entry, Exception error) {
                if (activityDestroyed) return;
                toast(error == null ? "Page hors ligne enregistrée · " + humanBytes(entry.size) : "Échec de l'enregistrement : " + safeMessage(error));
            }
        });
    }

    private void showOfflinePages() {
        final List<OfflinePageStore.Entry> entries = services.offlinePages().getAll();
        if (entries.size() == 0) { toast("Aucune page hors ligne"); return; }
        String[] labels = new String[entries.size()];
        for (int i = 0; i < entries.size(); i++) {
            OfflinePageStore.Entry entry = entries.get(i);
            labels[i] = safeTitle(entry.title, entry.url) + " · " + humanBytes(entry.size) + "\n" + hostOf(entry.url);
        }
        new AlertDialog.Builder(this).setTitle("Pages hors ligne").setItems(labels, new DialogInterface.OnClickListener() {
            @Override public void onClick(DialogInterface dialog, int which) { showOfflineActions(entries.get(which)); }
        }).setNegativeButton("Retour", new DialogInterface.OnClickListener() {
            @Override public void onClick(DialogInterface dialog, int which) { showBrowserLibrary(); }
        }).setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface dialog) { showBrowserLibrary(); }
        }).show();
    }

    private void showOfflineActions(final OfflinePageStore.Entry entry) {
        String[] items = new String[] { "Ouvrir hors ligne", "Ouvrir la page web d'origine", "Partager le fichier archivé", "Supprimer la page hors ligne" };
        showActionSheet(entry.title, entry.url, items, new int[] { BrowserIconView.PLUS, BrowserIconView.RELOAD,
                BrowserIconView.SHARE, BrowserIconView.CLOSE }, null, null,
                new Runnable() { @Override public void run() { showOfflinePages(); } }, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) {
                    String offlineUrl = services.offlinePages().uriFor(entry).toString();
                    prepareOfflineDestination(webView, offlineUrl);
                    webView.loadUrl(offlineUrl);
                }
                else if (which == 1) loadInput(entry.url);
                else if (which == 2) {
                    Intent share = new Intent(Intent.ACTION_SEND);
                    share.setType("application/x-mimearchive");
                    share.putExtra(Intent.EXTRA_STREAM, services.offlinePages().uriFor(entry));
                    share.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION);
                    try { startActivity(Intent.createChooser(share, "Partager la page hors ligne")); }
                    catch (Exception e) { toast("Aucune application de partage disponible"); }
                } else {
                    confirmDeleteOfflinePage(entry);
                }
            }
        });
    }

    private void confirmDeleteOfflinePage(final OfflinePageStore.Entry entry) {
        new AlertDialog.Builder(this).setTitle("Supprimer la page hors ligne ?").setMessage(entry.title)
                .setPositiveButton("Supprimer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        services.offlinePages().remove(entry.file);
                        toast("Page hors ligne supprimée");
                        if (services.offlinePages().getAll().isEmpty()) showBrowserLibrary();
                        else showOfflinePages();
                    }
                }).setNegativeButton("Annuler", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) { showOfflineActions(entry); }
                }).setOnCancelListener(new DialogInterface.OnCancelListener() {
                    @Override public void onCancel(DialogInterface dialog) { showOfflineActions(entry); }
                }).show();
    }

    private void copyCleanPageUrl() {
        String url = currentPageUrl;
        if (url == null || !isNetworkPage(url)) return;
        String cleaned = UrlCleaner.cleanTracking(url);
        android.content.ClipboardManager manager = (android.content.ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
        if (manager != null) manager.setPrimaryClip(android.content.ClipData.newPlainText("Adresse sans paramètres de suivi", cleaned));
        toast(url.equals(cleaned) ? "Aucun paramètre de suivi connu dans l'adresse" : "Adresse nettoyée copiée");
    }

    @Override public void run() { showBrowserSettings(); }

    private void showBrowserSettings() {
        startupSessionPending = false;
        String[] items = new String[] {
                "Blocage de publicités\n" + (adBlockEnabled ? "Activé" : "Désactivé"),
                "Mode sombre\n" + (nightMode ? "Activé" : "Désactivé"),
                "Navigation par glissement latéral\n" + (edgeNavigationEnabled ? "Activé" : "Désactivé"),
                "Marquer la publicité de la page\n" + (isNetworkPage(currentPageUrl) ? "Touchez pour masquer les éléments de la page" : "Veuillez d'abord ouvrir une page web"),
                "Navigation et recherche\nConnexion, démarrage et barre d'adresse",
                "Accueil et apparence\nPage d'accueil, mise en page et thème",
                "Scripts et blocage\nFiltres, règles et scripts",
                "Confidentialité et mots de passe\nCoffre, autorisations et données",
                "Paramètres de téléchargement\nDossier et politique de téléchargement",
                "Mode de performance\nActuel : " + modeLabel(),
                "À propos de Median\nInformations de version et communauté"
        };
        int[] icons = new int[] {
                BrowserIconView.SHIELD, BrowserIconView.APPEARANCE, BrowserIconView.BACK,
                BrowserIconView.CLEAN, BrowserIconView.SEARCH, BrowserIconView.HOME,
                BrowserIconView.SCRIPT, BrowserIconView.KEY, BrowserIconView.DOWNLOAD,
                BrowserIconView.SPEED, BrowserIconView.INFO
        };
        int[] kinds = new int[] {
                adBlockEnabled ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                nightMode ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                edgeNavigationEnabled ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                SHEET_ROW_ACTION,
                SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE,
                SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE,
                SHEET_ROW_NAVIGATE
        };
        showDashboardSheet("Paramètres", "Interrupteurs fréquents et paramètres par catégorie", items, icons, kinds, 2,
                new int[] { 0, 4, 10 }, new String[] { "Actions fréquentes", "Catégories de paramètres", "Autres" }, new Runnable() {
            @Override public void run() { showMainMenu(); }
        }, null, null, 0, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) {
                    adBlockEnabled = !adBlockEnabled;
                    prefs.edit().putBoolean("adblock", adBlockEnabled).apply();
                    adBlockActiveByView.clear();
                    if (webView != null && isNetworkPage(currentPageUrl)) reloadWebView(webView);
                    toast(adBlockEnabled ? "Blocage de publicités activé" : "Blocage de publicités désactivé");
                    showBrowserSettings();
                } else if (which == 3) {
                    if (!isNetworkPage(currentPageUrl)) {
                        toast("Veuillez d'abord ouvrir une page web normale avant de marquer la publicité");
                        showBrowserSettings();
                        return;
                    }
                    startAdPicker();
                } else if (which == 1) {
                    toggleNightMode();
                    // Keep the settings dashboard in place after a live theme switch so the
                    // user can continue adjusting options without reopening the menu.
                    showBrowserSettings();
                }
                else if (which == 2) {
                    edgeNavigationEnabled = !edgeNavigationEnabled;
                    prefs.edit().putBoolean("edge_navigation", edgeNavigationEnabled).apply();
                    toast(edgeNavigationEnabled ? "Gestures en bord de page activés" : "Gestures en bord de page désactivés");
                    showBrowserSettings();
                } else if (which == 4) showBrowsingSettings();
                else if (which == 5) showHomeCustomization(MainActivity.this);
                else if (which == 6) showExtensionSettings();
                else if (which == 7) showPrivacyDataSettings();
                else if (which == 8) showDownloadSettings();
                else if (which == 9) showPerformancePanel(MainActivity.this);
                else showAbout(MainActivity.this);
            }
        });
    }

    private void showBrowsingSettings() {
        String[] items = new String[] {
                "HTTPS prioritaire",
                "Nettoyer les paramètres de suivi",
                "Cookies tiers",
                "Au démarrage\n" + homeOpenBehaviorLabel(),
                "Recherche par défaut\n" + searchEngineLabel(),
                "Barre de défilement immersive\nGlissez vers le bas pour masquer les barres, vers le haut pour les afficher"
        };
        int[] icons = new int[] { BrowserIconView.SHIELD, BrowserIconView.CLEAN,
                BrowserIconView.COOKIE, BrowserIconView.STARTUP, BrowserIconView.SEARCH, BrowserIconView.APPEARANCE };
        int[] kinds = new int[] {
                httpsOnly ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                cleanTrackingParameters ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                acceptThirdPartyCookies ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE,
                immersiveScrollChrome ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF
        };
        showActionSheet("Navigation et recherche", "Connexion, démarrage et barre d'adresse", items, icons, kinds, null,
                this, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) {
                            httpsOnly = !httpsOnly;
                            prefs.edit().putBoolean("https_only", httpsOnly).apply();
                        } else if (which == 1) {
                            cleanTrackingParameters = !cleanTrackingParameters;
                            prefs.edit().putBoolean("clean_tracking_parameters", cleanTrackingParameters).apply();
                        } else if (which == 2) {
                            acceptThirdPartyCookies = !acceptThirdPartyCookies;
                            prefs.edit().putBoolean("accept_third_party_cookies", acceptThirdPartyCookies).apply();
                            applyCookiePolicyToAll();
                            toast(acceptThirdPartyCookies ? "Cookies tiers autorisés globalement" :
                                    "Cookies tiers bloqués par défaut, autorisables par site");
                        } else if (which == 3) showHomeOpenBehaviorChoice(false);
                        else if (which == 4) showSearchSettings();
                        else {
                            immersiveScrollChrome = !immersiveScrollChrome;
                            prefs.edit().putBoolean("immersive_scroll_chrome", immersiveScrollChrome).apply();
                            updateImmersivePageLayout();
                            if (!immersiveScrollChrome) showBrowserChrome(false);
                            toast(immersiveScrollChrome ? "Barre de défilement immersive activée" : "Barre de défilement immersive désactivée");
                        }
                    }
                });
    }

    private void showExtensionSettings() {
        String[] items = new String[] {
                "Blocage de publicités",
                "Bloquer manuellement des éléments de page",
                "Abonnements de filtres et règles",
                "Scripts utilisateur"
        };
        int[] icons = new int[] { BrowserIconView.SHIELD, BrowserIconView.CLEAN,
                BrowserIconView.STORAGE, BrowserIconView.SCRIPT };
        int[] kinds = new int[] { adBlockEnabled ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF,
                SHEET_ROW_ACTION, SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE };
        showActionSheet("Scripts et blocage de publicités", "Les règles et les scripts sont traités localement", items, icons,
                kinds, null, this, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) {
                            adBlockEnabled = !adBlockEnabled;
                            prefs.edit().putBoolean("adblock", adBlockEnabled).apply();
                            adBlockActiveByView.clear();
                            if (webView != null && isNetworkPage(currentPageUrl)) reloadWebView(webView);
                            toast(adBlockEnabled ? "Blocage de publicités activé" : "Blocage de publicités désactivé");
                        } else if (which == 1) {
                            if (!isNetworkPage(currentPageUrl)) {
                                toast("Veuillez d'abord ouvrir une page web normale avant de marquer la publicité");
                                showExtensionSettings();
                            } else startAdPicker();
                        }
                        else if (which == 2) showFilterCenter(new Runnable() {
                            @Override public void run() { showExtensionSettings(); }
                        });
                        else showScriptCenter(new Runnable() {
                            @Override public void run() { showExtensionSettings(); }
                        });
                    }
                });
    }

    private void showPrivacyDataSettings() {
        String host = currentHost();
        String[] items = new String[] {
                "Autorisations du site actuel\n" + (host.length() == 0 ? "Veuillez d'abord ouvrir une page web" : host),
                "Coffre de mots de passe",
                "Signets et historique",
                "Stockage et données",
                "Nouvelle fenêtre privée",
                "Nettoyer les données de navigation à la fermeture\nSans supprimer les signets, mots de passe, téléchargements et scripts"
        };
        int[] icons = new int[] { BrowserIconView.SHIELD, BrowserIconView.KEY,
                BrowserIconView.HISTORY, BrowserIconView.STORAGE, BrowserIconView.SHIELD, BrowserIconView.CLOSE };
        int[] kinds = new int[] { SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE,
                SHEET_ROW_NAVIGATE, SHEET_ROW_NAVIGATE,
                clearDataOnExit ? SHEET_ROW_TOGGLE_ON : SHEET_ROW_TOGGLE_OFF };
        showActionSheet("Confidentialité et données", "Local d'abord", items, icons,
                kinds, null, this, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) showSiteSettings();
                        else if (which == 1) showPasswordMenu(new Runnable() {
                            @Override public void run() { showPrivacyDataSettings(); }
                        });
                        else if (which == 2) showBrowserLibrary();
                        else if (which == 3) showStoragePanel(MainActivity.this);
                        else if (which == 4) openPrivateWindow();
                        else {
                            clearDataOnExit = !clearDataOnExit;
                            prefs.edit().putBoolean("clear_data_on_exit", clearDataOnExit).apply();
                            toast(clearDataOnExit ? "Les données de navigation seront nettoyées à la fermeture" : "Les données de navigation ne seront pas nettoyées automatiquement à la fermeture");
                        }
                    }
                });
    }

    private void showSearchSettings() {
        int customCount = searchEngines.customEngines().size();
        String[] items = new String[] {
                "Moteur de recherche par défaut\nActuel : " + searchEngineLabel(),
                "Gérer les moteurs de recherche personnalisés\nEnregistrés : " + customCount + ""
        };
        int[] icons = new int[] { BrowserIconView.SEARCH, BrowserIconView.SETTINGS };
        final Runnable returnHere = new Runnable() {
            @Override public void run() { showSearchSettings(); }
        };
        showActionSheet("Paramètres de recherche", "Partagé entre la barre d'adresse et la page d'accueil", items, icons,
                null, null, this, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) showSearchEngineDialog(returnHere);
                        else showCustomSearchList(returnHere);
                    }
                });
    }

    private void showHomeCustomization() {
        showHomeCustomization(new Runnable() {
            @Override public void run() { showMainMenu(); }
        });
    }

    private void showHomeCustomization(Runnable backAction) {
        homeCustomization().show(backAction);
    }

    /** Appearance editing is lazy and does not participate in first-page startup. */
    private HomeCustomizationController homeCustomization() {
        if (homeCustomizationController == null) {
            homeCustomizationController = new HomeCustomizationController(this, prefs, homeImages, uiHandler,
                    new HomeCustomizationController.TaskQueue() {
                        @Override public boolean isAvailable() {
                            return scriptExecutor != null && !scriptExecutor.isShutdown();
                        }
                        @Override public boolean execute(Runnable task) { return executeTask(scriptExecutor, task); }
                    }, new HomeCustomizationController.Host() {
                        @Override public HomePageConfig homePageConfig() { return MainActivity.this.homePageConfig(); }
                        @Override public boolean isNightMode() { return nightMode; }
                        @Override public void refreshHomeIfVisible() {
                            if (isHomeUrl(currentPageUrl)) showHome();
                        }
                        @Override public void toast(String message) { MainActivity.this.toast(message); }
                        @Override public void postAfterUiTransition(Runnable action) {
                            MainActivity.this.postAfterUiTransition(action);
                        }
                        @Override public void showActionSheet(String title, String subtitle, String[] items, int[] icons,
                                Runnable backAction, final HomeCustomizationController.SheetHandler handler) {
                            MainActivity.this.showActionSheet(title, subtitle, items, icons, null, null, backAction,
                                    new SheetHandler() {
                                        @Override public void onItem(int which) { handler.onItem(which); }
                                    });
                        }
                        @Override public String searchEngineLabel() { return MainActivity.this.searchEngineLabel(); }
                        @Override public void showSearchEngineDialog(Runnable action) {
                            MainActivity.this.showSearchEngineDialog(action);
                        }
                        @Override public void openBookmarkManager(Runnable action) {
                            MainActivity.this.openBookmarkManager(action);
                        }
                        @Override public String homeOpenBehaviorLabel() { return MainActivity.this.homeOpenBehaviorLabel(); }
                        @Override public void showHomeOpenBehaviorChoice() {
                            MainActivity.this.showHomeOpenBehaviorChoice(true);
                        }
                    });
        }
        return homeCustomizationController;
    }

    private void showHomeOpenBehaviorChoice() { showHomeOpenBehaviorChoice(false); }

    private void showHomeOpenBehaviorChoice(final boolean returnToCustomization) {
        HomeOpenDialogReturn back = new HomeOpenDialogReturn(returnToCustomization);
        final String[] modes = new String[] { HomeOpenPolicy.OPEN_HOME, HomeOpenPolicy.OPEN_CUSTOM_URL,
                HomeOpenPolicy.KEEP_LAST };
        String[] labels = new String[] {
                "Ouvrir la page d'accueil",
                "Ouvrir une page personnalisée",
                "Restaurer les onglets de la dernière session"
        };
        int checked = 0;
        String current = homeOpenMode();
        for (int i = 0; i < modes.length; i++) if (modes[i].equals(current)) checked = i;
        new AlertDialog.Builder(this).setTitle("À chaque ouverture").setSingleChoiceItems(labels, checked,
                new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        dialog.dismiss();
                        if (HomeOpenPolicy.OPEN_CUSTOM_URL.equals(modes[which])) {
                            showCustomHomeUrlEditor(returnToCustomization);
                            return;
                        }
                        restoreTabs = HomeOpenPolicy.KEEP_LAST.equals(modes[which]);
                        prefs.edit().putString("home_open_mode", modes[which])
                                .putBoolean("restore_tabs", restoreTabs).apply();
                        toast(restoreTabs ? "Le contenu de la dernière session sera restauré au prochain démarrage" : "La page d'accueil sera ouverte");
                        continueHomeOpenSettings(returnToCustomization);
                    }
                }).setNegativeButton("Annuler", back).setOnCancelListener(back).show();
    }

    private void showCustomHomeUrlEditor(final boolean returnToCustomization) {
        final EditText input = new EditText(this);
        final HomeOpenDialogReturn back = new HomeOpenDialogReturn(returnToCustomization);
        input.setSingleLine(true);
        input.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_URI);
        input.setHint("Exemple : www.example.com");
        input.setText(prefs.getString("home_custom_url", ""));
        input.setSelectAllOnFocus(true);
        input.setPadding(dp(16), dp(8), dp(16), dp(8));
        final AlertDialog dialog = new AlertDialog.Builder(this).setTitle("Page personnalisée")
                .setMessage("Utilisé pour le bouton Accueil, le démarrage à froid et les nouveaux onglets ; HTTPS est utilisé si aucun protocole n'est indiqué.")
                .setView(input).setPositiveButton("Enregistrer et utiliser", null)
                .setNegativeButton("Annuler", back).create();
        dialog.setOnCancelListener(back);
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View view) {
                        String normalized = normalizeConfiguredHomeUrl(input.getText().toString());
                        if (normalized.length() == 0) { toast("Veuillez saisir une adresse web HTTP ou HTTPS valide"); return; }
                        boolean saved = prefs.edit().putString("home_open_mode", HomeOpenPolicy.OPEN_CUSTOM_URL)
                                .putString("home_custom_url", normalized).putBoolean("restore_tabs", false).commit();
                        if (!saved) { toast("Échec de l'enregistrement des paramètres de la page d'accueil"); return; }
                        restoreTabs = false;
                        dialog.dismiss();
                        toast("La page personnalisée a été définie comme page d'accueil");
                        continueHomeOpenSettings(returnToCustomization);
                    }
                });
            }
        });
        dialog.show();
    }

    private void continueHomeOpenSettings(boolean returnToCustomization) {
        if (returnToCustomization) continueHomeCustomization();
        else continueSettingsPanel(this);
    }


    private void continueHomeCustomization() {
        homeCustomization().continueCustomization();
    }

    private void continueSettingsPanel(final Runnable action) {
        if (action == null) return;
        postAfterUiTransition(new Runnable() {
            @Override public void run() {
                if (isFinishing() || isDestroyed()) return;
                action.run();
            }
        });
    }

    private void postAfterUiTransition(Runnable action) {
        if (action == null) return;
        final View target = rootFrame;
        if (target == null) {
            uiHandler.post(action);
        } else if (target.isAttachedToWindow()) {
            target.postOnAnimation(action);
        } else {
            // onResume is invoked before WindowManager necessarily attaches the decor view. A
            // plain Handler.post here can still run before the first traversal and lets vendor
            // WebView providers drop the initial load. Cross the attach boundary and one frame.
            final Runnable pending = action;
            target.addOnAttachStateChangeListener(new View.OnAttachStateChangeListener() {
                @Override public void onViewAttachedToWindow(View view) {
                    view.removeOnAttachStateChangeListener(this);
                    view.postOnAnimation(pending);
                }
                @Override public void onViewDetachedFromWindow(View view) {}
            });
        }
    }

    private void showSearchEngineDialog() {
        showSearchEngineDialog(this);
    }

    private void showSearchEngineDialog(final Runnable returnAction) {
        SettingsDialogReturn back = new SettingsDialogReturn(returnAction);
        final List<SearchEngineStore.Engine> custom = searchEngines.customEngines();
        final String[] values = new String[custom.size() + 4];
        final String[] labels = new String[values.length];
        values[0] = "google"; labels[0] = "Google";
        values[1] = "baidu"; labels[1] = "Baidu";
        values[2] = "bing"; labels[2] = "Bing";
        for (int i = 0; i < custom.size(); i++) {
            values[i + 3] = custom.get(i).id;
            labels[i + 3] = custom.get(i).name;
        }
        values[values.length - 1] = "";
        labels[labels.length - 1] = "＋ Ajouter un moteur de recherche personnalisé";
        int checked = -1;
        for (int i = 0; i < values.length - 1; i++) if (values[i].equals(searchEngine)) checked = i;
        new AlertDialog.Builder(this).setTitle("Moteur de recherche par défaut").setSingleChoiceItems(labels, checked, new DialogInterface.OnClickListener() {
            @Override public void onClick(DialogInterface dialog, int which) {
                if (which == values.length - 1) {
                    dialog.dismiss();
                    showCustomSearchEditor(null, returnAction);
                    return;
                }
                setSearchEngine(values[which]);
                dialog.dismiss();
                if (isHomeUrl(currentPageUrl)) showHome();
                continueSettingsPanel(returnAction);
            }
        }).setNegativeButton("Annuler", back).setOnCancelListener(back).show();
    }

    private void showCustomSearchList(final Runnable returnAction) {
        final List<SearchEngineStore.Engine> engines = searchEngines.customEngines();
        String[] labels = new String[engines.size() + 1];
        for (int i = 0; i < engines.size(); i++) {
            SearchEngineStore.Engine item = engines.get(i);
            labels[i] = item.name + (item.id.equals(searchEngine) ? " · par défaut" : "") + "\n" + item.template;
        }
        labels[labels.length - 1] = "＋ Ajouter un moteur de recherche";
        new AlertDialog.Builder(this).setTitle("Moteurs de recherche personnalisés").setItems(labels, new DialogInterface.OnClickListener() {
            @Override public void onClick(DialogInterface dialog, int which) {
                if (which == engines.size()) showCustomSearchEditor(null, returnAction);
                else showCustomSearchActions(engines.get(which), returnAction);
            }
        }).setNegativeButton("Retour", new DialogInterface.OnClickListener() {
            @Override public void onClick(DialogInterface dialog, int which) { continueSettingsPanel(returnAction); }
        }).setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface dialog) { continueSettingsPanel(returnAction); }
        }).show();
    }

    private void showCustomSearchActions(final SearchEngineStore.Engine engine, final Runnable returnAction) {
        String[] actions = new String[] { "Définir par défaut", "Renommer ou modifier l'adresse", "Supprimer" };
        new AlertDialog.Builder(this).setTitle(engine.name).setItems(actions, new DialogInterface.OnClickListener() {
            @Override public void onClick(DialogInterface dialog, int which) {
                if (which == 0) {
                    setSearchEngine(engine.id);
                    if (isHomeUrl(currentPageUrl)) showHome();
                    showCustomSearchList(returnAction);
                } else if (which == 1) {
                    showCustomSearchEditor(engine, returnAction);
                } else {
                    confirmDeleteSearchEngine(engine, returnAction);
                }
            }
        }).setNegativeButton("Retour", new DialogInterface.OnClickListener() {
            @Override public void onClick(DialogInterface dialog, int which) { showCustomSearchList(returnAction); }
        }).setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface dialog) { showCustomSearchList(returnAction); }
        }).show();
    }

    private void confirmDeleteSearchEngine(final SearchEngineStore.Engine engine, final Runnable returnAction) {
        new AlertDialog.Builder(this).setTitle("Supprimer le moteur de recherche ?").setMessage(engine.name)
                .setPositiveButton("Supprimer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        searchEngines.delete(engine.id);
                        if (engine.id.equals(searchEngine)) setSearchEngine("google");
                        cachedHomeKey = "";
                        if (isHomeUrl(currentPageUrl)) showHome();
                        showCustomSearchList(returnAction);
                    }
                }).setNegativeButton("Annuler", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        showCustomSearchActions(engine, returnAction);
                    }
                }).setOnCancelListener(new DialogInterface.OnCancelListener() {
                    @Override public void onCancel(DialogInterface dialog) {
                        showCustomSearchActions(engine, returnAction);
                    }
                }).show();
    }

    private void showCustomSearchEditor(final SearchEngineStore.Engine existing, final Runnable returnAction) {
        final EditText name = new EditText(this);
        name.setHint("Nom, par exemple DuckDuckGo");
        name.setSingleLine(true);
        name.setText(existing == null ? "" : existing.name);
        final EditText address = new EditText(this);
        address.setHint("https://example.com/search?q=%s");
        address.setText(existing == null ? "" : existing.template);
        address.setSingleLine(true);
        address.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_URI);
        LinearLayout fields = new LinearLayout(this);
        fields.setOrientation(LinearLayout.VERTICAL);
        fields.setPadding(dp(18), 0, dp(18), 0);
        fields.addView(name);
        fields.addView(address);
        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle(existing == null ? "Ajouter un moteur de recherche" : "Modifier le moteur de recherche")
                .setMessage("Utilisez %s pour le terme de recherche encodé ; adresses HTTPS uniquement.")
                .setView(fields).setPositiveButton(existing == null ? "Enregistrer et utiliser" : "Enregistrer", null)
                .setNegativeButton("Annuler", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface ignored, int which) { showCustomSearchList(returnAction); }
                }).create();
        dialog.setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface ignored) { showCustomSearchList(returnAction); }
        });
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View view) {
                        String label = name.getText().toString().trim();
                        String template = address.getText().toString().trim();
                        if (label.length() == 0) { toast("Veuillez saisir le nom du moteur de recherche"); return; }
                        if (!SearchEngineStore.validTemplate(template)) { toast("L'adresse doit commencer par https:// et contenir %s"); return; }
                        SearchEngineStore.Engine saved = existing == null
                                ? searchEngines.add(label, template)
                                : searchEngines.update(existing.id, label, template);
                        if (saved == null) { toast("Impossible d'enregistrer le moteur de recherche"); return; }
                        if (existing == null) setSearchEngine(saved.id);
                        cachedHomeKey = "";
                        if (isHomeUrl(currentPageUrl)) showHome();
                        dialog.dismiss();
                        showCustomSearchList(returnAction);
                    }
                });
            }
        });
        dialog.show();
    }

    private void copyText(String label, String text, String confirmation) {
        android.content.ClipboardManager manager = (android.content.ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
        if (manager == null) { toast("Presse-papiers indisponible"); return; }
        manager.setPrimaryClip(android.content.ClipData.newPlainText(label == null ? "Median" : label, text == null ? "" : text));
        toast(confirmation == null || confirmation.length() == 0 ? "Copié" : confirmation);
    }

    private void copyPageUrl() {
        String url = webView == null ? null : webView.getUrl();
        if (!isNetworkPage(url)) return;
        android.content.ClipboardManager manager = (android.content.ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
        if (manager != null) manager.setPrimaryClip(android.content.ClipData.newPlainText("Adresse de la page", url));
        toast("Adresse de la page copiée");
    }

    private void translatePage() {
        String url = webView == null ? null : webView.getUrl();
        if (!isNetworkPage(url)) return;
        try { loadInput("https://translate.google.com/translate?sl=auto&tl=zh-CN&u=" + URLEncoder.encode(url, "UTF-8")); }
        catch (Exception e) { toast("Impossible de créer l'adresse de traduction"); }
    }

    private void printPage() {
        if (webView == null || !isNetworkPage(webView.getUrl())) return;
        try {
            PrintManager manager = (PrintManager) getSystemService(PRINT_SERVICE);
            if (manager != null) manager.print(safeTitle(webView.getTitle(), webView.getUrl()),
                    webView.createPrintDocumentAdapter("Median page"), new android.print.PrintAttributes.Builder().build());
        } catch (Exception e) { toast("Service d'impression système indisponible"); }
    }

    private void showDownloadCenter() {
        try { startActivity(new Intent(this, DownloadCenterActivity.class)); }
        catch (RuntimeException error) { toast("Impossible d'ouvrir le centre de téléchargements : " + safeMessage(error)); }
    }

    private String downloadPolicySummary() {
        ArrayList<String> parts = new ArrayList<String>();
        if (prefs.getBoolean("download_wifi_only", false)) parts.add("Réseau non facturé uniquement"); else parts.add("Réseau mobile autorisé");
        if (prefs.getBoolean("download_allow_roaming", false)) parts.add("Itinérance autorisée");
        if (prefs.getBoolean("download_charging_only", false)) parts.add("Pendant la charge uniquement");
        parts.add("Téléchargement Median à connexion unique");
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < parts.size(); i++) { if (i > 0) out.append(" · "); out.append(parts.get(i)); }
        return out.toString();
    }

    private void showDownloadSettings() {
        String[] items = new String[] { "Modifier le dossier de téléchargement\nActuel : " + DownloadDirectory.label(this),
                "Politique de téléchargement\n" + downloadPolicySummary(), "Centre de téléchargements" };
        final Runnable returnHere = new Runnable() { @Override public void run() { showDownloadSettings(); } };
        showActionSheet("Paramètres de téléchargement", "Gestionnaire de téléchargement intégré et enregistrement de fichiers", items,
                new int[] { BrowserIconView.STORAGE, BrowserIconView.SETTINGS, BrowserIconView.STORAGE },
                null, null, this, new SheetHandler() {
                    @Override public void onItem(int which) {
                        if (which == 0) DownloadDirectory.showPickerDialog(MainActivity.this, DOWNLOAD_DIRECTORY_REQUEST, returnHere);
                        else if (which == 1) showDownloadPolicy(returnHere);
                        else showDownloadCenter();
                    }
                });
    }

    private void showDownloadPolicy(final Runnable returnAction) {
        final String[] labels = new String[] { "Télécharger uniquement sur un réseau non facturé", "Autoriser le téléchargement en itinérance", "Télécharger uniquement pendant la charge" };
        final boolean[] checked = new boolean[] {
                prefs.getBoolean("download_wifi_only", false),
                prefs.getBoolean("download_allow_roaming", false),
                prefs.getBoolean("download_charging_only", false)
        };
        AlertDialog dialog = new AlertDialog.Builder(this).setTitle("Politique de téléchargement")
                .setMultiChoiceItems(labels, checked, new DialogInterface.OnMultiChoiceClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which, boolean isChecked) { checked[which] = isChecked; }
                })
                .setPositiveButton("Enregistrer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        prefs.edit().putBoolean("download_wifi_only", checked[0])
                                .putBoolean("download_allow_roaming", checked[1])
                                .putBoolean("download_charging_only", checked[2]).apply();
                        toast("Politique de téléchargement mise à jour");
                        continueSettingsPanel(returnAction);
                    }
                }).setNegativeButton("Annuler", new SettingsDialogReturn(returnAction))
                .setOnCancelListener(new SettingsDialogReturn(returnAction)).create();
        secureDialog(dialog);
        dialog.show();
    }

    private String downloadStatusSummary(long id) {
        DownloadStore.Item item = services.downloads().get(id);
        if (item != null && item.isAdaptive()) return adaptiveDownloadStatus(item);
        DownloadManager manager = (DownloadManager) getSystemService(DOWNLOAD_SERVICE);
        if (manager == null) return "État inconnu";
        Cursor cursor = null;
        try {
            cursor = manager.query(new DownloadManager.Query().setFilterById(id));
            if (cursor == null || !cursor.moveToFirst()) return "Enregistrement invalide";
            return downloadStatusFromCursor(cursor);
        } catch (Exception e) {
            return "État inconnu";
        } finally {
            if (cursor != null) cursor.close();
        }
    }

    private String adaptiveDownloadStatus(DownloadStore.Item item) {
        if (DownloadStore.STATUS_COMPLETED.equals(item.status)) {
            return "Terminé" + (item.totalBytes > 0L ? " · " + humanBytes(item.totalBytes) : "");
        }
        if (DownloadStore.STATUS_FAILED.equals(item.status)) return "Échec · " + (item.reason.length() == 0 ? "Raison inconnue" : item.reason);
        if (DownloadStore.STATUS_CANCELLED.equals(item.status)) return "Annulé";
        if (DownloadStore.STATUS_PAUSED.equals(item.status)) return "En pause" + (item.reason.length() == 0 ? "" : " · " + item.reason);
        if (DownloadStore.STATUS_WAITING.equals(item.status)) return item.reason.length() == 0 ? "En attente" : item.reason;
        if (DownloadStore.STATUS_PENDING.equals(item.status)) return "Préparation";
        long percent = DownloadCenterPolicy.progressPermille(item.downloadedBytes, item.totalBytes) / 10L;
        StringBuilder out = new StringBuilder("Téléchargement en cours");
        if (item.totalBytes > 0L) out.append(" · ").append(percent).append('%');
        if (item.bytesPerSecond > 0L) out.append(" · ").append(humanBytes(item.bytesPerSecond)).append("/s");
        return out.toString();
    }

    private Map<Long, String> downloadStatusSummaries(List<DownloadStore.Item> downloads, int limit) {
        HashMap<Long, String> result = new HashMap<Long, String>();
        int count = Math.min(limit, downloads == null ? 0 : downloads.size());
        if (count == 0) return result;
        ArrayList<Long> systemIds = new ArrayList<Long>();
        for (int i = 0; i < count; i++) {
            DownloadStore.Item item = downloads.get(i);
            if (item.isAdaptive()) result.put(Long.valueOf(item.id), adaptiveDownloadStatus(item));
            else systemIds.add(Long.valueOf(item.id));
        }
        if (systemIds.size() == 0) return result;
        long[] ids = new long[systemIds.size()];
        for (int i = 0; i < systemIds.size(); i++) ids[i] = systemIds.get(i).longValue();
        DownloadManager manager = (DownloadManager) getSystemService(DOWNLOAD_SERVICE);
        if (manager == null) return result;
        Cursor cursor = null;
        try {
            cursor = manager.query(new DownloadManager.Query().setFilterById(ids));
            if (cursor == null) return result;
            int idColumn = cursor.getColumnIndexOrThrow(DownloadManager.COLUMN_ID);
            while (cursor.moveToNext()) result.put(Long.valueOf(cursor.getLong(idColumn)), downloadStatusFromCursor(cursor));
        } catch (Exception ignored) {
        } finally { if (cursor != null) cursor.close(); }
        return result;
    }

    private String downloadStatusFromCursor(Cursor cursor) {
        int status = cursor.getInt(cursor.getColumnIndexOrThrow(DownloadManager.COLUMN_STATUS));
        long current = cursor.getLong(cursor.getColumnIndexOrThrow(DownloadManager.COLUMN_BYTES_DOWNLOADED_SO_FAR));
        long total = cursor.getLong(cursor.getColumnIndexOrThrow(DownloadManager.COLUMN_TOTAL_SIZE_BYTES));
        if (status == DownloadManager.STATUS_SUCCESSFUL) return "Terminé" + (total > 0 ? " · " + humanBytes(total) : "");
        if (status == DownloadManager.STATUS_FAILED) return "Échec · " + downloadReason(cursor.getInt(cursor.getColumnIndexOrThrow(DownloadManager.COLUMN_REASON)));
        if (status == DownloadManager.STATUS_PAUSED) return "En pause · " + downloadReason(cursor.getInt(cursor.getColumnIndexOrThrow(DownloadManager.COLUMN_REASON)));
        if (status == DownloadManager.STATUS_PENDING) return "En attente";
        return "Téléchargement en cours" + (total > 0 ? " · " + (DownloadCenterPolicy.progressPermille(current, total) / 10) + "%" : "");
    }

    private void showDownloadActions(final DownloadStore.Item original) {
        final DownloadStore.Item latest = services.downloads().get(original.id);
        final DownloadStore.Item item = latest == null ? original : latest;
        String cancelLabel = item.isAdaptive() ? "Annuler la tâche de téléchargement" : "Supprimer l'ancienne tâche système";
        String[] actions = new String[] { "Ouvrir le fichier", "Partager le fichier", "Télécharger à nouveau", "Copier l'adresse de téléchargement", "Calculer le SHA-256", "Afficher les détails", cancelLabel, "Oublier uniquement l'entrée Median" };
        int[] icons = new int[] { BrowserIconView.PLUS, BrowserIconView.SHARE, BrowserIconView.RELOAD, BrowserIconView.PLUS,
                BrowserIconView.SHIELD, BrowserIconView.STORAGE, BrowserIconView.CLOSE, BrowserIconView.CLOSE };
        showActionSheet(item.filename, downloadStatusSummary(item.id), actions, icons, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) openDownloadedFile(item, false);
                else if (which == 1) openDownloadedFile(item, true);
                else if (which == 2) enqueueDownloadAdvanced(item.url,
                        webView == null ? null : webView.getSettings().getUserAgentString(), null,
                        item.mime, item.filename, downloadContextHeaders(webView, item.url));
                else if (which == 3) copyText("Adresse de téléchargement", item.url, "Adresse de téléchargement copiée");
                else if (which == 4) calculateDownloadSha256(item);
                else if (which == 5) showDownloadDetails(item);
                else if (which == 6) {
                    if (item.isAdaptive()) {
                        Intent cancel = new Intent(MainActivity.this, AdaptiveDownloadService.class);
                        cancel.setAction(AdaptiveDownloadService.ACTION_CANCEL);
                        cancel.putExtra(AdaptiveDownloadService.EXTRA_ID, item.id);
                        try { startService(cancel); } catch (RuntimeException ignored) {}
                        toast("Annulation du téléchargement demandée");
                    } else {
                        DownloadManager manager = (DownloadManager) getSystemService(DOWNLOAD_SERVICE);
                        if (manager != null) manager.remove(item.id);
                        services.downloads().remove(item.id);
                        toast("Tâche de téléchargement et enregistrement système supprimés");
                    }
                } else {
                    services.downloads().remove(item.id);
                    toast("Entrée de téléchargement Median supprimée");
                }
            }
        });
    }

    private void showDownloadDetails(DownloadStore.Item source) {
        final DownloadStore.Item refreshed = services.downloads().get(source.id);
        final DownloadStore.Item item = refreshed == null ? source : refreshed;
        String time = item.createdAt <= 0 ? "Inconnu" : new java.text.SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.getDefault()).format(new java.util.Date(item.createdAt));
        String engine = item.isAdaptive() ? "Téléchargement interne Median" : "Ancien enregistrement de téléchargement système";
        String progress = item.isAdaptive() ? (item.totalBytes > 0L ?
                "\nProgression : " + humanBytes(item.downloadedBytes) + " / " + humanBytes(item.totalBytes) :
                "\nProgression : " + humanBytes(item.downloadedBytes) + " / taille totale inconnue") : "";
        String message = "État : " + downloadStatusSummary(item.id) +
                "\nMoteur : " + engine + progress +
                "\nFichier : " + item.filename +
                "\nType : " + (item.mime.length() == 0 ? "Inconnu" : item.mime) +
                "\nDate de création : " + time +
                "\nID de tâche : " + item.id +
                "\nAdresse : " + item.url;
        AlertDialog dialog = new AlertDialog.Builder(this).setTitle("Détails du téléchargement").setMessage(message)
                .setPositiveButton("Copier l'adresse", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) { copyText("Adresse de téléchargement", item.url, "Adresse de téléchargement copiée"); }
                }).setNegativeButton("Fermer", null).create();
        secureDialog(dialog);
        dialog.show();
    }

    private void calculateDownloadSha256(final DownloadStore.Item source) {
        final DownloadStore.Item refreshed = services.downloads().get(source.id);
        final DownloadStore.Item item = refreshed == null ? source : refreshed;
        final Uri uri = downloadedUri(item);
        if (uri == null) { toast("Le fichier n'a pas encore été entièrement téléchargé"); return; }
        if (scriptNetworkExecutor == null || scriptNetworkExecutor.isShutdown()) return;
        toast("Calcul du SHA-256…");
        executeTask(scriptNetworkExecutor, new Runnable() {
            @Override public void run() {
                InputStream input = null;
                try {
                    MessageDigest digest = MessageDigest.getInstance("SHA-256");
                    input = getContentResolver().openInputStream(uri);
                    if (input == null) throw new IllegalStateException("Impossible de lire le fichier");
                    byte[] buffer = new byte[65536];
                    int read;
                    while ((read = input.read(buffer)) != -1) digest.update(buffer, 0, read);
                    byte[] bytes = digest.digest();
                    final String hex = HexCodec.encode(bytes, bytes.length, false, false);
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            if (activityDestroyed) return;
                            copyText("SHA-256", hex, "SHA-256 calculé et copié");
                            AlertDialog dialog = new AlertDialog.Builder(MainActivity.this).setTitle("SHA-256")
                                    .setMessage(item.filename + "\n\n" + hex).setPositiveButton("OK", null).create();
                            secureDialog(dialog); dialog.show();
                        }
                    });
                } catch (final Exception e) {
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            if (!activityDestroyed) toast("Échec de la vérification : " + safeMessage(e));
                        }
                    });
                } finally { NetworkSecurity.closeQuietly(input); }
            }
        });
    }

    private Uri downloadedUri(DownloadStore.Item item) {
        if (item == null) return null;
        if (item.isAdaptive()) {
            if (!DownloadStore.STATUS_COMPLETED.equals(item.status) || item.localUri.length() == 0) return null;
            try { return Uri.parse(item.localUri); } catch (RuntimeException ignored) { return null; }
        }
        DownloadManager manager = (DownloadManager) getSystemService(DOWNLOAD_SERVICE);
        return manager == null ? null : manager.getUriForDownloadedFile(item.id);
    }

    private String downloadReason(int reason) {
        if (reason == DownloadManager.PAUSED_WAITING_TO_RETRY) return "En attente de nouvelle tentative";
        if (reason == DownloadManager.PAUSED_WAITING_FOR_NETWORK) return "En attente de réseau";
        if (reason == DownloadManager.PAUSED_QUEUED_FOR_WIFI) return "En attente d'un réseau non facturé";
        if (reason == DownloadManager.PAUSED_UNKNOWN) return "Raison inconnue";
        if (reason == DownloadManager.ERROR_CANNOT_RESUME) return "Reprise impossible";
        if (reason == DownloadManager.ERROR_DEVICE_NOT_FOUND) return "Stockage indisponible";
        if (reason == DownloadManager.ERROR_FILE_ALREADY_EXISTS) return "Le fichier existe déjà";
        if (reason == DownloadManager.ERROR_FILE_ERROR) return "Erreur de fichier";
        if (reason == DownloadManager.ERROR_HTTP_DATA_ERROR) return "Erreur de données HTTP";
        if (reason == DownloadManager.ERROR_INSUFFICIENT_SPACE) return "Espace insuffisant";
        if (reason == DownloadManager.ERROR_TOO_MANY_REDIRECTS) return "Trop de redirections";
        if (reason >= 400 && reason <= 599) return "HTTP " + reason;
        return "code " + reason;
    }

    private void openDownloadedFile(DownloadStore.Item source, boolean share) {
        DownloadStore.Item refreshed = services.downloads().get(source.id);
        DownloadStore.Item item = refreshed == null ? source : refreshed;
        try {
            Uri uri = downloadedUri(item);
            if (uri == null) { toast("Le fichier n'a pas fini d'être téléchargé ou a été supprimé"); return; }
            String mime = DownloadFileTypes.mimeForOpen(getContentResolver(), uri, item.filename, item.mime);
            if (!share && DownloadFileTypes.isApk(item.filename, mime) && Build.VERSION.SDK_INT >= 26 &&
                    !getPackageManager().canRequestPackageInstalls()) {
                toast("Veuillez autoriser Median à installer les APK téléchargés, puis appuyez à nouveau sur « Ouvrir »");
                startActivity(new Intent(Settings.ACTION_MANAGE_UNKNOWN_APP_SOURCES,
                        Uri.parse("package:" + getPackageName())));
                return;
            }
            Intent intent;
            if (share) {
                intent = new Intent(Intent.ACTION_SEND);
                intent.setType(mime);
                intent.putExtra(Intent.EXTRA_STREAM, uri);
            } else {
                intent = new Intent(Intent.ACTION_VIEW);
                intent.setDataAndType(uri, mime);
            }
            intent.setClipData(ClipData.newRawUri(item.filename, uri));
            intent.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION);
            toast(share ? "Ouverture du panneau de partage" : "Ouverture : " + item.filename);
            startActivity(share ? Intent.createChooser(intent, "Partager le fichier téléchargé") : intent);
        } catch (Exception e) { toast("Échec de l'ouverture : aucune application disponible ou fichier déplacé"); }
    }

    private void probeAndShowMediaCenter() {
        if (webView == null || !isNetworkPage(webView.getUrl())) { showMediaCenter(); return; }
        final WebView source = webView;
        final long sequence = navigationSequence;
        final String sourceHost = currentHost();
        String probe = MediaProbeScript.build();
        try {
            source.evaluateJavascript(probe, new ValueCallback<String>() {
                @Override public void onReceiveValue(String value) {
                    if (!isCurrentPageCallback(source, sequence)) return;
                    try {
                        Object decoded = new JSONTokener(value == null ? "[]" : value).nextValue();
                        String json = decoded instanceof String ? (String) decoded : String.valueOf(decoded);
                        JSONArray array = new JSONArray(json);
                        for (int i = 0; i < array.length(); i++) {
                            JSONObject object = array.optJSONObject(i);
                            if (object == null) continue;
                            int opaque = object.optInt("opaque", 0);
                            if (opaque > 0) {
                                mediaSniffer.noteOpaqueCount(opaque);
                                continue;
                            }
                            mediaSniffer.observe(object.optString("url", ""), object.optString("mime", ""),
                                    sourceHost, object.optString("source", "probe"),
                                    object.optInt("width", 0), object.optInt("height", 0),
                                    object.optDouble("duration", 0d));
                        }
                    } catch (Exception ignored) {}
                    showMediaCenter();
                }
            });
        } catch (RuntimeException e) { showMediaCenter(); }
    }

    private void showMediaCenter() {
        final List<MediaResourceSniffer.Resource> resources = mediaSniffer.getAll();
        final int opaqueMedia = mediaSniffer.opaqueCount();
        String[] items = new String[resources.size() + 2];
        int[] icons = new int[items.length];
        items[0] = "Passer en image dans l'image maintenant";
        items[1] = "Image dans l'image automatique en quittant l'application : " + (autoPictureInPicture ? "Activé" : "Désactivé");
        icons[0] = BrowserIconView.SPEED;
        icons[1] = BrowserIconView.SPEED;
        for (int i = 0; i < resources.size(); i++) {
            MediaResourceSniffer.Resource item = resources.get(i);
            String host = hostOf(item.url);
            String detail = item.width > 0 && item.height > 0 ? " · " + item.width + "×" + item.height : "";
            if (item.duration > 0) detail += " · " + Math.max(1, Math.round(item.duration)) + " s";
            items[i + 2] = item.kind + detail + " · " + (host.length() == 0 ? item.url : host);
            icons[i + 2] = BrowserIconView.STORAGE;
        }
        String subtitle = resources.size() == 0 ?
                (opaqueMedia > 0 ? "La page utilise blob/MediaSource ; le suivi de ses manifestes, segments et sources réseau se poursuit" :
                        "Aucun lien direct découvert pour le moment ; les flux DRM et chiffrés ne sont pas déguisés en fichiers téléchargeables") :
                "Découverts : " + resources.size() + " ressources candidates" +
                        (opaqueMedia > 0 ? ", et " + opaqueMedia + " blob/MediaSource" : "") +
                        " · trié par manifestes, liens directs et segments";
        showActionSheet("Centre multimédia", subtitle, items, icons, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) enterPagePictureInPicture();
                else if (which == 1) {
                    autoPictureInPicture = !autoPictureInPicture;
                    prefs.edit().putBoolean("auto_picture_in_picture", autoPictureInPicture).apply();
                    toast(autoPictureInPicture ? "Tentative de passage en image dans l'image en quittant l'application" : "Image dans l'image automatique désactivée");
                } else {
                    int index = which - 2;
                    if (index >= 0 && index < resources.size()) showMediaResourceActions(resources.get(index));
                }
            }
        });
    }

    private void showMediaResourceActions(final MediaResourceSniffer.Resource resource) {
        showMediaResourceActions(resource, true);
    }

    private void showMediaResourceActions(final MediaResourceSniffer.Resource resource, boolean allowManifestInspection) {
        String lowerUrl = resource.url.toLowerCase(Locale.US);
        final boolean manifest = allowManifestInspection && ("Flux HLS".equals(resource.kind) ||
                "Flux DASH".equals(resource.kind) || "Flux Smooth".equals(resource.kind) ||
                "Manifeste multimédia".equals(resource.kind) || resource.mime.contains("mpegurl") ||
                resource.mime.contains("dash+xml") || resource.mime.contains("vnd.ms-sstr") ||
                lowerUrl.contains(".m3u") || lowerUrl.contains(".mpd") ||
                lowerUrl.contains(".ism/manifest") || lowerUrl.contains(".isml/manifest"));
        String[] actions = manifest ? new String[] { "Analyser le manifeste, les pistes et le chiffrement", "Ouvrir avec un lecteur externe", "Envoyer vers un gestionnaire de téléchargement externe", "Télécharger la ressource", "Ouvrir dans un nouvel onglet", "Copier l'adresse du média", "Partager l'adresse du média" }
                : new String[] { "Ouvrir avec un lecteur externe", "Envoyer vers un gestionnaire de téléchargement externe", "Télécharger la ressource", "Ouvrir dans un nouvel onglet", "Copier l'adresse du média", "Partager l'adresse du média" };
        int[] icons = manifest ? new int[] { BrowserIconView.SPEED, BrowserIconView.SPEED, BrowserIconView.STORAGE, BrowserIconView.STORAGE, BrowserIconView.PLUS, BrowserIconView.PLUS, BrowserIconView.SHARE }
                : new int[] { BrowserIconView.SPEED, BrowserIconView.STORAGE, BrowserIconView.STORAGE, BrowserIconView.PLUS, BrowserIconView.PLUS, BrowserIconView.SHARE };
        showActionSheet(resource.kind, hostOf(resource.url) + " · " + resource.mime, actions, icons, new SheetHandler() {
            @Override public void onItem(int which) {
                if (manifest && which == 0) { inspectMediaManifest(resource); return; }
                if (manifest) which--;
                if (which == 0) openMediaExternally(resource);
                else if (which == 1) sendToExternalDownloader(resource.url);
                else if (which == 2) enqueueDownload(webView, resource.url,
                        webView == null ? null : webView.getSettings().getUserAgentString(), null, resource.mime);
                else if (which == 3) openUrlInNewTab(resource.url, true);
                else if (which == 4) {
                    android.content.ClipboardManager manager = (android.content.ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
                    if (manager != null) manager.setPrimaryClip(android.content.ClipData.newPlainText("Adresse du média", resource.url));
                    toast("Adresse du média copiée");
                } else {
                    Intent share = new Intent(Intent.ACTION_SEND);
                    share.setType("text/plain");
                    share.putExtra(Intent.EXTRA_TEXT, resource.url);
                    try { startActivity(Intent.createChooser(share, "Partager l'adresse du média")); } catch (Exception e) { toast("Aucune application de partage disponible"); }
                }
            }
        });
    }

    private void inspectMediaManifest(final MediaResourceSniffer.Resource resource) {
        final WebView sourceView = webView;
        final long sourceSequence = navigationSequence;
        if (sourceView == null || resource == null) return;
        final HashMap<String, String> headers = new HashMap<String, String>(downloadContextHeaders(sourceView, resource.url));
        headers.put("User-Agent", sourceView.getSettings().getUserAgentString());
        headers.put("Accept", "application/vnd.apple.mpegurl, application/x-mpegurl, application/dash+xml, application/vnd.ms-sstr+xml, application/xml, text/xml, text/plain, */*");
        String cookie = CookieManager.getInstance().getCookie(resource.url);
        if (cookie != null && cookie.length() > 0) headers.put("Cookie", cookie);
        toast("Analyse du manifeste multimédia…");
        if (!executeTask(scriptNetworkExecutor, new Runnable() {
            @Override public void run() {
                HttpURLConnection connection = null;
                try {
                    connection = NetworkSecurity.openPublicGetFollowingRedirects(
                            NetworkSecurity.parseHttpUrl(resource.url), 5000, 7000, headers);
                    int status = connection.getResponseCode();
                    if (status < 200 || status >= 300) throw new IOException("HTTP " + status);
                    if (connection.getContentLength() > 2097152) throw new IOException("Manifeste supérieur à 2 Mo");
                    byte[] data = NetworkSecurity.readBounded(connection.getInputStream(), 2097152, "Manifeste supérieur à 2 Mo");
                    final String base = connection.getURL().toString();
                    String responseMime = connection.getContentType();
                    if (responseMime == null || responseMime.length() == 0) responseMime = resource.mime;
                    final MediaManifestParser.Playlist parsed = MediaManifestParser.parse(base, responseMime,
                            new String(data, StandardCharsets.UTF_8));
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            if (!activityDestroyed && isCurrentPageCallback(sourceView, sourceSequence))
                                showManifestVariants(resource, parsed);
                        }
                    });
                } catch (final Exception error) {
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            if (!activityDestroyed && isCurrentPageCallback(sourceView, sourceSequence))
                                toast("Échec de l'analyse du manifeste : " + safeMessage(error));
                        }
                    });
                } finally {
                    if (connection != null) connection.disconnect();
                }
            }
        })) toast("Service d'analyse multimédia occupé, veuillez réessayer plus tard");
    }

    private void showManifestVariants(MediaResourceSniffer.Resource source, final MediaManifestParser.Playlist playlist) {
        String state = (playlist.live ? "En direct" : "À la demande") + " · " + playlist.segments + " segments répertoriés" +
                (playlist.encrypted ? " · chiffrement détecté" : " · aucune balise de chiffrement détectée dans le manifeste");
        if (playlist.variants.size() == 0) {
            new AlertDialog.Builder(this).setTitle(playlist.format + " Informations sur le manifeste").setMessage(state +
                    (playlist.encrypted ? "\n\nLes flux chiffrés sont réservés aux lecteurs compatibles et ne sont pas déguisés en vidéo directement fusionnable." : ""))
                    .setPositiveButton("OK", null).show();
            return;
        }
        final ArrayList<MediaResourceSniffer.Resource> variants = new ArrayList<MediaResourceSniffer.Resource>();
        String[] labels = new String[playlist.variants.size()];
        int[] icons = new int[labels.length];
        for (int i = 0; i < labels.length; i++) {
            MediaManifestParser.Variant parsed = playlist.variants.get(i);
            MediaResourceSniffer.Resource item = new MediaResourceSniffer.Resource();
            item.url = parsed.url;
            item.mime = "HLS".equals(playlist.format) ? "application/vnd.apple.mpegurl" :
                    ("DASH".equals(playlist.format) ? "application/dash+xml" : "application/vnd.ms-sstr+xml");
            item.kind = playlist.format + " sous-flux";
            item.pageHost = source.pageHost;
            labels[i] = parsed.label;
            icons[i] = BrowserIconView.SPEED;
            variants.add(item);
            mediaSniffer.observe(item.url, item.mime, item.pageHost);
        }
        showActionSheet(playlist.format + " Qualités et pistes", state, labels, icons, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which >= 0 && which < variants.size()) showMediaResourceActions(variants.get(which), false);
            }
        });
    }

    private void openMediaExternally(MediaResourceSniffer.Resource resource) {
        try {
            Intent intent = new Intent(Intent.ACTION_VIEW);
            intent.setDataAndType(Uri.parse(resource.url), resource.mime.length() == 0 ? "video/*" : resource.mime);
            intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
            startActivity(intent);
        } catch (Exception e) { toast("Aucun lecteur compatible avec ce média externe"); }
    }

    /**
     * Gives URL-only download clients (1DM, ADM, etc.) a safe hand-off. Cookies,
     * Authorization headers and the WebView profile are intentionally not shared.
     */
    private void sendToExternalDownloader(String url) {
        try {
            final ArrayList<Intent> candidates = ExternalDownloadIntents.candidates(this, url);
            if (candidates.isEmpty()) { toast("Aucune application externe ne peut recevoir de lien de téléchargement"); return; }
            new AlertDialog.Builder(this).setTitle("Choisir un gestionnaire de téléchargement externe")
                    .setItems(ExternalDownloadIntents.labels(this, candidates), new DialogInterface.OnClickListener() {
                        @Override public void onClick(DialogInterface dialog, int which) {
                            try { startActivity(candidates.get(which)); }
                            catch (ActivityNotFoundException error) { toast("Cette application externe n'est plus disponible, veuillez rechoisir un gestionnaire"); }
                            catch (RuntimeException error) { toast("Impossible d'envoyer le lien de téléchargement : " + safeMessage(error)); }
                        }
                    }).setNegativeButton("Annuler", null).show();
        } catch (ActivityNotFoundException e) {
            toast("Aucun gestionnaire de téléchargement externe disponible");
        } catch (Exception e) {
            toast("Impossible d'envoyer le lien de téléchargement : " + safeMessage(e));
        }
    }

    private void enterPagePictureInPicture() {
        if (webView == null || !isNetworkPage(currentPageUrl)) { toast("Cette page ne peut pas passer en mode image dans l'image"); return; }
        try {
            PictureInPictureParams params = new PictureInPictureParams.Builder().setAspectRatio(new Rational(16, 9)).build();
            if (!enterPictureInPictureMode(params)) toast("Le système n'a pas autorisé le passage en image dans l'image");
        } catch (Exception e) { toast("Image dans l'image indisponible : " + safeMessage(e)); }
    }

    private void showPageScriptCommands() {
        if (webView == null || !isNetworkPage(currentPageUrl)) { toast("Aucune commande de script sur cette page"); return; }
        final WebView source = webView;
        final long sequence = navigationSequence;
        final String sourceUrl = currentPageUrl;
        final String token = scriptBridgeTokens.get(source);
        if (token == null || token.length() < 32) { toast("La WebView actuelle ne prend pas en charge les commandes de script sécurisées"); return; }
        StringBuilder query = new StringBuilder("(function(){var a=[];");
        for (UserScriptStore.Script script : scriptStore.getAll()) {
            if (!script.enabled || !scriptStore.matchesUrl(script.id, sourceUrl)) continue;
            String objectName = UserScriptStore.dispatchObjectName(token, script.id);
            query.append("try{var d=window[").append(JSONObject.quote(objectName)).append("];if(d&&typeof d.menus==='function'){var m=d.menus(")
                    .append(JSONObject.quote(token)).append(");if(Array.isArray(m))m.forEach(function(x){x.scriptId=")
                    .append(JSONObject.quote(script.id)).append(";a.push(x);});}}catch(_){}");
        }
        query.append("return JSON.stringify(a);})();");
        try {
            source.evaluateJavascript(query.toString(), new ValueCallback<String>() {
                @Override public void onReceiveValue(String value) {
                    if (!isCurrentPageCallback(source, sequence) || !token.equals(scriptBridgeTokens.get(source))) return;
                    try {
                        Object decoded = new JSONTokener(value == null ? "[]" : value).nextValue();
                        String raw = decoded instanceof String ? (String) decoded : String.valueOf(decoded);
                        final JSONArray commands = new JSONArray(raw);
                        if (commands.length() == 0) { toast("Les scripts de cette page n'ont enregistré aucune commande"); return; }
                        String[] items = new String[commands.length()];
                        int[] icons = new int[commands.length()];
                        for (int i = 0; i < commands.length(); i++) {
                            JSONObject command = commands.optJSONObject(i);
                            items[i] = (command == null ? "Commandes de script" : command.optString("caption", "Commandes de script")) +
                                    (command == null || command.optString("script", "").length() == 0 ? "" : " · " + command.optString("script", ""));
                            icons[i] = BrowserIconView.SCRIPT;
                        }
                        showActionSheet("Commandes de script", hostOf(sourceUrl), items, icons, new SheetHandler() {
                            @Override public void onItem(int which) {
                                JSONObject command = commands.optJSONObject(which);
                                if (command == null || !isCurrentPageCallback(source, sequence) ||
                                        !token.equals(scriptBridgeTokens.get(source))) return;
                                String scriptId = command.optString("scriptId", "");
                                String id = command.optString("id", "");
                                if (!scriptStore.matchesUrl(scriptId, source.getUrl())) return;
                                String objectName = UserScriptStore.dispatchObjectName(token, scriptId);
                                String run = "(function(){var d=window[" + JSONObject.quote(objectName) + "];if(d&&typeof d.runMenu==='function')d.runMenu(" +
                                        JSONObject.quote(token) + "," + JSONObject.quote(id) + ");})();";
                                try { source.evaluateJavascript(run, null); } catch (RuntimeException ignored) {}
                            }
                        });
                    } catch (Exception e) { toast("Impossible de lire les commandes de script de la page"); }
                }
            });
        } catch (RuntimeException e) { toast("Cette page ne prend pas en charge les commandes de script"); }
    }

    private String triStateLabel(int value, String inherit) {
        return value == SiteSettingsStore.ALLOW ? "Autoriser" : (value == SiteSettingsStore.BLOCK ? "Bloquer" : inherit);
    }

    private int nextTriState(int value) {
        if (value == SiteSettingsStore.INHERIT) return SiteSettingsStore.ALLOW;
        if (value == SiteSettingsStore.ALLOW) return SiteSettingsStore.BLOCK;
        return SiteSettingsStore.INHERIT;
    }

    private String searchEngineLabel() {
        return searchEngines == null ? "Google" : searchEngines.label(searchEngine);
    }

    private void showPerformancePanel() {
        showPerformancePanel(this);
    }

    private void showPerformancePanel(final Runnable backAction) {
        String[] modes = new String[] {
                "Mode fluide",
                "Mode standard",
                "Mode économie d'énergie",
                "Le mode fluide conserve le blocage de publicités (toujours activé)",
                "Libérer la mémoire des pages en arrière-plan"
        };
        int[] icons = new int[] { BrowserIconView.SPEED, BrowserIconView.HOME, BrowserIconView.SHIELD, BrowserIconView.SHIELD, BrowserIconView.STORAGE };
        int[] kinds = new int[] { SHEET_ROW_ACTION, SHEET_ROW_ACTION, SHEET_ROW_ACTION,
                SHEET_ROW_TOGGLE_ON, SHEET_ROW_ACTION };
        showActionSheet("Gestion des performances", modeLabel(), modes, icons,
                kinds, null, backAction, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 3) {
                    toast("Le blocage de publicités et la protection contre les redirections restent toujours activés");
                    showPerformancePanel(backAction);
                    return;
                }
                if (which == 4) {
                    releaseInactiveTabStates();
                    if (services != null) services.trimMemory();
                    toast("Mémoire des pages en arrière-plan libérée, les onglets sont conservés");
                    return;
                }
                setPerformanceMode(which == 0 ? MODE_PERFORMANCE : (which == 2 ? MODE_POWER_SAVE : MODE_STANDARD));
                postAfterUiTransition(new Runnable() {
                    @Override public void run() { showPerformancePanel(backAction); }
                });
            }
        });
    }

    private void setPerformanceMode(String mode) {
        if (!MODE_PERFORMANCE.equals(mode) && !MODE_POWER_SAVE.equals(mode)) mode = MODE_STANDARD;
        if (mode.equals(performanceMode)) return;
        performanceMode = mode;
        prefs.edit().putString("performance_mode", performanceMode).apply();
        applyPerformanceMode();
        renderedProgress = -1;
        renderedAddress = null;
        renderedBackEnabled = null;
        renderedForwardEnabled = null;
        renderedTabCount = null;
        renderedShieldActive = null;
        requestChromeUpdate();
        toast("Passage en mode " + modeLabel());
    }

    private String modeLabel() {
        if (MODE_PERFORMANCE.equals(performanceMode)) return "Mode fluide";
        if (MODE_POWER_SAVE.equals(performanceMode)) return "Mode économie d'énergie";
        return "Mode standard";
    }

    private boolean reduceMotion() {
        return MODE_POWER_SAVE.equals(performanceMode);
    }

    private int scriptThreadPriority() {
        // Parsing subscriptions and preparing userscripts must never compete with WebView's
        // renderer or Android's UI thread, including in the performance preset.
        return Process.THREAD_PRIORITY_BACKGROUND;
    }

    private int progressStep() {
        return MODE_POWER_SAVE.equals(performanceMode) ? 12 : 8;
    }

    private void showScriptCenter() {
        showScriptCenter(scriptCenterBackAction);
    }

    private void showScriptCenter(final Runnable backAction) {
        scriptCenterBackAction = backAction;
        final List<UserScriptStore.Script> scripts = scriptStore.getAll();
        final int actions = 4;
        String[] items = new String[actions + scripts.size()];
        int[] icons = new int[items.length];
        int[] kinds = new int[items.length];
        String[] sections = new String[items.length];
        items[0] = "Parcourir Greasy Fork\nRechercher des scripts utilisateur publics";
        items[1] = "Rechercher des scripts pour ce site\nFiltrer Greasy Fork par le domaine actuel";
        items[2] = "Coller un lien ou le code du script pour l'installer";
        items[3] = "Vérifier et mettre à jour tous les scripts";
        icons[0] = BrowserIconView.SEARCH;
        icons[1] = BrowserIconView.SEARCH;
        icons[2] = BrowserIconView.PLUS;
        icons[3] = BrowserIconView.RELOAD;
        for (int i = 0; i < actions; i++) kinds[i] = SHEET_ROW_ACTION;
        sections[0] = "Obtenir et gérer";
        for (int i = 0; i < scripts.size(); i++) {
            UserScriptStore.Script script = scripts.get(i);
            String version = script.version.length() == 0 ? "" : " · v" + script.version;
            items[i + actions] = script.name + version + "\n" +
                    (script.enabled ? "Activé" : "Désactivé") + " · " + script.matches.size() +
                    " correspondances · " + script.runAt;
            icons[i + actions] = BrowserIconView.SCRIPT;
            kinds[i + actions] = SHEET_ROW_NAVIGATE;
        }
        if (scripts.size() > 0) sections[actions] = "Installés · " + scripts.size();
        String subtitle = scripts.size() == 0 ? "Aucun script installé · Installez uniquement des sources de confiance" :
                "Activés : " + enabledScriptCount() + " · sans score de risque ni sandbox automatique";
        showActionSheet("Scripts utilisateur", subtitle, items, icons, kinds, sections, backAction,
                new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) loadNetworkUrl(webView, "https://greasyfork.org/zh-CN/scripts");
                else if (which == 1) {
                    String host = currentHost();
                    loadNetworkUrl(webView, host.length() == 0 || isHomeUrl(webView.getUrl()) ?
                            "https://greasyfork.org/zh-CN/scripts" :
                            "https://greasyfork.org/zh-CN/scripts/by-site/" + host);
                } else if (which == 2) showScriptImportDialog();
                else if (which == 3) updateAllUserScripts();
                else showScriptDetails(scripts.get(which - actions));
            }
        });
    }

    private void showScriptImportDialog() {
        final EditText input = new EditText(this);
        input.setHint("Collez un lien de script HTTPS ou le code ==UserScript== complet");
        input.setSingleLine(false);
        input.setMinLines(3);
        input.setMaxLines(8);
        input.setGravity(Gravity.TOP | Gravity.START);
        input.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_FLAG_MULTI_LINE |
                InputType.TYPE_TEXT_FLAG_NO_SUGGESTIONS);
        input.setPadding(dp(16), dp(8), dp(16), dp(8));
        String clipboard = clipboardText();
        if (UserScriptInstallPolicy.looksLikeInstallUrl(clipboard) ||
                UserScriptInstallPolicy.isSourceText(clipboard)) input.setText(clipboard);
        final SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
            @Override public void run() { showScriptCenter(); }
        });
        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Installer un script utilisateur")
                .setMessage("Copiez le lien du script puis ouvrez cet écran pour un remplissage automatique ; vous pouvez aussi coller directement le code complet. Les boutons d'installation .user.js des pages web sont pris en charge directement par Median.")
                .setView(input)
                .setPositiveButton("Lire et vérifier", null)
                .setNegativeButton("Annuler", back)
                .create();
        dialog.setOnCancelListener(back);
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) {
                        String value = input.getText().toString().trim();
                        if (UserScriptInstallPolicy.isSourceText(value)) {
                            dialog.dismiss();
                            installScriptFromSource(value);
                            return;
                        }
                        try {
                            NetworkSecurity.parseHttpsUrl(value);
                            dialog.dismiss();
                            installScriptFromUrl(value);
                        } catch (Exception invalid) {
                            input.setError("Veuillez coller un lien HTTPS valide ou un code UserScript complet");
                        }
                    }
                });
            }
        });
        dialog.show();
    }

    private String clipboardText() {
        ClipboardManager manager = (ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
        if (manager == null || !manager.hasPrimaryClip() || manager.getPrimaryClip() == null ||
                manager.getPrimaryClip().getItemCount() == 0) return "";
        CharSequence text = manager.getPrimaryClip().getItemAt(0).coerceToText(this);
        return text == null ? "" : text.toString().trim();
    }

    private void installScriptFromUrl(final String sourceUrl) {
        final String normalizedSourceUrl;
        try { normalizedSourceUrl = NetworkSecurity.parseHttpsUrl(sourceUrl).toString(); }
        catch (Exception invalidUrl) {
            toast("Les scripts ne peuvent être installés qu'à partir d'adresses HTTPS valides");
            return;
        }
        if (scriptDownloadInProgress) {
            toast("Un script est déjà en cours de lecture, veuillez patienter");
            return;
        }
        scriptDownloadInProgress = true;
        toast("Lecture du script ; nouvelles tentatives automatiques en cas d'instabilité du réseau…");
        final String userAgent = webView.getSettings().getUserAgentString();
        if (scriptNetworkExecutor == null || scriptNetworkExecutor.isShutdown()) {
            scriptDownloadInProgress = false;
            toast("Service d'arrière-plan des scripts indisponible");
            return;
        }
        if (!executeTask(scriptNetworkExecutor, new Runnable() {
            @Override public void run() {
                try { Process.setThreadPriority(scriptThreadPriority()); } catch (RuntimeException ignored) {}
                try {
                    final UserScriptStore.Script script = downloadAndPrepareUserScript(normalizedSourceUrl, userAgent);
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            // A network task may finish after Android has torn down this
                            // Activity. Do not attach a dialog to the dead window.
                            if (activityDestroyed) return;
                            showScriptInstallConfirmation(script);
                        }
                    });
                } catch (final Exception e) {
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            if (!activityDestroyed) toast("Échec de l'installation du script : " + safeMessage(e));
                        }
                    });
                } finally {
                    scriptDownloadInProgress = false;
                }
            }
        })) scriptDownloadInProgress = false;
    }

    private void installScriptFromSource(final String source) {
        if (!UserScriptInstallPolicy.isSourceText(source)) {
            toast("Ce n'est pas un code UserScript valide");
            return;
        }
        if (scriptDownloadInProgress) {
            toast("Un script est déjà en cours de lecture, veuillez patienter");
            return;
        }
        scriptDownloadInProgress = true;
        toast("Vérification du script et de ses dépendances…");
        final String userAgent = webView == null ? "MedianBrowser" : webView.getSettings().getUserAgentString();
        if (scriptNetworkExecutor == null || scriptNetworkExecutor.isShutdown()) {
            scriptDownloadInProgress = false;
            toast("Service d'arrière-plan des scripts indisponible");
            return;
        }
        if (!executeTask(scriptNetworkExecutor, new Runnable() {
            @Override public void run() {
                try { Process.setThreadPriority(scriptThreadPriority()); } catch (RuntimeException ignored) {}
                try {
                    final UserScriptStore.Script script = prepareUserScriptSource(source, "", userAgent);
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            if (activityDestroyed) return;
                            showScriptInstallConfirmation(script);
                        }
                    });
                } catch (final Exception error) {
                    uiHandler.post(new Runnable() {
                        @Override public void run() {
                            if (!activityDestroyed) toast("Échec de l'installation du script : " + safeMessage(error));
                        }
                    });
                } finally {
                    scriptDownloadInProgress = false;
                }
            }
        })) scriptDownloadInProgress = false;
    }

    private UserScriptStore.Script downloadAndPrepareUserScript(String sourceUrl, String userAgent) throws Exception {
        FetchedScriptBytes fetched = fetchUserScriptBytes(sourceUrl, userAgent, 16 * 1024 * 1024, "Script");
        return prepareUserScriptSource(new String(fetched.data, StandardCharsets.UTF_8), fetched.finalUrl, userAgent);
    }

    private UserScriptStore.Script prepareUserScriptSource(String source, String baseUrl, String userAgent) throws Exception {
        final UserScriptStore.Script parsed = scriptStore.parseUserScript(source, baseUrl);
        if (parsed.requires.size() > UserScriptStore.MAX_DEPENDENCIES || parsed.resources.size() > UserScriptStore.MAX_RESOURCES)
            throw new IllegalArgumentException("Nombre de dépendances du script utilisateur au-delà de la limite");
        if (parsed.updateUrl.length() > 0 && !"none".equalsIgnoreCase(parsed.updateUrl))
            parsed.updateUrl = resolveHttpsUrl(baseUrl, parsed.updateUrl, "@updateURL");
        if (parsed.downloadUrl.length() > 0 && !"none".equalsIgnoreCase(parsed.downloadUrl))
            parsed.downloadUrl = resolveHttpsUrl(baseUrl, parsed.downloadUrl, "@downloadURL");

        final ArrayList<String> requireUrls = new ArrayList<String>();
        final ArrayList<Future<FetchedScriptBytes>> downloads = new ArrayList<Future<FetchedScriptBytes>>();
        try {
            for (String requireUrl : parsed.requires) {
                final String resolved = resolveHttpsUrl(baseUrl, requireUrl, "@require");
                requireUrls.add(resolved);
                downloads.add(submitScriptAsset(resolved, userAgent, "@require"));
            }
            final int resourceOffset = downloads.size();
            for (UserScriptStore.Script.Resource resource : parsed.resources) {
                final String resolved = resolveHttpsUrl(baseUrl, resource.url, "@resource");
                resource.url = resolved;
                downloads.add(submitScriptAsset(resolved, userAgent, "@resource"));
            }

            StringBuilder dependencies = new StringBuilder();
            long assetBytes = 0L;
            for (int i = 0; i < requireUrls.size(); i++) {
                FetchedScriptBytes dependency = awaitScriptAsset(downloads.get(i));
                downloads.set(i, null);
                assetBytes += dependency.data.length;
                if (assetBytes > SCRIPT_ASSET_TOTAL_MAX_BYTES) throw new IllegalArgumentException("Taille totale des dépendances du script utilisateur au-delà de la limite");
                String resolved = requireUrls.get(i);
                dependencies.append("\n/* @require ").append(resolved.replace("*/", "* /")).append(" */\n")
                        .append(new String(dependency.data, StandardCharsets.UTF_8)).append('\n');
            }
            parsed.requireCode = dependencies.toString();
            for (int i = 0; i < parsed.resources.size(); i++) {
                UserScriptStore.Script.Resource resource = parsed.resources.get(i);
                int index = resourceOffset + i;
                FetchedScriptBytes data = awaitScriptAsset(downloads.get(index));
                downloads.set(index, null);
                assetBytes += data.data.length;
                if (assetBytes > SCRIPT_ASSET_TOTAL_MAX_BYTES) throw new IllegalArgumentException("Taille totale des ressources du script utilisateur au-delà de la limite");
                resource.mime = guessResourceMime(resource.url);
                resource.base64 = android.util.Base64.encodeToString(data.data, android.util.Base64.NO_WRAP);
            }
        } catch (Exception failure) {
            for (Future<FetchedScriptBytes> download : downloads) if (download != null) download.cancel(true);
            throw failure;
        }
        return parsed;
    }

    private Future<FetchedScriptBytes> submitScriptAsset(final String url, final String userAgent,
                                                          final String label) {
        if (scriptNetworkExecutor == null || scriptNetworkExecutor.isShutdown())
            throw new RejectedExecutionException("Service d'arrière-plan des scripts indisponible");
        return scriptNetworkExecutor.submit(new Callable<FetchedScriptBytes>() {
            @Override public FetchedScriptBytes call() throws Exception {
                try { Process.setThreadPriority(scriptThreadPriority()); } catch (RuntimeException ignored) {}
                return fetchUserScriptBytes(url, userAgent, SCRIPT_ASSET_MAX_BYTES, label);
            }
        });
    }

    private FetchedScriptBytes awaitScriptAsset(Future<FetchedScriptBytes> future) throws Exception {
        try {
            return future.get();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IOException("Lecture du script annulée", interrupted);
        } catch (ExecutionException wrapped) {
            Throwable cause = wrapped.getCause();
            if (cause instanceof Exception) throw (Exception) cause;
            throw new IOException("Échec de la lecture des dépendances du script", cause);
        }
    }

    private FetchedScriptBytes fetchUserScriptBytes(String sourceUrl, String userAgent, int maxBytes,
                                                     String label) throws Exception {
        URL parsed = NetworkSecurity.parseHttpsUrl(sourceUrl);
        Exception lastFailure = null;
        for (int attempt = 0; attempt < UserScriptInstallPolicy.MAX_FETCH_ATTEMPTS; attempt++) {
            HttpURLConnection connection = null;
            try {
                HashMap<String, String> headers = new HashMap<String, String>();
                headers.put("User-Agent", userAgent == null ? "MedianBrowser/2.0" : userAgent);
                headers.put("Accept", "text/javascript, application/javascript, text/plain, */*");
                headers.put("Cache-Control", "no-cache");
                connection = NetworkSecurity.openPublicHttpsGetFollowingRedirects(parsed,
                        UserScriptInstallPolicy.connectTimeoutMs(attempt),
                        UserScriptInstallPolicy.readTimeoutMs(attempt), headers);
                int status = connection.getResponseCode();
                if (status < 200 || status >= 300) {
                    if (!UserScriptInstallPolicy.retryableHttpStatus(status) ||
                            attempt + 1 >= UserScriptInstallPolicy.MAX_FETCH_ATTEMPTS)
                        throw new IllegalArgumentException(label + "Échec du téléchargement : HTTP " + status);
                    lastFailure = new IOException("HTTP " + status);
                } else {
                    int declared = connection.getContentLength();
                    if (declared > maxBytes) throw new IllegalArgumentException(label + "Contenu anormalement volumineux");
                    byte[] data = NetworkSecurity.readBounded(connection.getInputStream(), maxBytes, label + "Contenu anormalement volumineux");
                    return new FetchedScriptBytes(data, connection.getURL().toString());
                }
            } catch (Exception failure) {
                lastFailure = failure;
                if (!UserScriptInstallPolicy.retryableFailure(failure) ||
                        attempt + 1 >= UserScriptInstallPolicy.MAX_FETCH_ATTEMPTS) {
                    if (UserScriptInstallPolicy.retryableFailure(failure))
                        throw new IOException(label + "Délai expiré ou réseau interrompu (une nouvelle tentative automatique a été effectuée)", failure);
                    throw failure;
                }
            } finally {
                if (connection != null) connection.disconnect();
            }
            try { Thread.sleep(UserScriptInstallPolicy.retryDelayMs(attempt)); }
            catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
                throw new IOException("Lecture du script annulée", interrupted);
            }
        }
        throw new IOException(label + "Échec du téléchargement", lastFailure);
    }

    private String resolveHttpsUrl(String baseUrl, String candidate, String label) throws Exception {
        String resolved = baseUrl == null || baseUrl.length() == 0
                ? NetworkSecurity.parseHttpsUrl(candidate).toString()
                : new URL(new URL(baseUrl), candidate).toString();
        if (!resolved.startsWith("https://")) throw new IllegalArgumentException(label + " uniquement HTTPS autorisé : " + resolved);
        return resolved;
    }

    private static final class FetchedScriptBytes {
        final byte[] data;
        final String finalUrl;
        FetchedScriptBytes(byte[] data, String finalUrl) {
            this.data = data;
            this.finalUrl = finalUrl;
        }
    }

    private String guessResourceMime(String url) {
        String lower = url.toLowerCase(Locale.US);
        if (lower.matches(".*\\.(css)(?:[?#].*)?$")) return "text/css";
        if (lower.matches(".*\\.(js|mjs)(?:[?#].*)?$")) return "text/javascript";
        if (lower.matches(".*\\.(json)(?:[?#].*)?$")) return "application/json";
        if (lower.matches(".*\\.(png)(?:[?#].*)?$")) return "image/png";
        if (lower.matches(".*\\.(jpe?g)(?:[?#].*)?$")) return "image/jpeg";
        if (lower.matches(".*\\.(svg)(?:[?#].*)?$")) return "image/svg+xml";
        if (lower.matches(".*\\.(webp)(?:[?#].*)?$")) return "image/webp";
        if (lower.matches(".*\\.(txt|md|html?)(?:[?#].*)?$")) return "text/plain;charset=utf-8";
        return "application/octet-stream";
    }

    private void updateAllUserScripts() {
        updateUserScripts(scriptStore.getAll());
    }

    private void updateOneUserScript(UserScriptStore.Script script) {
        ArrayList<UserScriptStore.Script> scripts = new ArrayList<UserScriptStore.Script>();
        scripts.add(script);
        updateUserScripts(scripts);
    }

    private void updateUserScripts(final List<UserScriptStore.Script> scripts) {
        if (scriptDownloadInProgress) { toast("Une tâche de script est déjà en cours"); return; }
        if (scripts == null || scripts.size() == 0) { toast("Aucun script à vérifier"); return; }
        scriptDownloadInProgress = true;
        toast("Vérification des mises à jour des scripts…");
        final String userAgent = webView == null ? "MedianBrowser" : webView.getSettings().getUserAgentString();
        if (scriptNetworkExecutor == null || scriptNetworkExecutor.isShutdown()) {
            scriptDownloadInProgress = false;
            toast("Service d'arrière-plan des scripts indisponible");
            return;
        }
        if (!executeTask(scriptNetworkExecutor, new Runnable() {
            @Override public void run() {
                try { Process.setThreadPriority(scriptThreadPriority()); } catch (RuntimeException ignored) {}
                try {
                int checked = 0;
                int updated = 0;
                int failed = 0;
                int skipped = 0;
                ArrayList<UserScriptStore.Script> pendingSaves = new ArrayList<UserScriptStore.Script>();
                for (UserScriptStore.Script existing : scripts) {
                    String source = preferredUpdateUrl(existing);
                    if (!source.startsWith("https://")) { skipped++; continue; }
                    try {
                        UserScriptStore.Script candidate = downloadAndPrepareUserScript(source, userAgent);
                        checked++;
                        long now = System.currentTimeMillis();
                        int versionOrder = compareVersions(candidate.version, existing.version);
                        boolean changed = !candidate.code.equals(existing.code) || !candidate.requireCode.equals(existing.requireCode) ||
                                !resourceSignature(candidate).equals(resourceSignature(existing));
                        boolean shouldUpdate = versionOrder > 0 || (versionOrder == 0 && changed);
                        if (shouldUpdate) {
                            candidate.id = existing.id;
                            candidate.installedAt = existing.installedAt == 0L ? now : existing.installedAt;
                            candidate.updatedAt = now;
                            candidate.lastUpdateCheck = now;
                            candidate.enabled = existing.enabled;
                            pendingSaves.add(candidate);
                            updated++;
                        } else {
                            existing.lastUpdateCheck = now;
                            pendingSaves.add(existing);
                        }
                    } catch (Exception ignored) {
                        failed++;
                    }
                }
                // onDestroy() closes the store while an in-flight fetch is winding down.
                // Avoid writing through that closed instance and avoid posting a dialog to a
                // destroyed Activity.
                if (activityDestroyed || scriptStore == null) return;
                scriptStore.saveBatch(pendingSaves);
                final int finalChecked = checked;
                final int finalUpdated = updated;
                final int finalFailed = failed;
                final int finalSkipped = skipped;
                scriptDownloadInProgress = false;
                uiHandler.post(new Runnable() {
                    @Override public void run() {
                        if (activityDestroyed) return;
                        String result = "Mise à jour des scripts terminée : " + finalChecked + " vérifiés, " + finalUpdated + "";
                        if (finalSkipped > 0) result += ", " + finalSkipped + " scripts sans adresse de mise à jour ignorés";
                        if (finalFailed > 0) result += ", échecs : " + finalFailed + "";
                        toast(result);
                        if (finalUpdated > 0) refreshUserScriptRegistrations(true);
                    }
                });
                } catch (RuntimeException ignored) {
                    // The store can be closed while an update is winding down during Activity
                    // destruction. The finally block below releases the in-progress gate.
                } finally {
                    scriptDownloadInProgress = false;
                }
            }
        })) scriptDownloadInProgress = false;
    }

    private String preferredUpdateUrl(UserScriptStore.Script script) {
        if (script == null) return "";
        if ("none".equalsIgnoreCase(script.updateUrl) || "none".equalsIgnoreCase(script.downloadUrl)) return "";
        if (script.downloadUrl.length() > 0) return script.downloadUrl;
        if (script.sourceUrl.length() > 0) return script.sourceUrl;
        if (script.updateUrl.length() > 0) return script.updateUrl;
        return script.sourceUrl;
    }

    private int compareVersions(String left, String right) {
        String l = left == null ? "" : left.trim();
        String r = right == null ? "" : right.trim();
        int plus = l.indexOf('+'); if (plus >= 0) l = l.substring(0, plus);
        plus = r.indexOf('+'); if (plus >= 0) r = r.substring(0, plus);
        String[] lp = l.split("-", 2);
        String[] rp = r.split("-", 2);
        String[] a = lp[0].split("[._]");
        String[] b = rp[0].split("[._]");
        int count = Math.max(a.length, b.length);
        for (int i = 0; i < count; i++) {
            String av = i < a.length ? a[i] : "0";
            String bv = i < b.length ? b[i] : "0";
            int comparison = compareVersionPart(av, bv, false);
            if (comparison != 0) return comparison;
        }
        boolean aPre = lp.length > 1 && lp[1].length() > 0;
        boolean bPre = rp.length > 1 && rp[1].length() > 0;
        if (aPre != bPre) return aPre ? -1 : 1;
        if (!aPre) return 0;
        a = lp[1].split("[._-]");
        b = rp[1].split("[._-]");
        count = Math.max(a.length, b.length);
        for (int i = 0; i < count; i++) {
            if (i >= a.length) return -1;
            if (i >= b.length) return 1;
            int comparison = compareVersionPart(a[i], b[i], true);
            if (comparison != 0) return comparison;
        }
        return 0;
    }

    private int compareVersionPart(String left, String right, boolean numericBeforeText) {
        boolean leftNumber = left.matches("[0-9]+");
        boolean rightNumber = right.matches("[0-9]+");
        if (leftNumber && rightNumber) {
            try { return Long.compare(Long.parseLong(left), Long.parseLong(right)); }
            catch (NumberFormatException ignored) {
                if (left.length() != right.length()) return left.length() < right.length() ? -1 : 1;
                return left.compareTo(right);
            }
        }
        if (numericBeforeText && leftNumber != rightNumber) return leftNumber ? -1 : 1;
        return left.compareToIgnoreCase(right);
    }

    private String resourceSignature(UserScriptStore.Script script) {
        StringBuilder value = new StringBuilder();
        for (UserScriptStore.Script.Resource resource : script.resources) {
            value.append(resource.name).append(':').append(resource.url).append(':').append(UrlCleaner.stableId(resource.base64)).append(';');
        }
        return value.toString();
    }

    private void showScriptInstallConfirmation(final UserScriptStore.Script script) {
        StringBuilder scope = new StringBuilder();
        int count = Math.min(6, script.matches.size());
        for (int i = 0; i < count; i++) scope.append("\n• ").append(script.matches.get(i));
        if (script.matches.size() > count) scope.append("\n• et ").append(script.matches.size() - count).append(" élément(s)");
        StringBuilder grants = new StringBuilder();
        int grantCount = Math.min(6, script.grants.size());
        for (int i = 0; i < grantCount; i++) grants.append(i == 0 ? "" : "、").append(script.grants.get(i));
        if (script.grants.size() > grantCount) grants.append(" et ").append(script.grants.size()).append(" élément(s)");
        String message = "Version : " + (script.version.length() == 0 ? "Inconnu" : script.version) +
                "\nSource : " + (script.sourceUrl.length() == 0 ? "Collé localement" : script.sourceUrl) +
                "\nMoment d'exécution : " + script.runAt + (script.noFrames ? " · page de premier niveau uniquement" : "") +
                "\nAutorisations déclarées : " + (grants.length() == 0 ? "Non déclaré" : grants.toString()) +
                "\nDépendances HTTPS : " + script.requires.size() + " élément(s)" +
                "\nRessources HTTPS : " + script.resources.size() + " élément(s)" +
                "\nPortée réseau : " + (script.connects.size() == 0 ? "Non déclaré" : script.connects.toString()) +
                "\n\nSites sur lesquels le script peut s'exécuter : " + scope.toString() +
                "\n\nInstallez uniquement des scripts de confiance. Le réseau natif respecte strictement @connect et refuse les adresses locales et privées.";
        new AlertDialog.Builder(this)
                .setTitle("Installer « " + script.name + "”？")
                .setMessage(message)
                .setPositiveButton("Installer et activer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        script.enabled = true;
                        scriptStore.save(script);
                        refreshUserScriptRegistrations(true);
                        toast("Script installé et activé");
                    }
                })
                .setNeutralButton("Installer mais désactiver", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        script.enabled = false;
                        scriptStore.save(script);
                        refreshUserScriptRegistrations(false);
                        toast("Script installé, actuellement désactivé");
                    }
                })
                .setNegativeButton("Annuler", null)
                .show();
    }

    private void showScriptDetails(final UserScriptStore.Script script) {
        boolean canUpdate = preferredUpdateUrl(script).length() > 0;
        String[] items = canUpdate
                ? new String[] { script.enabled ? "Désactiver le script" : "Activer le script", "Vérifier les mises à jour",
                        "Autorisations, source et portée de correspondance", "Supprimer le script" }
                : new String[] { script.enabled ? "Désactiver le script" : "Activer le script",
                        "Autorisations, source et portée de correspondance", "Supprimer le script" };
        int[] icons = canUpdate
                ? new int[] { BrowserIconView.SCRIPT, BrowserIconView.RELOAD,
                        BrowserIconView.INFO, BrowserIconView.DELETE }
                : new int[] { BrowserIconView.SCRIPT, BrowserIconView.INFO, BrowserIconView.DELETE };
        int[] kinds = new int[items.length];
        for (int i = 0; i < kinds.length; i++) kinds[i] = SHEET_ROW_ACTION;
        String subtitle = (script.enabled ? "Activé" : "Désactivé") +
                (script.version.length() == 0 ? "" : " · v" + script.version) + " · " + script.runAt;
        showActionSheet(script.name, subtitle, items, icons, kinds, null,
                new Runnable() { @Override public void run() { showScriptCenter(); } },
                new SheetHandler() {
                    @Override public void onItem(int which) {
                        boolean hasUpdate = preferredUpdateUrl(script).length() > 0;
                        if (which == 0) {
                            scriptStore.setEnabled(script.id, !script.enabled);
                            refreshUserScriptRegistrations(true);
                            toast(script.enabled ? "Script activé" : "Script désactivé");
                            showScriptDetails(script);
                        } else if (hasUpdate && which == 1) updateOneUserScript(script);
                        else if (which == (hasUpdate ? 2 : 1)) showScriptMetadata(script);
                        else confirmDeleteScript(script);
                    }
                });
    }

    private void showScriptMetadata(final UserScriptStore.Script script) {
        StringBuilder matches = new StringBuilder();
        for (String item : script.matches) matches.append("\n• ").append(item);
        String message = "État : " + (script.enabled ? "Activé" : "Désactivé") +
                "\nVersion : " + (script.version.length() == 0 ? "Inconnu" : script.version) +
                "\nMoment d'exécution : " + script.runAt + (script.noFrames ? " · page de premier niveau uniquement" : "") +
                "\nAutorisations déclarées : " + (script.grants.size() == 0 ? "Non déclaré" : script.grants.toString()) +
                "\nDépendances HTTPS : " + script.requires.size() + " élément(s)" +
                "\nRessources HTTPS : " + script.resources.size() + " élément(s)" +
                "\nPortée réseau : " + (script.connects.size() == 0 ? "Non déclaré" : script.connects.toString()) +
                "\nSource : " + (script.sourceUrl.length() == 0 ? "Local" : script.sourceUrl) +
                "\nPortée de correspondance : " + matches.toString();
        SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
            @Override public void run() { showScriptDetails(script); }
        });
        new AlertDialog.Builder(this)
                .setTitle(script.name)
                .setMessage(message)
                .setPositiveButton("OK", back)
                .setNegativeButton("Retour", back)
                .setOnCancelListener(back).show();
    }

    private void confirmDeleteScript(final UserScriptStore.Script script) {
        SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
            @Override public void run() { showScriptDetails(script); }
        });
        new AlertDialog.Builder(this).setTitle("Supprimer le script ?").setMessage(script.name)
                .setPositiveButton("Supprimer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        scriptStore.delete(script.id);
                        refreshUserScriptRegistrations(true);
                        toast("Script supprimé");
                        showScriptCenter();
                    }
                }).setNegativeButton("Annuler", back).setOnCancelListener(back).show();
    }

    private boolean looksLikeUserScript(String url) {
        return UserScriptInstallPolicy.looksLikeInstallUrl(url);
    }

    private int enabledScriptCount() {
        int count = 0;
        for (UserScriptStore.Script script : scriptStore.getAll()) if (script.enabled) count++;
        return count;
    }

    private void showTabs() {
        if (!requireStartupReady()) return;
        saveCurrentTab();
        dismissOverlayForNavigation();
        final int pageBackground = nightMode ? DARK_BACKGROUND : WHITE;
        final int cardBackground = nightMode ? DARK_CARD : WHITE;
        final int activeCard = nightMode ? 0xff203652 : 0xffe8f0fe;
        final int pageText = nightMode ? DARK_TEXT : TEXT;
        final int pageMuted = nightMode ? DARK_MUTED : MUTED;
        final FrameLayout overlay = new FrameLayout(this);
        overlay.setBackgroundColor(pageBackground);
        overlay.setClickable(true);
        overlay.setFocusableInTouchMode(true);

        LinearLayout page = new LinearLayout(this);
        page.setOrientation(LinearLayout.VERTICAL);
        page.setClickable(true);
        page.setPadding(dp(14), dp(8), dp(14), dp(12));
        overlay.addView(page, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.CENTER_VERTICAL);
        header.setPadding(dp(4), 0, 0, dp(8));
        TextView title = new TextView(this);
        title.setText("Onglets  " + tabs.size());
        title.setTextSize(22f);
        title.setTextColor(pageText);
        title.setTypeface(android.graphics.Typeface.DEFAULT_BOLD);
        header.addView(title, new LinearLayout.LayoutParams(0, dp(54), 1f));
        BrowserIconView add = iconButton(BrowserIconView.PLUS, "Nouvel onglet");
        BrowserIconView closePage = iconButton(BrowserIconView.CLOSE, "Retour à la page");
        add.setTintColor(pageText);
        closePage.setTintColor(pageText);
        header.addView(add, new LinearLayout.LayoutParams(dp(48), dp(48)));
        header.addView(closePage, new LinearLayout.LayoutParams(dp(48), dp(48)));
        page.addView(header, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(58)));

        final BaseAdapter[] tabAdapterHolder = new BaseAdapter[1];
        final class TabRow {
            final LinearLayout root;
            final TextView title;
            final TextView url;
            final BrowserIconView close;

            TabRow() {
                root = new LinearLayout(MainActivity.this);
                root.setOrientation(LinearLayout.HORIZONTAL);
                root.setGravity(Gravity.CENTER_VERTICAL);
                root.setPadding(dp(16), dp(8), dp(7), dp(8));
                root.setElevation(dp(1));
                // Bind touch directly to the card instead of relying on ListView row dispatch.
                // Some OEM ListView implementations stop delivering item clicks when a row
                // contains an independently clickable child such as the close button.
                root.setClickable(true);
                root.setLongClickable(true);
                root.setFocusable(false);
                LinearLayout text = new LinearLayout(MainActivity.this);
                text.setOrientation(LinearLayout.VERTICAL);
                text.setGravity(Gravity.CENTER_VERTICAL);
                title = new TextView(MainActivity.this);
                title.setTextColor(pageText);
                title.setTextSize(15.5f);
                title.setSingleLine(true);
                title.setEllipsize(android.text.TextUtils.TruncateAt.END);
                url = new TextView(MainActivity.this);
                url.setTextColor(pageMuted);
                url.setTextSize(12.5f);
                url.setSingleLine(true);
                url.setEllipsize(android.text.TextUtils.TruncateAt.END);
                text.addView(title, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(27)));
                text.addView(url, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(23)));
                root.addView(text, new LinearLayout.LayoutParams(0, dp(58), 1f));
                close = iconButton(BrowserIconView.CLOSE, "Fermer l'onglet");
                close.setTintColor(pageText);
                // Keep the close affordance touchable without allowing it to steal row focus.
                close.setFocusable(false);
                close.setFocusableInTouchMode(false);
                root.addView(close, new LinearLayout.LayoutParams(dp(46), dp(46)));
            }

            void bind(final int position) {
                final BrowserTab boundTab = tabs.get(position);
                title.setText((boundTab.pinned ? "Épinglé · " : "") + safeTitle(boundTab.title, boundTab.url));
                String host = hostOf(boundTab.url);
                url.setText(host.length() == 0 ? "Accueil" : host);
                root.setBackground(roundRect(position == currentTabIndex ? activeCard : cardBackground, 18));
                root.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View view) {
                        int currentPosition = tabs.indexOf(boundTab);
                        if (currentPosition < 0) return;
                        dismissOverlay();
                        switchTab(currentPosition);
                    }
                });
                root.setOnLongClickListener(new View.OnLongClickListener() {
                    @Override public boolean onLongClick(View view) {
                        int currentPosition = tabs.indexOf(boundTab);
                        if (currentPosition < 0) return false;
                        BrowserTab tab = tabs.get(currentPosition);
                        tab.pinned = !tab.pinned;
                        persistSession();
                        if (tabAdapterHolder[0] != null) tabAdapterHolder[0].notifyDataSetChanged();
                        toast(tab.pinned ? "Onglet épinglé" : "Épinglage annulé");
                        return true;
                    }
                });
                close.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View view) {
                        int currentPosition = tabs.indexOf(boundTab);
                        if (currentPosition >= 0) closeTabAt(currentPosition);
                    }
                });
            }
        }

        final BaseAdapter tabAdapter = new BaseAdapter() {
            @Override public int getCount() { return tabs.size(); }
            @Override public BrowserTab getItem(int position) { return tabs.get(position); }
            @Override public long getItemId(int position) { return position; }
            @Override public View getView(int position, View convertView, ViewGroup parent) {
                TabRow row;
                if (convertView == null) {
                    row = new TabRow();
                    row.root.setTag(row);
                    convertView = row.root;
                } else row = (TabRow) convertView.getTag();
                row.bind(position);
                return convertView;
            }
        };
        tabAdapterHolder[0] = tabAdapter;
        ListView list = new ListView(this);
        list.setAdapter(tabAdapter);
        list.setBackgroundColor(Color.TRANSPARENT);
        list.setDivider(new android.graphics.drawable.ColorDrawable(Color.TRANSPARENT));
        list.setDividerHeight(dp(10));
        list.setPadding(0, dp(4), 0, dp(20));
        list.setClipToPadding(false);
        list.setVerticalScrollBarEnabled(false);
        list.setItemsCanFocus(false);
        page.addView(list, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f));

        rootFrame.addView(overlay, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        activeOverlay = overlay;
        activeOverlayPanel = page;
        activeOverlaySheet = false;
        activeOverlayBackAction = null;
        activeOverlayDismissAction = null;
        Motion.showPage(overlay, page, reduceMotion());
        add.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { dismissOverlay(); newTab(); }
        });
        closePage.setOnClickListener(new View.OnClickListener() {
            @Override public void onClick(View v) { dismissOverlay(); }
        });
    }

    private void closeTabAt(int index) {
        if (index < 0 || index >= tabs.size()) return;
        if (tabs.size() <= 1) {
            dismissOverlay();
            resetOnlyTabToHome(true);
            return;
        }
        if (index == currentTabIndex) {
            dismissOverlay();
            closeCurrentTab();
            return;
        }
        BrowserTab removed = tabs.remove(index);
        rememberClosedTab(removed);
        destroyTabView(removed, false);
        if (index < currentTabIndex) currentTabIndex--;
        renderedTabCount = null;
        persistSession();
        showTabs();
    }

    private void newTab() {
        if (!requireStartupReady()) return;
        if (tabs.size() >= MAX_TABS) { toast("Maximum autorisé : " + MAX_TABS + " onglets"); return; }
        BrowserTab tab = new BrowserTab();
        tab.url = configuredHomeUrl();
        tabs.add(tab);
        activateTab(tabs.size() - 1);
        if (webView != null) webView.clearHistory();
    }

    private void switchTab(int index) {
        if (index < 0 || index >= tabs.size() || index == currentTabIndex) return;
        activateTab(index);
    }

    private void activateTab(int index) {
        if (index < 0 || index >= tabs.size()) return;
        BrowserTab previous = currentTabIndex >= 0 && currentTabIndex < tabs.size() ? tabs.get(currentTabIndex) : null;
        BrowserTab targetTab = tabs.get(index);
        WebView previousView = webView;
        boolean singleRendererSwap = targetTab.liveView == null && previous != null && previousView != null &&
                deviceProfile != null && deviceProfile.hotWebViewLimit(performanceMode) <= 1;
        if (previous != null && previousView != null) {
            updateTabForView(previousView, previousView.getUrl(), previousView.getTitle());
            previous.lastActiveAt = SystemClock.uptimeMillis();
            previousView.onPause();
            if (previousView.getParent() == webContainer) webContainer.removeView(previousView);
        }

        currentTabIndex = index;
        // In the one-renderer policy, capture and destroy the old surface before allocating the
        // target. The former create-first/trim-next-frame order briefly doubled Chromium memory
        // and produced exactly the tab-switch peaks users could feel as jank.
        if (singleRendererSwap) {
            previous.state = captureWebViewState(previousView);
            previous.liveView = null;
            webView = null;
            destroyWebView(previousView);
            trimColdTabStates();
        }
        boolean created = targetTab.liveView == null;
        if (created) {
            makeRoomForRenderer();
            bindWebViewToTab(targetTab, acquireWebView());
        }
        webView = targetTab.liveView;
        if (!singleRendererSwap && previousView != null && previousView != webView) applyPerformanceMode(previousView);
        applyPerformanceMode(webView);
        targetTab.lastActiveAt = SystemClock.uptimeMillis();
        if (webView.getParent() instanceof ViewGroup) ((ViewGroup) webView.getParent()).removeView(webView);
        webContainer.addView(webView, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        webView.onResume();
        resetWebViewTransform(webView);
        webView.requestFocus(View.FOCUS_DOWN);

        advanceNavigationSequence();
        preparedInjection = null;
        pageCommitted = true;
        pageFinished = webView.getProgress() >= 100;
        injectedStartSequence = -1;
        injectedEndSequence = -1;

        if (created) {
            boolean restored = restoreWebViewState(webView, targetTab.state);
            targetTab.state = null;
            if (!restored) {
                if (isHomeUrl(targetTab.url)) showHome();
                else if (isQrScannerUrl(targetTab.url)) showQrScannerPage();
                else loadNetworkUrl(webView, targetTab.url);
            } else {
                currentPageUrl = webView.getUrl() == null ? targetTab.url : webView.getUrl();
                currentPageHost = hostOf(currentPageUrl);
                if (isHomeUrl(currentPageUrl)) {
                    renderedHomeKeys.remove(webView);
                    showHome();
                } else if (isQrScannerUrl(currentPageUrl)) {
                    showQrScannerPage();
                } else if (isNetworkPage(currentPageUrl)) {
                    prepareNetworkDestination(webView, currentPageUrl, currentPageHost);
                    watchInitialNetworkNavigation(webView, currentPageUrl);
                } else if (isOfflineUrl(currentPageUrl)) {
                    prepareOfflineDestination(webView, currentPageUrl);
                } else {
                    applyPageAccessPolicy(webView, currentPageUrl);
                    appliedSiteSettings.remove(webView);
                }
            }
        } else {
            currentPageUrl = webView.getUrl() == null ? targetTab.url : webView.getUrl();
            currentPageHost = hostOf(currentPageUrl);
        }

        pageHosts.put(webView, currentPageHost == null ? "" : currentPageHost);
        resumeQrScannerIfNeeded();
        scheduleHotWebViewTrim();
        requestChromeUpdate();
        persistSession();
    }

    private void closeCurrentTab() {
        if (tabs.size() <= 1) {
            resetOnlyTabToHome(true);
            return;
        }
        int closingIndex = currentTabIndex;
        BrowserTab closing = tabs.get(closingIndex);
        rememberClosedTab(closing);
        if (webView != null && webView.getParent() == webContainer) webContainer.removeView(webView);
        destroyTabView(closing, false);
        tabs.remove(closingIndex);
        int target = Math.min(closingIndex, tabs.size() - 1);
        currentTabIndex = -1;
        webView = null;
        activateTab(target);
    }

    private void resetOnlyTabToHome(boolean remember) {
        if (tabs.size() == 0) tabs.add(new BrowserTab());
        BrowserTab tab = tabs.get(0);
        if (remember) rememberClosedTab(tab);
        tab.title = "Nouvel onglet";
        final String target = configuredHomeUrl();
        tab.url = target;
        tab.state = null;
        tab.pinned = false;
        if (webView != null) {
            try { webView.stopLoading(); webView.clearHistory(); } catch (RuntimeException ignored) {}
        }
        currentTabIndex = 0;
        openConfiguredHome();
        uiHandler.postDelayed(new Runnable() {
            @Override public void run() {
                if (webView != null && (isHomeUrl(target) ? isHomeUrl(webView.getUrl()) : target.equals(webView.getUrl())))
                    webView.clearHistory();
            }
        }, 250L);
        persistSession();
    }

    private void rememberClosedTab(BrowserTab tab) {
        if (tab == null || tab.url == null || isInternalBrowserUrl(tab.url)) return;
        BrowserTab copy = new BrowserTab();
        copy.title = tab.title;
        copy.url = tab.url;
        copy.pinned = tab.pinned;
        closedTabs.add(0, copy);
        while (closedTabs.size() > 12) closedTabs.remove(closedTabs.size() - 1);
    }

    private void showTabTools() {
        String[] items = new String[] {
                "Rechercher des onglets",
                "Rouvrir un onglet récemment fermé" + (closedTabs.size() == 0 ? " · aucun enregistrement" : " · " + closedTabs.size()),
                "Dupliquer l'onglet actuel",
                "Fermer les autres onglets non épinglés",
                "Geler les onglets en arrière-plan non épinglés",
                "Tout fermer et revenir à l'accueil"
        };
        int[] icons = new int[] { BrowserIconView.SEARCH, BrowserIconView.RELOAD, BrowserIconView.PLUS,
                BrowserIconView.CLOSE, BrowserIconView.SPEED, BrowserIconView.HOME };
        showActionSheet("Outils des onglets", tabs.size() + " onglets", items, icons, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) showTabSearch();
                else if (which == 1) reopenClosedTab();
                else if (which == 2) duplicateCurrentTab();
                else if (which == 3) closeOtherTabs();
                else if (which == 4) {
                    int frozen = 0;
                    for (int i = 0; i < tabs.size(); i++) {
                        BrowserTab tab = tabs.get(i);
                        if (i != currentTabIndex && !tab.pinned && tab.liveView != null) {
                            freezeTab(tab);
                            frozen++;
                        }
                    }
                    if (frozen == 0) {
                        toast("Aucun onglet en arrière-plan non épinglé à geler");
                        showTabTools();
                    } else toast("Gelés : " + frozen + " onglets en arrière-plan");
                } else closeAllTabs();
            }
        });
    }

    private void reopenClosedTab() {
        if (closedTabs.size() == 0) { toast("Aucun onglet récemment fermé"); showTabTools(); return; }
        if (tabs.size() >= MAX_TABS) { toast("Nombre maximal d'onglets atteint"); showTabTools(); return; }
        BrowserTab closed = closedTabs.remove(0);
        BrowserTab tab = new BrowserTab();
        tab.title = closed.title;
        tab.url = closed.url;
        tab.pinned = closed.pinned;
        tabs.add(tab);
        activateTab(tabs.size() - 1);
    }

    private void duplicateCurrentTab() {
        if (currentTabIndex < 0 || currentTabIndex >= tabs.size()) return;
        if (tabs.size() >= MAX_TABS) { toast("Nombre maximal d'onglets atteint"); showTabTools(); return; }
        saveCurrentTab();
        BrowserTab current = tabs.get(currentTabIndex);
        BrowserTab duplicate = new BrowserTab();
        duplicate.title = current.title;
        duplicate.url = current.url;
        tabs.add(duplicate);
        activateTab(tabs.size() - 1);
    }

    private void closeOtherTabs() {
        if (tabs.size() <= 1) { toast("Aucun autre onglet"); showTabTools(); return; }
        BrowserTab current = tabs.get(currentTabIndex);
        int closed = 0;
        for (int i = tabs.size() - 1; i >= 0; i--) {
            BrowserTab tab = tabs.get(i);
            if (tab == current || tab.pinned) continue;
            rememberClosedTab(tab);
            destroyTabView(tab, false);
            tabs.remove(i);
            closed++;
        }
        currentTabIndex = tabs.indexOf(current);
        renderedTabCount = null;
        persistSession();
        requestChromeUpdate();
        if (closed == 0) {
            toast("Tous les autres onglets sont épinglés");
            showTabTools();
        } else toast("Fermés : " + closed + " onglets");
    }

    private void closeAllTabs() {
        BrowserTab active = currentTabIndex >= 0 && currentTabIndex < tabs.size() ? tabs.get(currentTabIndex) : null;
        for (BrowserTab tab : new ArrayList<BrowserTab>(tabs)) {
            rememberClosedTab(tab);
            if (tab != active) destroyTabView(tab, false);
        }
        tabs.clear();
        if (active == null) active = new BrowserTab();
        else scriptTabValues.removeTab(active.scriptTabId);
        tabs.add(active);
        currentTabIndex = 0;
        resetOnlyTabToHome(false);
    }

    private void showTabSearch() {
        final EditText input = new EditText(this);
        input.setSingleLine(true);
        input.setHint("Titre ou adresse");
        final AlertDialog dialog = new AlertDialog.Builder(this).setTitle("Rechercher des onglets").setView(input)
                .setPositiveButton("Rechercher", null)
                .setNegativeButton("Annuler", null).create();
        dialog.setOnCancelListener(new DialogInterface.OnCancelListener() {
            @Override public void onCancel(DialogInterface ignored) { showTabTools(); }
        });
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_NEGATIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) { dialog.dismiss(); showTabTools(); }
                });
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) {
                        String query = input.getText().toString().trim().toLowerCase(Locale.US);
                        final ArrayList<Integer> matches = new ArrayList<Integer>();
                        for (int i = 0; i < tabs.size(); i++) {
                            BrowserTab tab = tabs.get(i);
                            if (query.length() == 0 || tab.title.toLowerCase(Locale.US).contains(query) || tab.url.toLowerCase(Locale.US).contains(query)) matches.add(Integer.valueOf(i));
                        }
                        if (matches.size() == 0) { input.setError("Aucun onglet correspondant"); return; }
                        String[] labels = new String[matches.size()];
                        for (int i = 0; i < labels.length; i++) {
                            BrowserTab tab = tabs.get(matches.get(i).intValue());
                            labels[i] = safeTitle(tab.title, tab.url) + "\n" + tab.url;
                        }
                        dialog.dismiss();
                        new AlertDialog.Builder(MainActivity.this).setTitle("Onglets correspondants").setItems(labels, new DialogInterface.OnClickListener() {
                            @Override public void onClick(DialogInterface dialog, int which) { activateTab(matches.get(which).intValue()); }
                        }).setNegativeButton("Retour", new DialogInterface.OnClickListener() {
                            @Override public void onClick(DialogInterface dialog, int which) { showTabSearch(); }
                        }).setOnCancelListener(new DialogInterface.OnCancelListener() {
                            @Override public void onCancel(DialogInterface dialog) { showTabSearch(); }
                        }).show();
                    }
                });
            }
        });
        dialog.show();
    }

    private void saveCurrentTab() {
        if (tabs.size() == 0 || currentTabIndex < 0 || currentTabIndex >= tabs.size() || webView == null) return;
        BrowserTab tab = tabs.get(currentTabIndex);
        updateTabForView(webView, webView.getUrl(), webView.getTitle());
        tab.lastActiveAt = SystemClock.uptimeMillis();
    }

    private void updateCurrentTab(String url, String title) {
        if (tabs.size() == 0 || currentTabIndex < 0 || currentTabIndex >= tabs.size()) return;
        BrowserTab tab = tabs.get(currentTabIndex);
        if (url != null) tab.url = url;
        if (title != null && title.length() > 0) tab.title = title;
    }

    private void scheduleHotWebViewTrim() {
        if (hotTrimPending || webContainer == null) return;
        hotTrimPending = true;
        webContainer.postOnAnimation(new Runnable() {
            @Override public void run() {
                hotTrimPending = false;
                enforceHotWebViewLimit();
            }
        });
    }

    /** Releases an older background renderer before allocation, never after the memory peak. */
    private void makeRoomForRenderer() {
        if (deviceProfile == null) return;
        int limit = deviceProfile.hotWebViewLimit(performanceMode);
        while (liveWebViewCount() >= limit) {
            BrowserTab oldest = null;
            for (int i = 0; i < tabs.size(); i++) {
                BrowserTab candidate = tabs.get(i);
                if (i == currentTabIndex || candidate.liveView == null || candidate.liveView == webView) continue;
                if (oldest == null || candidate.lastActiveAt < oldest.lastActiveAt) oldest = candidate;
            }
            if (oldest == null) return;
            freezeTab(oldest);
        }
    }

    private void enforceHotWebViewLimit() {
        if (deviceProfile == null) return;
        int limit = deviceProfile.hotWebViewLimit(performanceMode);
        while (liveWebViewCount() > limit) {
            BrowserTab oldest = null;
            for (int i = 0; i < tabs.size(); i++) {
                BrowserTab candidate = tabs.get(i);
                if (i == currentTabIndex || candidate.liveView == null) continue;
                if (oldest == null || candidate.lastActiveAt < oldest.lastActiveAt) oldest = candidate;
            }
            if (oldest == null) break;
            freezeTab(oldest);
        }
    }

    private void freezeTab(BrowserTab tab) {
        if (tab == null || tab.liveView == null || tab.liveView == webView) return;
        WebView view = tab.liveView;
        updateTabForView(view, view.getUrl(), view.getTitle());
        tab.state = captureWebViewState(view);
        destroyTabView(tab, true);
        trimColdTabStates();
    }

    /** Prevents oversized WebView history bundles from exhausting RAM or Binder saved state. */
    private static Bundle captureWebViewState(WebView view) {
        if (view == null) return null;
        Bundle state = new Bundle();
        Parcel parcel = null;
        try {
            if (view.saveState(state) == null) return null;
            parcel = Parcel.obtain();
            state.writeToParcel(parcel, 0);
            return parcel.dataSize() <= MAX_WEBVIEW_STATE_BYTES ? state : null;
        } catch (RuntimeException ignored) {
            return null;
        } finally {
            if (parcel != null) parcel.recycle();
        }
    }

    private static boolean restoreWebViewState(WebView view, Bundle state) {
        if (view == null || state == null) return false;
        try { return view.restoreState(state) != null; }
        catch (RuntimeException ignored) { return false; }
    }

    private static boolean isBoundedTabState(Bundle state) {
        Parcel parcel = null;
        try {
            parcel = Parcel.obtain();
            state.writeToParcel(parcel, 0);
            return parcel.dataSize() <= MAX_WEBVIEW_STATE_BYTES;
        } catch (RuntimeException ignored) { return false; }
        finally { if (parcel != null) parcel.recycle(); }
    }

    private boolean isRestorableTabUrl(String url) {
        if (url == null || url.length() == 0 || url.length() > MAX_SAVED_TAB_URL_CHARS) return false;
        if (isHomeUrl(url) || isQrScannerUrl(url) || isOfflineUrl(url)) return true;
        if (!isNetworkPage(url)) return false;
        try { NetworkSecurity.parseHttpUrl(url); return true; }
        catch (Exception ignored) { return false; }
    }

    /** Only lightweight metadata belongs in the Activity parcel; background histories stay out. */
    private Bundle captureTabMetadata() {
        int count = Math.min(tabs.size(), MAX_TABS);
        if (count == 0) return null;
        int selected = Math.max(0, Math.min(currentTabIndex, count - 1));
        byte[][] urls = new byte[count][];
        byte[][] titles = new byte[count][];
        boolean[] replaced = new boolean[count];
        byte[] home = HOME_URL.getBytes(StandardCharsets.UTF_8);
        int bytes = 16 + count * 9;
        for (int i = 0; i < count; i++) {
            BrowserTab tab = tabs.get(i);
            replaced[i] = !isRestorableTabUrl(tab.url);
            urls[i] = replaced[i] ? home : tab.url.getBytes(StandardCharsets.UTF_8);
            String title = tab.title == null ? "" : tab.title;
            if (title.length() > MAX_SAVED_TAB_TITLE_CHARS) title = title.substring(0, MAX_SAVED_TAB_TITLE_CHARS);
            titles[i] = title.getBytes(StandardCharsets.UTF_8);
            bytes += urls[i].length + titles[i].length;
        }
        // Reserve ample room for Bundle/key/byte-array parcel headers. UTF-8 retains ordinary
        // ASCII URLs efficiently. If pathological URLs exceed the total budget, retain every
        // tab slot and prefer preserving the selected URL, rather than truncating valid URLs.
        while (bytes > MAX_TAB_METADATA_BYTES - 1024) {
            int largest = -1;
            for (int i = 0; i < count; i++) {
                if (i != selected && urls[i].length > home.length &&
                        (largest < 0 || urls[i].length > urls[largest].length)) largest = i;
            }
            if (largest < 0 && urls[selected].length > home.length) largest = selected;
            if (largest < 0) return null;
            bytes -= urls[largest].length - home.length;
            urls[largest] = home;
            replaced[largest] = true;
        }
        Parcel parcel = null;
        try {
            ByteArrayOutputStream buffer = new ByteArrayOutputStream(bytes);
            DataOutputStream output = new DataOutputStream(buffer);
            output.writeInt(1);
            output.writeInt(count);
            output.writeInt(selected);
            int replacements = 0;
            for (boolean value : replaced) if (value) replacements++;
            output.writeInt(replacements);
            for (int i = 0; i < count; i++) {
                output.writeInt(urls[i].length);
                output.write(urls[i]);
                output.writeInt(titles[i].length);
                output.write(titles[i]);
                output.writeBoolean(tabs.get(i).pinned);
            }
            Bundle metadata = new Bundle();
            metadata.putByteArray("data", buffer.toByteArray());
            parcel = Parcel.obtain();
            metadata.writeToParcel(parcel, 0);
            return parcel.dataSize() <= MAX_TAB_METADATA_BYTES ? metadata : null;
        } catch (IOException | RuntimeException ignored) { return null; }
        finally { if (parcel != null) parcel.recycle(); }
    }

    private static String readTabMetadataString(DataInputStream input, int maxChars) throws IOException {
        int length = input.readInt();
        if (length < 0 || length > maxChars * 4 || length > input.available()) throw new IOException("Invalid tab string");
        byte[] bytes = new byte[length];
        input.readFully(bytes);
        String value = new String(bytes, StandardCharsets.UTF_8);
        if (value.length() > maxChars) throw new IOException("Tab string too long");
        return value;
    }

    private boolean restoreTabMetadata(Bundle savedState) {
        if (savedState == null) return false;
        try {
            Bundle metadata = savedState.getBundle(STATE_TABS);
            byte[] bytes = metadata == null ? null : metadata.getByteArray("data");
            if (bytes == null || bytes.length > MAX_TAB_METADATA_BYTES - 1024) return false;
            DataInputStream input = new DataInputStream(new ByteArrayInputStream(bytes));
            if (input.readInt() != 1) return false;
            int count = input.readInt();
            int selected = input.readInt();
            int replacements = input.readInt();
            if (count < 1 || count > MAX_TABS || selected < 0 || selected >= count ||
                    replacements < 0 || replacements > count) return false;
            ArrayList<BrowserTab> restored = new ArrayList<BrowserTab>(count);
            for (int i = 0; i < count; i++) {
                BrowserTab tab = new BrowserTab();
                tab.url = readTabMetadataString(input, MAX_SAVED_TAB_URL_CHARS);
                tab.title = readTabMetadataString(input, MAX_SAVED_TAB_TITLE_CHARS);
                tab.pinned = input.readBoolean();
                if (!isRestorableTabUrl(tab.url)) return false;
                restored.add(tab);
            }
            if (input.available() != 0) return false;
            tabs.clear();
            tabs.addAll(restored);
            currentTabIndex = selected;
            BrowserTab active = tabs.get(selected);
            bindWebViewToTab(active, webView);
            active.lastActiveAt = SystemClock.uptimeMillis();
            if (replacements > 0) toast("Certaines adresses d'onglets trop longues ont été remplacées par la page d'accueil ; rouvrez-les depuis l'historique");
            return true;
        } catch (IOException | RuntimeException ignored) { return false; }
    }

    private void trimColdTabStates() {
        int limit = deviceProfile == null ? 2 : deviceProfile.coldTabStateLimit(performanceMode);
        int count = 0;
        for (int i = 0; i < tabs.size(); i++) if (i != currentTabIndex && tabs.get(i).state != null) count++;
        while (count > limit) {
            BrowserTab oldest = null;
            for (int i = 0; i < tabs.size(); i++) {
                BrowserTab candidate = tabs.get(i);
                if (i == currentTabIndex || candidate.state == null) continue;
                if (oldest == null || candidate.lastActiveAt < oldest.lastActiveAt) oldest = candidate;
            }
            if (oldest == null) return;
            oldest.state = null;
            count--;
        }
    }

    private void destroyTabView(BrowserTab tab, boolean keepState) {
        if (tab == null) return;
        if (!keepState) {
            tab.state = null;
            scriptTabValues.removeTab(tab.scriptTabId);
        }
        if (tab.liveView == null) return;
        WebView view = tab.liveView;
        tab.liveView = null;
        if (view.getParent() instanceof ViewGroup) ((ViewGroup) view.getParent()).removeView(view);
        destroyWebView(view);
    }

    private void recoverFromRendererLoss() {
        if (activityDestroyed || isFinishing() || webContainer == null) {
            rendererRecoveryPending = false;
            return;
        }
        // Renderer loss invalidates every pending page enhancement. Advance the generation
        // before replacing views so work queued for the dead renderer cannot target its replacement.
        advanceNavigationSequence();
        preparedInjection = null;
        String reloadUrl = currentPageUrl;
        if (reloadUrl == null || reloadUrl.length() == 0) reloadUrl = HOME_URL;
        if (customView != null) exitFullscreen();
        ArrayList<WebView> affected = new ArrayList<WebView>();
        for (BrowserTab tab : tabs) {
            if (tab.liveView != null && !affected.contains(tab.liveView)) {
                updateTabForView(tab.liveView, tab.liveView.getUrl(), tab.liveView.getTitle());
                affected.add(tab.liveView);
            }
            tab.liveView = null;
            tab.state = null;
        }
        for (WebView view : affected) destroyWebView(view);

        BrowserTab active = currentTabIndex >= 0 && currentTabIndex < tabs.size() ? tabs.get(currentTabIndex) : null;
        webView = createConfiguredWebView();
        applyPerformanceMode(webView);
        if (active != null) {
            bindWebViewToTab(active, webView);
            active.lastActiveAt = SystemClock.uptimeMillis();
        }
        webContainer.removeAllViews();
        webContainer.addView(webView, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        if (activityResumed) webView.onResume();
        currentPageUrl = reloadUrl;
        currentPageHost = hostOf(reloadUrl);
        pageHosts.put(webView, currentPageHost);
        adBlockActiveByView.put(webView, Boolean.valueOf(isAdBlockActiveForHost(currentPageHost)));
        rendererRecoveryPending = false;
        if (isHomeUrl(reloadUrl)) showHome();
        else if (isQrScannerUrl(reloadUrl)) showQrScannerPage();
        else loadNetworkUrl(webView, reloadUrl);
        requestChromeUpdate();
        toast("Processus de rendu web récupéré");
    }

    private void destroyWebView(WebView view) {
        if (view == null) return;
        initialNavigationGuards.remove(view);
        navigationGestureGuards.remove(view);
        navigationSourceDocuments.remove(view);
        mainFrameNavigationContexts.remove(view);
        popupSourceDocuments.remove(view);
        startedPageUrls.remove(view);
        unresponsiveWebViews.remove(view);
        scriptTabIds.remove(view);
        scriptDocumentGenerations.remove(view);
        removeDocumentStartUserScripts(view);
        removeConnectionHintScript(view);
        pageHosts.remove(view);
        adBlockActiveByView.remove(view);
        mobileUserAgents.remove(view);
        appliedSiteSettings.remove(view);
        cosmeticInjected.remove(view);
        trustedHomeViews.remove(view);
        customHomeViews.remove(view);
        adPickerViews.remove(view);
        adPickerSessions.remove(view);
        qrScannerViews.remove(view);
        renderedHomeKeys.remove(view);
        try { view.stopLoading(); } catch (RuntimeException ignored) {}
        try { view.onPause(); } catch (RuntimeException ignored) {}
        view.setOnTouchListener(null);
        view.setOnLongClickListener(null);
        view.setDownloadListener(null);
        if (Build.VERSION.SDK_INT >= 29) {
            RendererWatchdog.detach(view);
        }
        view.setWebChromeClient(null);
        view.setWebViewClient(null);
        view.destroy();
    }

    private String safeTitle(String title, String url) {
        String value = title == null || title.trim().length() == 0 ? url : title.trim();
        if (isHomeUrl(url)) value = "Accueil";
        else if (isQrScannerUrl(url)) value = "Scanner un QR code";
        return UiText.ellipsize(value, 34);
    }

    private void enterFullscreen(View view, WebChromeClient.CustomViewCallback callback) {
        if (customView != null) {
            callback.onCustomViewHidden();
            return;
        }
        customView = view;
        customViewCallback = callback;
        previousOrientation = getRequestedOrientation();
        previousSystemUi = getWindow().getDecorView().getSystemUiVisibility();
        view.setFocusable(true);
        view.setFocusableInTouchMode(true);
        browserChrome.setVisibility(View.GONE);
        rootFrame.addView(view, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        view.requestFocus(View.FOCUS_DOWN);
        getWindow().addFlags(WindowManager.LayoutParams.FLAG_FULLSCREEN | WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        setImmersiveSystemBars(true);
        rootFrame.requestApplyInsets();
        setRequestedOrientation(ActivityInfo.SCREEN_ORIENTATION_SENSOR_LANDSCAPE);
    }

    private void exitFullscreen() {
        if (customView == null) return;
        rootFrame.removeView(customView);
        customView = null;
        browserChrome.setVisibility(View.VISIBLE);
        getWindow().clearFlags(WindowManager.LayoutParams.FLAG_FULLSCREEN | WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        getWindow().getDecorView().setSystemUiVisibility(previousSystemUi);
        setImmersiveSystemBars(chromeHiddenByScroll);
        rootFrame.requestApplyInsets();
        setRequestedOrientation(previousOrientation);
        if (customViewCallback != null) customViewCallback.onCustomViewHidden();
        customViewCallback = null;
        resetWebViewTransform(webView);
        if (webView != null) webView.requestFocus(View.FOCUS_DOWN);
    }

    private boolean isSecureCredentialUrl(String url) {
        try {
            URL parsed = NetworkSecurity.parseHttpUrl(url);
            return "https".equalsIgnoreCase(parsed.getProtocol()) &&
                    parsed.getUserInfo() == null && !"median.invalid".equalsIgnoreCase(parsed.getHost());
        } catch (Exception ignored) { return false; }
    }

    private int secureCredentialPort(String url) {
        try {
            URL parsed = NetworkSecurity.parseHttpsUrl(url);
            return NetworkSecurity.effectivePort(parsed);
        } catch (Exception ignored) { return -1; }
    }

    private static boolean sameCredentialDocument(String expected, String actual) {
        return expected != null && actual != null && UrlCleaner.sameOrigin(expected, actual) &&
                navigationDocumentUrl(expected).equals(navigationDocumentUrl(actual));
    }

    private void showPasswordMenu() {
        showPasswordMenu(passwordMenuBackAction);
    }

    private void showPasswordMenu(final Runnable backAction) {
        passwordMenuBackAction = backAction;
        String[] items = new String[] {
                "Remplissage automatique : désactivé (sélectionnez un compte manuellement)",
                "Enregistrement automatique des pages : désactivé (enregistrez manuellement)",
                "Enregistrer manuellement le compte de ce site", "Remplir manuellement la page actuelle", "Gérer les mots de passe enregistrés", "Informations de sécurité sur les mots de passe"
        };
        SettingsDialogReturn back = new SettingsDialogReturn(backAction);
        AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Gestionnaire de mots de passe")
                .setItems(items, new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        if (which == 0) {
                            toast("Le remplissage automatique est désactivé, utilisez « Remplir manuellement la page actuelle »");
                            postAfterUiTransition(new Runnable() {
                                @Override public void run() { showPasswordMenu(); }
                            });
                            return;
                        }
                        if (which == 1) {
                            toast("L'enregistrement automatique des pages est désactivé, utilisez « Enregistrer manuellement le compte de ce site »");
                            postAfterUiTransition(new Runnable() {
                                @Override public void run() { showPasswordMenu(); }
                            });
                            return;
                        }
                        if (which == 5) {
                            showVaultInfo(new Runnable() {
                                @Override public void run() { showPasswordMenu(); }
                            });
                            return;
                        }
                        final int action = which;
                        if ((action == 2 || action == 3) && !requireSecurePage()) {
                            showPasswordMenu();
                            return;
                        }
                        withVaultUnlock(new Runnable() {
                            @Override public void run() {
                                if (action == 2) saveCredentialDialog();
                                else if (action == 3) chooseCredentialToFill();
                                else manageCredentials();
                            }
                        }, new Runnable() {
                            @Override public void run() { showPasswordMenu(); }
                        });
                    }
                })
                .setNegativeButton(backAction == null ? "Fermer" : "Retour", back)
                .setOnCancelListener(back)
                .create();
        secureDialog(dialog);
        dialog.show();
    }

    private void withVaultUnlock(Runnable action) {
        withVaultUnlock(action, null);
    }

    private void withVaultUnlock(Runnable action, final Runnable cancelAction) {
        if (action == null) return;
        if (SystemClock.elapsedRealtime() < vaultUnlockedUntil) { action.run(); return; }
        android.app.KeyguardManager manager = (android.app.KeyguardManager) getSystemService(KEYGUARD_SERVICE);
        if (manager == null || !manager.isDeviceSecure()) {
            SettingsDialogReturn cancel = new SettingsDialogReturn(cancelAction);
            new AlertDialog.Builder(this).setTitle("Verrouillage de l'écran requis")
                    .setMessage("Median lie désormais la clé Keystore directement à l'authentification système. Veuillez d'abord configurer un code PIN, un schéma, un mot de passe ou la biométrie ; le coffre de mots de passe n'offre aucun moyen de contournement.")
                    .setPositiveButton("Ouvrir les paramètres de sécurité", new DialogInterface.OnClickListener() {
                        @Override public void onClick(DialogInterface dialog, int which) {
                            try { startActivity(new Intent(Settings.ACTION_SECURITY_SETTINGS)); }
                            catch (Exception e) { toast("Impossible d'ouvrir les paramètres de sécurité du système"); }
                        }
                    }).setNegativeButton("Annuler", cancel).setOnCancelListener(cancel).show();
            return;
        }
        Intent unlock = manager.createConfirmDeviceCredentialIntent("Déverrouiller le coffre Median", "Confirmez l'identité de l'appareil pour continuer");
        if (unlock == null) {
            toast("Authentification système indisponible, le coffre reste verrouillé");
            continueSettingsPanel(cancelAction);
            return;
        }
        pendingVaultAction = action;
        pendingVaultCancelAction = cancelAction;
        try { startActivityForResult(unlock, VAULT_UNLOCK_REQUEST); }
        catch (Exception e) {
            pendingVaultAction = null;
            pendingVaultCancelAction = null;
            toast("Impossible d'invoquer l'authentification système");
            continueSettingsPanel(cancelAction);
        }
    }

    private boolean requireSecurePage() {
        Uri uri = currentUri();
        if (uri == null || !"https".equalsIgnoreCase(uri.getScheme()) || uri.getUserInfo() != null ||
                isInternalBrowserUrl(uri.toString())) {
            toast("Enregistrer ou remplir les mots de passe uniquement sur les sites HTTPS");
            return false;
        }
        return currentHost().length() > 0 && secureCredentialPort(currentPageUrl) > 0;
    }

    private void saveCredentialDialog() {
        if (!requireSecurePage()) return;
        final WebView source = webView;
        final String expectedUrl = currentPageUrl;
        final String expectedHost = currentHost();
        final int expectedPort = secureCredentialPort(expectedUrl);
        final EditText username = new EditText(this);
        username.setHint("Nom d'utilisateur ou e-mail");
        username.setSingleLine(true);
        final EditText password = new EditText(this);
        password.setHint("Mot de passe");
        password.setSingleLine(true);
        password.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_PASSWORD);

        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);
        content.setPadding(dp(18), 0, dp(18), 0);
        TextView host = new TextView(this);
        host.setText("Site : " + expectedHost + (expectedPort == 443 ? "" : ":" + expectedPort));
        host.setPadding(0, dp(8), 0, dp(8));
        content.addView(host);
        content.addView(username);
        content.addView(password);

        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Enregistrer le compte")
                .setView(content)
                .setPositiveButton("Enregistrer", null)
                .setNegativeButton("Annuler", new SettingsDialogReturn(new Runnable() {
                    @Override public void run() { showPasswordMenu(); }
                }))
                .create();
        dialog.setOnCancelListener(new SettingsDialogReturn(new Runnable() {
            @Override public void run() { showPasswordMenu(); }
        }));
        secureDialog(dialog);
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) {
                        final String user = username.getText().toString().trim();
                        final String pass = password.getText().toString();
                        if (source != webView || !sameCredentialDocument(expectedUrl, currentPageUrl) ||
                                !expectedHost.equalsIgnoreCase(currentHost()) ||
                                expectedPort != secureCredentialPort(currentPageUrl) ||
                                !requireSecurePage()) {
                            toast("L'origine de la page a changé, l'enregistrement a été refusé");
                            dialog.dismiss();
                            return;
                        }
                        if (user.length() == 0 || pass.length() == 0) {
                            if (user.length() == 0) username.setError("Le nom d'utilisateur ne peut pas être vide");
                            if (pass.length() == 0) password.setError("Le mot de passe ne peut pas être vide");
                            return;
                        }
                        if (user.length() > 512 || pass.length() > 8192) {
                            toast("Le compte ou le mot de passe dépasse la limite de sécurité");
                            return;
                        }
                        final Button save = dialog.getButton(AlertDialog.BUTTON_POSITIVE);
                        save.setEnabled(false);
                        services.passwords().saveCredential(expectedHost, expectedPort, user, pass, new PasswordVault.Callback<Void>() {
                            @Override public void onComplete(Void value, Exception error) {
                                if (activityDestroyed) return;
                                if (error == null) {
                                    dialog.dismiss();
                                    toast("Enregistré de manière chiffrée");
                                } else {
                                    save.setEnabled(true);
                                    toast("Échec de l'enregistrement : " + safeMessage(error));
                                }
                            }
                        });
                    }
                });
            }
        });
        dialog.show();
        webView.evaluateJavascript(CredentialAutofill.captureFieldsScript(), new ValueCallback<String>() {
            @Override public void onReceiveValue(String value) {
                if (activityDestroyed || !dialog.isShowing() || source != webView ||
                        !sameCredentialDocument(expectedUrl, currentPageUrl)) return;
                try {
                    Object decoded = new JSONTokener(value).nextValue();
                    JSONArray fields = new JSONArray(decoded instanceof String ? (String) decoded : String.valueOf(decoded));
                    if (username.getText().length() == 0) username.setText(fields.optString(0, ""));
                    if (password.getText().length() == 0) password.setText(fields.optString(1, ""));
                } catch (Exception ignored) {}
            }
        });
    }

    private void chooseCredentialToFill() {
        if (!requireSecurePage()) return;
        final String requestedHost = currentHost();
        final int requestedPort = secureCredentialPort(currentPageUrl);
        final String expectedUrl = currentPageUrl;
        final long expectedSequence = navigationSequence;
        services.passwords().forOrigin(requestedHost, requestedPort, new PasswordVault.Callback<List<PasswordVault.Credential>>() {
            @Override public void onComplete(final List<PasswordVault.Credential> credentials, Exception error) {
                if (activityDestroyed) {
                    PasswordVault.clearCredentials(credentials);
                    return;
                }
                if (error != null) {
                    PasswordVault.clearCredentials(credentials);
                    toast("Échec de la lecture du coffre : " + safeMessage(error));
                    showPasswordMenu();
                    return;
                }
                if (!requestedHost.equalsIgnoreCase(currentHost()) || expectedSequence != navigationSequence ||
                        requestedPort != secureCredentialPort(currentPageUrl) ||
                        !sameCredentialDocument(expectedUrl, currentPageUrl)) {
                    PasswordVault.clearCredentials(credentials);
                    toast("La page a changé, veuillez sélectionner à nouveau le compte");
                    showPasswordMenu();
                    return;
                }
                if (credentials == null || credentials.size() == 0) {
                    PasswordVault.clearCredentials(credentials);
                    toast("Aucun compte enregistré pour ce site");
                    showPasswordMenu();
                    return;
                }
                String[] names = new String[credentials.size()];
                for (int i = 0; i < credentials.size(); i++) names[i] = credentials.get(i).username;
                SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
                    @Override public void run() { showPasswordMenu(); }
                });
                AlertDialog dialog = new AlertDialog.Builder(MainActivity.this)
                        .setTitle("Choisir un compte")
                        .setItems(names, new DialogInterface.OnClickListener() {
                            @Override public void onClick(DialogInterface dialog, int which) {
                                // The dialog's dismiss listener clears the backing list. Pass an
                                // independent copy so the async WebView callback can still validate
                                // the credential after the list is wiped.
                                fillCredentialOnPage(webView, expectedUrl, credentials.get(which).copy(), false, expectedSequence);
                            }
                        }).setNegativeButton("Retour", back).setOnCancelListener(back)
                        .create();
                dialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
                    @Override public void onDismiss(DialogInterface ignored) {
                        PasswordVault.clearCredentials(credentials);
                    }
                });
                secureDialog(dialog);
                dialog.show();
            }
        });
    }

    private void fillCredential(PasswordVault.Credential credential) {
        if (!requireSecurePage()) return;
        fillCredentialOnPage(webView, currentPageUrl, credential, false, navigationSequence);
    }

    private void fillCredentialOnPage(final WebView target, final String expectedUrl,
                                      PasswordVault.Credential credential, final boolean automatic) {
        fillCredentialOnPage(target, expectedUrl, credential, automatic, navigationSequence);
    }

    private void fillCredentialOnPage(final WebView target, final String expectedUrl,
                                      PasswordVault.Credential credential, final boolean automatic,
                                      final long expectedSequence) {
        if (target == null || target != webView || credential == null ||
                expectedSequence != navigationSequence ||
                !isSecureCredentialUrl(target.getUrl()) ||
                !credential.host.equalsIgnoreCase(currentHost()) ||
                credential.port != secureCredentialPort(currentPageUrl) ||
                credential.port != secureCredentialPort(target.getUrl()) ||
                !credential.host.equalsIgnoreCase(hostOf(target.getUrl())) ||
                !sameCredentialDocument(expectedUrl, target.getUrl())) {
            if (!automatic) toast("Le site ou la page a changé, remplissage refusé");
            return;
        }
        try {
            target.evaluateJavascript(CredentialAutofill.fillScript(
                            credential.username, credential.password, !automatic),
                    new ValueCallback<String>() {
                @Override public void onReceiveValue(String value) {
                    if (target != webView || expectedSequence != navigationSequence ||
                            !isSecureCredentialUrl(currentPageUrl) ||
                            !credential.host.equalsIgnoreCase(currentHost()) ||
                            credential.port != secureCredentialPort(currentPageUrl) ||
                            credential.port != secureCredentialPort(target.getUrl()) ||
                            !credential.host.equalsIgnoreCase(hostOf(target.getUrl())) ||
                            !isSecureCredentialUrl(target.getUrl()) ||
                            !sameCredentialDocument(expectedUrl, currentPageUrl) ||
                            !sameCredentialDocument(expectedUrl, target.getUrl())) return;
                    boolean filled = false;
                    try {
                        Object decoded = new JSONTokener(value == null ? "{}" : value).nextValue();
                        JSONObject state = new JSONObject(decoded instanceof String ? (String) decoded : String.valueOf(decoded));
                        filled = state.optBoolean("filled", false);
                    } catch (Exception ignored) {}
                    if (filled) toast(automatic ? "Remplissage automatique effectué, veuillez vérifier puis vous connecter" : "Formulaire rempli, veuillez vérifier puis vous connecter");
                    else if (!automatic) toast("Aucun champ de mot de passe de connexion pouvant être rempli en toute sécurité sur cette page");
                }
            });
        } catch (RuntimeException ignored) {
            if (!automatic) toast("Impossible de remplir cette page pour le moment");
        }
    }

    private void manageCredentials() {
        services.passwords().getAll(new PasswordVault.Callback<List<PasswordVault.Credential>>() {
            @Override public void onComplete(final List<PasswordVault.Credential> all, Exception error) {
                if (activityDestroyed) {
                    PasswordVault.clearCredentials(all);
                    return;
                }
                if (error != null) {
                    PasswordVault.clearCredentials(all);
                    toast("Échec de la lecture du coffre : " + safeMessage(error));
                    showPasswordMenu();
                    return;
                }
                if (all == null || all.size() == 0) {
                    PasswordVault.clearCredentials(all);
                    toast("Le coffre est vide");
                    showPasswordMenu();
                    return;
                }
                String[] names = new String[all.size()];
                for (int i = 0; i < all.size(); i++) names[i] = all.get(i).host + "\n" + all.get(i).username;
                SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
                    @Override public void run() { showPasswordMenu(); }
                });
                AlertDialog dialog = new AlertDialog.Builder(MainActivity.this)
                        .setTitle("Compte enregistré")
                        .setItems(names, new DialogInterface.OnClickListener() {
                            @Override public void onClick(DialogInterface dialog, int which) {
                                showCredentialActions(all.get(which).copy());
                            }
                        })
                        .setNegativeButton("Retour", back)
                        .setOnCancelListener(back)
                        .create();
                dialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
                    @Override public void onDismiss(DialogInterface ignored) {
                        PasswordVault.clearCredentials(all);
                    }
                });
                secureDialog(dialog);
                dialog.show();
            }
        });
    }

    private void showCredentialActions(final PasswordVault.Credential credential) {
        if (credential == null) {
            manageCredentials();
            return;
        }
        final boolean canFill = isSecureCredentialUrl(currentPageUrl) &&
                credential.port == secureCredentialPort(currentPageUrl) &&
                credential.host.equalsIgnoreCase(currentHost());
        String[] actions = new String[] {
                canFill ? "Remplir la page actuelle" : "Ouvrir ce site",
                "Copier le nom d'utilisateur",
                "Supprimer le compte"
        };
        SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
            @Override public void run() { manageCredentials(); }
        });
        AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Actions du compte")
                .setMessage(credential.host + (credential.port == 443 ? "" : ":" + credential.port) + "\n" + credential.username)
                .setItems(actions, new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface ignored, int which) {
                        if (which == 0) {
                            if (canFill) fillCredential(credential);
                            else loadInput("https://" + credential.host +
                                    (credential.port == 443 ? "" : ":" + credential.port));
                        } else if (which == 1) {
                            ClipboardManager clipboard = (ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
                            if (clipboard != null) {
                                clipboard.setPrimaryClip(ClipData.newPlainText("Nom d'utilisateur Median", credential.username));
                                toast("Nom d'utilisateur copié");
                            }
                            postAfterUiTransition(new Runnable() {
                                @Override public void run() { manageCredentials(); }
                            });
                        } else {
                            confirmDeleteCredential(credential.copy());
                        }
                    }
                })
                .setNegativeButton("Retour", back)
                .setOnCancelListener(back)
                .create();
        dialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
            @Override public void onDismiss(DialogInterface ignored) { credential.clear(); }
        });
        secureDialog(dialog);
        dialog.show();
    }

    private void confirmDeleteCredential(final PasswordVault.Credential credential) {
        SettingsDialogReturn back = new SettingsDialogReturn(new Runnable() {
            @Override public void run() { manageCredentials(); }
        });
        AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Supprimer le compte ?")
                .setMessage(credential.host + (credential.port == 443 ? "" : ":" + credential.port) + "\n" + credential.username)
                .setPositiveButton("Supprimer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        services.passwords().delete(credential.id, new PasswordVault.Callback<Void>() {
                            @Override public void onComplete(Void value, Exception error) {
                                if (activityDestroyed) return;
                                if (error == null) toast("Supprimé");
                                else toast("Échec de la suppression : " + safeMessage(error));
                                manageCredentials();
                            }
                        });
                    }
                })
                .setNegativeButton("Annuler", back)
                .setOnCancelListener(back)
                .create();
        dialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
            @Override public void onDismiss(DialogInterface ignored) {
                if (credential != null) credential.clear();
            }
        });
        secureDialog(dialog);
        dialog.show();
    }

    private void showVaultInfo(final Runnable returnAction) {
        SettingsDialogReturn back = new SettingsDialogReturn(returnAction);
        new AlertDialog.Builder(this)
                .setTitle("Informations de sécurité sur les mots de passe")
                .setMessage("Les mots de passe sont chiffrés avec AES-GCM, la clé est protégée par Android Keystore et le déverrouillage requiert l'authentification système ; la sauvegarde par le système est interdite pour l'application.\n\nLe remplissage doit être lancé manuellement depuis le menu des mots de passe du navigateur, correspond uniquement aux hôtes HTTPS, ne remplit jamais les champs de nouveau mot de passe, de confirmation ou de code de vérification, et ne soumet jamais automatiquement.\n\nLe coffre n'a pas encore fait l'objet d'un audit de sécurité indépendant : n'y conservez pas les mots de passe de comptes financiers ou de messagerie principale.")
                .setPositiveButton("Compris", back)
                .setOnCancelListener(back)
                .show();
    }

    private void secureDialog(final AlertDialog dialog) {
        if (dialog != null && dialog.getWindow() != null)
            dialog.getWindow().addFlags(WindowManager.LayoutParams.FLAG_SECURE);
    }

    private void showFindDialog() {
        final WebView target = webView;
        if (target == null) return;
        final EditText input = new EditText(this);
        input.setSingleLine(true);
        input.setHint("Saisir le texte à rechercher");
        input.setContentDescription("Rechercher dans le contenu de la page");
        input.setImeOptions(EditorInfo.IME_ACTION_SEARCH);
        input.setPadding(dp(18), dp(8), dp(18), dp(8));
        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Rechercher dans la page")
                .setView(input)
                .setPositiveButton("Rechercher", null)
                .setNegativeButton("Annuler", null)
                .create();
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) {
                        String query = input.getText().toString().trim();
                        if (query.length() == 0) {
                            input.setError("Veuillez saisir le texte à rechercher");
                            return;
                        }
                        if (target != webView) {
                            toast("La page a changé, veuillez relancer la recherche");
                            dialog.dismiss();
                            return;
                        }
                        dialog.dismiss();
                        target.clearMatches();
                        target.findAllAsync(query);
                        target.showFindDialog(query, false);
                    }
                });
            }
        });
        dialog.show();
    }

    private void sharePage() {
        String url = webView.getUrl();
        if (!isNetworkPage(url)) return;
        Intent share = new Intent(Intent.ACTION_SEND);
        share.setType("text/plain");
        share.putExtra(Intent.EXTRA_TEXT, (webView.getTitle() == null ? "" : webView.getTitle() + "\n") + url);
        startActivity(Intent.createChooser(share, "Partager la page"));
    }

    private void showStoragePanel(final Runnable backAction) {
        toast("Calcul des données de navigation");
        executeTask(scriptExecutor, new Runnable() {
            @Override public void run() {
                final StoragePolicy.Snapshot snapshot = StoragePolicy.snapshot(MainActivity.this);
                uiHandler.post(new Runnable() {
                    @Override public void run() { showStorageSnapshot(snapshot, backAction); }
                });
            }
        });
    }

    private void showStorageSnapshot(final StoragePolicy.Snapshot snapshot, final Runnable backAction) {
        String subtitle = "Total : " + StoragePolicy.format(snapshot.totalBytes) +
                " · cache temporaire " + StoragePolicy.format(snapshot.transientBytes) +
                " · sites et paramètres " + StoragePolicy.format(snapshot.siteBytes);
        String[] items = new String[] {
                "Nettoyer le cache temporaire (en conservant la connexion)",
                "Effacer les cookies et les données de site (déconnexion possible)",
                "Effacer toutes les données de navigation",
                "Recalculer"
        };
        int[] icons = new int[] { BrowserIconView.RELOAD, BrowserIconView.SHIELD, BrowserIconView.CLOSE, BrowserIconView.SEARCH };
        showActionSheet("Stockage et données", subtitle, items, icons, null, null, backAction, new SheetHandler() {
            @Override public void onItem(int which) {
                if (which == 0) {
                    webView.clearCache(true);
                    clearConnectionHints();
                    toast("Cache temporaire nettoyé");
                    showStoragePanel(backAction);
                } else if (which == 1) {
                    CookieManager.getInstance().removeAllCookies(null);
                    CookieManager.getInstance().flush();
                    android.webkit.WebStorage.getInstance().deleteAllData();
                    toast("Cookies et données de site effacés");
                    showStoragePanel(backAction);
                } else if (which == 2) {
                    confirmClearData(new Runnable() {
                        @Override public void run() { showStoragePanel(backAction); }
                    });
                } else {
                    showStoragePanel(backAction);
                }
            }
        });
    }

    private void maybeTrimTransientCache() {
        if (scriptExecutor == null || scriptExecutor.isShutdown()) return;
        if (isMediaCompatibilityHost(currentPageHost)) return;
        long now = System.currentTimeMillis();
        long last = prefs.getLong("last_cache_check", 0L);
        if (now - last < 24L * 60L * 60L * 1000L) return;
        prefs.edit().putLong("last_cache_check", now).apply();
        final String mode = performanceMode;
        executeTask(scriptExecutor, new Runnable() {
            @Override public void run() {
                StoragePolicy.Snapshot snapshot = StoragePolicy.snapshot(MainActivity.this);
                long budget = StoragePolicy.budgetBytes(MainActivity.this, mode);
                final boolean substantiallyOverBudget = snapshot.transientBytes > budget + budget / 4L;
                if (!substantiallyOverBudget) return;
                uiHandler.post(new Runnable() {
                    @Override public void run() {
                        if (webView != null) webView.clearCache(false);
                    }
                });
            }
        });
    }

    private void confirmClearData(final Runnable returnAction) {
        SettingsDialogReturn back = new SettingsDialogReturn(returnAction);
        new AlertDialog.Builder(this)
                .setTitle("Effacer les données de navigation")
                .setMessage("Cela effacera les cookies, le cache, les formulaires, l'authentification HTTP, l'historique, l'index des téléchargements, les autorisations de sites et le stockage local. Les fichiers téléchargés, signets, pages hors ligne, mots de passe et scripts utilisateur ne seront pas supprimés.")
                .setPositiveButton("Effacer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        CookieManager.getInstance().removeAllCookies(new ValueCallback<Boolean>() {
                            @Override public void onReceiveValue(Boolean value) { CookieManager.getInstance().flush(); }
                        });
                        for (BrowserTab tab : tabs) if (tab.liveView != null) {
                            tab.liveView.clearCache(true);
                            tab.liveView.clearFormData();
                            tab.liveView.clearHistory();
                        }
                        if (dataStore != null) dataStore.clearHistory();
                        clearConnectionHints();
                        services.downloads().clear();
                        if (siteSettingsStore != null) siteSettingsStore.clearAll();
                        appliedSiteSettings.clear();
                        for (BrowserTab tab : tabs) if (tab.liveView != null) applySiteSettings(tab.liveView, pageHostFor(tab.liveView));
                        android.webkit.WebStorage.getInstance().deleteAllData();
                        android.webkit.GeolocationPermissions.getInstance().clearAll();
                        android.webkit.WebViewDatabase database = android.webkit.WebViewDatabase.getInstance(MainActivity.this);
                        database.clearHttpAuthUsernamePassword();
                        database.clearFormData();
                        toast("Données de navigation effacées");
                        continueSettingsPanel(returnAction);
                    }
                })
                .setNegativeButton("Annuler", back)
                .setOnCancelListener(back)
                .show();
    }

    private void clearDataForExit() {
        if (exitDataCleared) return;
        exitDataCleared = true;
        clearConnectionHints();
        try {
            CookieManager.getInstance().removeAllCookies(null);
            CookieManager.getInstance().flush();
        } catch (RuntimeException ignored) {}
        try { WebStorage.getInstance().deleteAllData(); } catch (RuntimeException ignored) {}
        for (BrowserTab tab : tabs) if (tab.liveView != null) {
            try { tab.liveView.clearCache(true); } catch (RuntimeException ignored) {}
            try { tab.liveView.clearFormData(); } catch (RuntimeException ignored) {}
            try { tab.liveView.clearHistory(); } catch (RuntimeException ignored) {}
        }
        if (dataStore != null) dataStore.clearHistory();
        if (dataStore != null) dataStore.clearSession();
        if (siteSettingsStore != null) siteSettingsStore.clearAll();
        try { GeolocationPermissions.getInstance().clearAll(); } catch (RuntimeException ignored) {}
        try { WebViewDatabase.getInstance(this).clearHttpAuthUsernamePassword(); } catch (RuntimeException ignored) {}
    }

    private void showCommunityNoticeOnFirstLaunch(Bundle state) {
        if (state != null || prefs.getBoolean(PREF_COMMUNITY_NOTICE_SHOWN, false)) return;
        prefs.edit().putBoolean(PREF_COMMUNITY_NOTICE_SHOWN, true).apply();
        // Never put a large dialog allocation into the launch/first-interaction window.
        uiHandler.postDelayed(new Runnable() {
            @Override public void run() {
                if (isFinishing() || (Build.VERSION.SDK_INT >= 17 && isDestroyed())) return;
                showCommunityNotice();
            }
        }, 2400L);
    }

    private void showCommunityNotice() {
        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Bienvenue dans Median Browser")
                .setMessage("Léger, local d'abord, sans publicité ni télémétrie.\n\n" + COMMUNITY_INFO)
                .setPositiveButton("Commencer", null)
                .create();
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) { enableDialogLinks(dialog); }
        });
        dialog.show();
    }

    private void enableDialogLinks(AlertDialog dialog) {
        TextView message = dialog.findViewById(android.R.id.message);
        if (message == null) return;
        android.text.util.Linkify.addLinks(message, android.text.util.Linkify.WEB_URLS);
        message.setMovementMethod(android.text.method.LinkMovementMethod.getInstance());
        message.setLinksClickable(true);
    }

    private void showAbout() {
        showAbout(null);
    }

    private void showAbout(final Runnable returnAction) {
        String profile = deviceProfile == null ? "Politique de l'appareil : non initialisée" : deviceProfile.summary();
        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Median Browser " + appVersionName())
                .setMessage("Léger, sans publicité, sans SDK d'analyse ni de télémétrie.\n\n" + profile
                        + "\n\nLes capacités web dépendent de la WebView système Android.\n\n" + COMMUNITY_INFO)
                .setPositiveButton("OK", null)
                .setNeutralButton("Notes de confidentialité", null)
                .setNegativeButton("Diagnostic de compatibilité", null)
                .create();
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                enableDialogLinks(dialog);
                Button privacy = dialog.getButton(AlertDialog.BUTTON_NEUTRAL);
                if (privacy != null) privacy.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) { showPrivacyNotice(); }
                });
                Button diagnostics = dialog.getButton(AlertDialog.BUTTON_NEGATIVE);
                if (diagnostics != null) diagnostics.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) { showCompatibilityDiagnostics(); }
                });
            }
        });
        dialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
            @Override public void onDismiss(DialogInterface ignored) {
                continueSettingsPanel(returnAction);
            }
        });
        dialog.show();
    }

    private void showCompatibilityDiagnostics() {
        final String report = WebViewCompat.getDocumentStartDiagnosticReport()
                + "\n\nEn l'absence de prise en charge de document-start, un repli sécurisé est utilisé ; sans pont de confiance, les capacités cross-origin, de téléchargement et de presse-papiers sont désactivées.\n\nDernière première navigation :\n"
                + prefs.getString(PREF_STARTUP_DIAGNOSTIC, "Aucun enregistrement de première navigation réseau");
        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle("Diagnostic de compatibilité WebView")
                .setMessage(report)
                .setPositiveButton("Exécuter l'auto-test d'injection", null)
                .setNeutralButton("Copier", null)
                .setNegativeButton("Fermer", null)
                .create();
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                Button copy = dialog.getButton(AlertDialog.BUTTON_NEUTRAL);
                if (copy != null) copy.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) {
                        ClipboardManager clipboard = (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
                        if (clipboard != null) {
                            clipboard.setPrimaryClip(ClipData.newPlainText("Median WebView diagnostics", report));
                            toast("Informations de diagnostic copiées");
                        }
                    }
                });
                Button test = dialog.getButton(AlertDialog.BUTTON_POSITIVE);
                if (test != null) test.setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View v) { runDocumentStartSelfTest(); }
                });
            }
        });
        dialog.show();
    }

    private void runDocumentStartSelfTest() {
        if (activityDestroyed || rootFrame == null) return;
        if (!WebViewFeature.isFeatureSupported(WebViewFeature.DOCUMENT_START_SCRIPT)) {
            toast("La WebView système actuelle ne prend pas en charge l'injection document-start sécurisée");
            return;
        }
        final WebView probe = new WebView(this);
        final String token = UrlCleaner.randomToken();
        final ScriptHandler[] registration = new ScriptHandler[1];
        final boolean[] finished = new boolean[] { false };
        WebSettings settings = probe.getSettings();
        settings.setJavaScriptEnabled(true);
        settings.setAllowFileAccess(false);
        settings.setAllowContentAccess(false);
        settings.setMixedContentMode(WebSettings.MIXED_CONTENT_NEVER_ALLOW);
        probe.setAlpha(0f);
        rootFrame.addView(probe, new FrameLayout.LayoutParams(1, 1));

        final Runnable cleanup = new Runnable() {
            @Override public void run() {
                if (finished[0]) return;
                finished[0] = true;
                if (registration[0] != null) try { registration[0].remove(); } catch (RuntimeException ignored) {}
                if (probe.getParent() instanceof ViewGroup) ((ViewGroup) probe.getParent()).removeView(probe);
                try { probe.stopLoading(); } catch (RuntimeException ignored) {}
                probe.destroy();
            }
        };

        probe.setWebViewClient(new WebViewClient() {
            @Override public void onPageFinished(WebView view, String url) {
                view.evaluateJavascript("String(window.__medianCompatOrder||'missing')", new ValueCallback<String>() {
                    @Override public void onReceiveValue(String value) {
                        boolean passed = value != null && value.contains("before");
                        cleanup.run();
                        if (!activityDestroyed)
                            toast(passed ? "Auto-test document-start réussi" : "Auto-test document-start échoué, repli sécurisé conservé");
                    }
                });
            }
        });
        try {
            registration[0] = WebViewCompat.addDocumentStartJavaScript(
                    probe, "window.__medianCompatToken=" + JSONObject.quote(token) + ";",
                    "https://median-compat.invalid");
            String html = "<!doctype html><meta charset=utf-8><script>"
                    + "window.__medianCompatOrder=(window.__medianCompatToken===" + JSONObject.quote(token)
                    + ")?'before':'after';</script>compat";
            probe.loadDataWithBaseURL("https://median-compat.invalid/", html, "text/html", "UTF-8", null);
            uiHandler.postDelayed(new Runnable() {
                @Override public void run() {
                    if (finished[0]) return;
                    cleanup.run();
                    if (!activityDestroyed) toast("Auto-test document-start expiré, repli sécurisé conservé");
                }
            }, 6000L);
        } catch (RuntimeException error) {
            cleanup.run();
            toast("Impossible de démarrer l'auto-test : " + safeMessage(error));
        }
    }

    private String appVersionName() {
        try {
            PackageInfo info = getPackageManager().getPackageInfo(getPackageName(), 0);
            return info.versionName == null ? "" : info.versionName;
        } catch (Exception ignored) { return ""; }
    }

    private void showPrivacyNotice() {
        new AlertDialog.Builder(this)
                .setTitle("Confidentialité et traitement des données")
                .setMessage("Signets, historique, onglets, paramètres, scripts et règles de filtrage sont stockés localement ; Median ne contient aucune publicité, analyse, télémétrie ou service de synchronisation.\n\nLes sites, recherches, traductions et abonnements reçoivent des requêtes réseau normales. La caméra, le microphone et la position ne sont fournis que sur les pages HTTPS et après votre autorisation.\n\nLe coffre de mots de passe utilise Keystore et AES-GCM. Les scripts utilisateur sont du code tiers : installez uniquement des scripts de confiance. Conservez précieusement vos fichiers exportés.")
                .setPositiveButton("Compris", null)
                .show();
    }

    private void setSearchEngine(String engine) {
        if (searchEngines == null || !searchEngines.contains(engine)) engine = "google";
        searchEngine = engine;
        prefs.edit().putString("search_engine", searchEngine).apply();
        cachedHomeKey = "";
    }

    private void applyPerformanceMode() {
        for (BrowserTab tab : tabs) if (tab.liveView != null) applyPerformanceMode(tab.liveView);
        enforceHotWebViewLimit();
    }

    private void applyPerformanceMode(WebView target) {
        if (target == null) return;
        applyPerformanceMode(target, target.getSettings());
    }

    private void applyPerformanceMode(WebView target, WebSettings settings) {
        settings.setCacheMode(WebSettings.LOAD_DEFAULT);

        settings.setDomStorageEnabled(true);
        settings.setDatabaseEnabled(true);
        // Chromium rasterizes visible content on demand. Hidden hot tabs do not need
        // pre-rasterized tiles competing with the active page for memory and GPU work.
        settings.setOffscreenPreRaster(false);
        settings.setLoadsImagesAutomatically(true);

        try {
            // Only the visible renderer stays IMPORTANT. Hot background tabs remain
            // restorable but cannot compete at the same OOM/CPU scheduling class.
            boolean active = target == webView;
            target.setRendererPriorityPolicy(active ? WebView.RENDERER_PRIORITY_IMPORTANT : WebView.RENDERER_PRIORITY_BOUND, !active);
        } catch (RuntimeException ignored) {
        }
    }

    private void applyDesktopMode() {
        for (BrowserTab tab : tabs) if (tab.liveView != null) applyDesktopMode(tab.liveView);
    }

    private void applyDesktopMode(WebView target) {
        if (target == null) return;
        WebSettings settings = target.getSettings();
        applyDesktopMode(target, settings, settings.getUserAgentString());
    }

    private void applyDesktopMode(WebView target, WebSettings settings) {
        applyDesktopMode(target, settings, settings.getUserAgentString());
    }

    private void applyDesktopMode(WebView target, WebSettings settings, String currentUserAgent) {
        SiteSettingsStore.SiteSettings site = siteSettingsStore == null ? new SiteSettingsStore.SiteSettings() : siteSettingsStore.forHost(pageHostFor(target));
        int desktop = site.get(SiteSettingsStore.DESKTOP);
        boolean enabled = desktop == SiteSettingsStore.ALLOW || (desktop == SiteSettingsStore.INHERIT && desktopMode);
        String mobile = mobileUserAgents.get(target);
        if (mobile == null || mobile.length() == 0) {
            mobile = WebViewPolicy.mobileUserAgent(currentUserAgent);
            mobileUserAgents.put(target, mobile);
        }
        String desiredUserAgent = mobile;
        if (enabled) {
            desiredUserAgent = desktopUserAgent(mobile);
            settings.setUseWideViewPort(true);
            settings.setLoadWithOverviewMode(true);
        } else {
            settings.setUseWideViewPort(false);
            settings.setLoadWithOverviewMode(false);
        }
        if (!desiredUserAgent.equals(currentUserAgent)) settings.setUserAgentString(desiredUserAgent);
    }

    private String desktopUserAgent(String mobile) {
        String chrome = "Chrome/120.0.0.0";
        int start = mobile == null ? -1 : mobile.indexOf("Chrome/");
        if (start >= 0) {
            int end = mobile.indexOf(' ', start);
            chrome = mobile.substring(start, end < 0 ? mobile.length() : end);
        }
        return "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) " + chrome + " Safari/537.36";
    }

    private void applySiteSettings(WebView target, String host) {
        if (target == null) return;
        String normalized = host == null ? "" : host;
        pageHosts.put(target, normalized);
        if (target == webView) currentPageHost = normalized;
        adBlockActiveByView.put(target, Boolean.valueOf(isAdBlockActiveForHost(normalized)));
        SiteSettingsStore.SiteSettings site = siteSettingsStore == null ? new SiteSettingsStore.SiteSettings() : siteSettingsStore.forHost(normalized);
        String configKey = normalized + '|' + site.packedStates() +
                '|' + desktopMode + '|' + nightMode + '|' + acceptThirdPartyCookies;
        if (configKey.equals(appliedSiteSettings.get(target))) return;
        WebSettings settings = target.getSettings();
        boolean compatibility = site.compatibilityMode();
        settings.setMixedContentMode(compatibility ? WebSettings.MIXED_CONTENT_COMPATIBILITY_MODE : WebSettings.MIXED_CONTENT_NEVER_ALLOW);
        int javascript = site.get(SiteSettingsStore.JAVASCRIPT);
        int images = site.get(SiteSettingsStore.IMAGES);
        int popups = site.get(SiteSettingsStore.POPUPS);
        int autoplay = site.get(SiteSettingsStore.AUTOPLAY);
        int thirdPartyCookies = site.get(SiteSettingsStore.THIRD_PARTY_COOKIES);
        settings.setJavaScriptEnabled(javascript != SiteSettingsStore.BLOCK);
        settings.setLoadsImagesAutomatically(images != SiteSettingsStore.BLOCK);
        settings.setBlockNetworkImage(images == SiteSettingsStore.BLOCK);
        settings.setTextZoom(site.textZoom());
        settings.setSupportMultipleWindows(compatibility || popups != SiteSettingsStore.BLOCK);
        settings.setJavaScriptCanOpenWindowsAutomatically(popups == SiteSettingsStore.ALLOW);
        settings.setMediaPlaybackRequiresUserGesture(autoplay != SiteSettingsStore.ALLOW);
        boolean allowThirdParty = compatibility || thirdPartyCookies == SiteSettingsStore.ALLOW ||
                (thirdPartyCookies == SiteSettingsStore.INHERIT && acceptThirdPartyCookies);
        CookieManager.getInstance().setAcceptThirdPartyCookies(target, allowThirdParty);
        applyDesktopMode(target, settings);
        applyDarkMode(target, settings);
        appliedSiteSettings.put(target, configKey);
    }

    private boolean shouldCleanTracking(String host) {
        SiteSettingsStore.SiteSettings site = siteSettingsStore == null ? null : siteSettingsStore.forHost(host);
        if (site != null && site.compatibilityMode()) return false;
        int tracking = site == null ? SiteSettingsStore.INHERIT : site.get(SiteSettingsStore.TRACKING_PROTECTION);
        return tracking == SiteSettingsStore.ALLOW ||
                (tracking == SiteSettingsStore.INHERIT && cleanTrackingParameters);
    }

    private void applyCookiePolicyToAll() {
        for (BrowserTab tab : tabs) {
            if (tab.liveView == null) continue;
            appliedSiteSettings.remove(tab.liveView);
            applySiteSettings(tab.liveView, pageHostFor(tab.liveView));
        }
        scheduleCookieFlush();
    }

    private void toggleNightMode() {
        nightMode = !nightMode;
        prefs.edit().putBoolean("night_mode", nightMode).apply();

        // Immediately update all backgrounds before re-rendering content
        applyDarkMode();

        // Update WebView background color immediately to prevent flash
        if (webView != null) {
            webView.setBackgroundColor(nightMode ? DARK_WEB : WHITE);
        }

        // Update all tab backgrounds
        for (BrowserTab tab : tabs) {
            if (tab.liveView != null) {
                tab.liveView.setBackgroundColor(nightMode ? DARK_WEB : WHITE);
            }
        }

        // Clear cached home render key to force regeneration with new theme
        cachedHomeKey = "";
        renderedHomeKeys.clear();

        // Re-render content after backgrounds are updated
        String activeUrl = webView == null ? currentPageUrl : webView.getUrl();
        if (activeUrl == null || activeUrl.length() == 0) activeUrl = currentPageUrl;
        homeThemeRepairPending = true;
        if (isHomeUrl(activeUrl)) {
            // Rewrite the current home document so the previous theme cannot remain in the
            // WebView back stack as a stale page.
            showHome(true);
        } else if (isQrScannerUrl(activeUrl)) {
            showQrScannerPage();
        } else if (webView != null && isInternalBrowserUrl(activeUrl)) {
            // Reload internal pages (settings, etc.) to apply new theme
            reloadWebView(webView);
        } else if (webView != null && isNetworkPage(activeUrl)) {
            // Re-apply the complete site policy so WebView providers that cache the darkening
            // flag do not leave a light surface behind after a live theme switch.
            appliedSiteSettings.remove(webView);
            applySiteSettings(webView, hostOf(activeUrl));
            webView.postInvalidateOnAnimation();
        }
    }

    private void applyDarkMode() {
        applyThemeSignal();
        for (BrowserTab tab : tabs) if (tab.liveView != null) applyDarkMode(tab.liveView);
        applyChromeTheme();
        refreshActiveSheetTheme();
    }

    private void applyThemeSignal() {
        try { getTheme().applyStyle(nightMode ? R.style.AppThemeSignalDark : R.style.AppThemeSignalLight, true); }
        catch (RuntimeException ignored) {}
    }

    private void applyChromeTheme() {
        if (browserChrome == null || topBar == null || bottomBar == null || addressPill == null || addressBar == null) return;
        int background = nightMode ? DARK_BACKGROUND : WHITE;
        int surface = nightMode ? DARK_SURFACE : SURFACE;
        int foreground = nightMode ? DARK_TEXT : TEXT;
        int hint = nightMode ? DARK_MUTED : 0xff80868b;
        if (rootFrame != null) rootFrame.setBackgroundColor(background);
        browserChrome.setBackgroundColor(background);
        topBar.setBackgroundColor(background);
        bottomBar.setBackgroundColor(background);
        if (statusBarBackground != null) statusBarBackground.setBackgroundColor(background);
        if (navigationBarBackground != null) navigationBarBackground.setBackgroundColor(background);
        if (webContainer != null) {
            int webBackground = nightMode ? DARK_WEB : WHITE;
            webContainer.setBackgroundColor(webBackground);
            // During the short WebView construction window the container still owns the
            // startup surface. Repaint that child as well so a live toggle cannot leave a
            // bright rectangle behind the dark chrome.
            for (int i = 0; i < webContainer.getChildCount(); i++) {
                View child = webContainer.getChildAt(i);
                if (child != null && child != webView) child.setBackgroundColor(webBackground);
            }
        }
        addressPill.setBackground(roundRect(surface, 999));
        addressBar.setTextColor(foreground);
        addressBar.setHintTextColor(hint);
        tintIconTree(topBar, foreground);
        tintIconTree(bottomBar, foreground);
        Window window = getWindow();
        if (Build.VERSION.SDK_INT >= 30) {
            window.setStatusBarColor(Color.TRANSPARENT);
            window.setNavigationBarColor(Color.TRANSPARENT);
            android.view.WindowInsetsController controller = window.getInsetsController();
            if (controller != null) {
                int appearance = nightMode ? 0 : (android.view.WindowInsetsController.APPEARANCE_LIGHT_STATUS_BARS |
                        android.view.WindowInsetsController.APPEARANCE_LIGHT_NAVIGATION_BARS);
                controller.setSystemBarsAppearance(appearance,
                        android.view.WindowInsetsController.APPEARANCE_LIGHT_STATUS_BARS |
                        android.view.WindowInsetsController.APPEARANCE_LIGHT_NAVIGATION_BARS);
            }
        } else {
            window.setStatusBarColor(background);
            window.setNavigationBarColor(background);
        }
        if (Build.VERSION.SDK_INT < 30) {
            int flags = 0;
            if (!nightMode) {
                flags |= View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR;
                flags |= View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR;
            }
            window.getDecorView().setSystemUiVisibility(flags);
        }
        setImmersiveSystemBars(chromeHiddenByScroll);
    }

    private void refreshActiveSheetTheme() {
        if (activeOverlayPanel != null && activeOverlaySheet) themeSheetTree(activeOverlayPanel);
    }

    private void themeSheetTree(View view) {
        if (view == null) return;
        int surface = nightMode ? DARK_SHEET : WHITE;
        int primary = nightMode ? DARK_TEXT : TEXT;
        int muted = nightMode ? DARK_MUTED : MUTED;
        int accent = nightMode ? DARK_ACCENT : BLUE;
        Object marker = view.getTag();
        int tag = marker instanceof Integer ? (Integer) marker : 0;
        if (tag == SHEET_TAG_SURFACE) view.setBackground(roundRect(surface, 20));
        else if (tag == SHEET_TAG_PLAIN_SURFACE) {
            // Scroll/list surfaces are separate views; repainting only the rounded panel leaves
            // the old theme visible in the gaps after an in-place mode switch.
            view.setBackgroundColor(surface);
            view.setForeground(null);
            view.setStateListAnimator(null);
            view.setBackgroundTintList(null);
        }
        else if (tag == SHEET_TAG_HANDLE)
            view.setBackground(sheetHandleDrawable());
        else if (tag == SHEET_TAG_ROW) {
            // Rows must be repainted as well as their labels. A platform foreground or animator
            // can otherwise keep the light-theme drawable alive after a live dark-mode switch.
            view.setBackgroundColor(surface);
            view.setForeground(null);
            view.setStateListAnimator(null);
            view.setBackgroundTintList(null);
        }
        if (view instanceof BrowserIconView) ((BrowserIconView) view).setTintColor(tag == SHEET_TAG_ACCENT ? accent : primary);
        if (view instanceof TextView) {
            if (tag == SHEET_TAG_PRIMARY) ((TextView) view).setTextColor(primary);
            else if (tag == SHEET_TAG_MUTED) ((TextView) view).setTextColor(muted);
            else if (tag == SHEET_TAG_ACCENT) ((TextView) view).setTextColor(accent);
        }
        if (view instanceof Switch) {
            Switch toggle = (Switch) view;
            int[][] states = new int[][] { new int[] { android.R.attr.state_checked }, new int[] {} };
            toggle.setThumbTintList(new ColorStateList(states, new int[] {
                    accent, nightMode ? 0xffbdc1c6 : 0xff757575
            }));
            toggle.setTrackTintList(new ColorStateList(states, new int[] {
                    0x761a73e8, nightMode ? 0xff505459 : 0xffbdc1c6
            }));
        }
        if (view instanceof ViewGroup) {
            ViewGroup group = (ViewGroup) view;
            for (int i = 0; i < group.getChildCount(); i++) themeSheetTree(group.getChildAt(i));
        }
    }

    private void tintIconTree(View view, int color) {
        if (view instanceof BrowserIconView) ((BrowserIconView) view).setTintColor(color);
        if (view instanceof ViewGroup) {
            ViewGroup group = (ViewGroup) view;
            for (int i = 0; i < group.getChildCount(); i++) tintIconTree(group.getChildAt(i), color);
        }
    }

    private void applyDarkMode(WebView target) {
        if (target == null) return;
        applyDarkMode(target, target.getSettings());
    }

    private void applyDarkMode(WebView target, WebSettings settings) {
        boolean enabled = darkModeEnabled(target);
        target.setBackgroundColor(enabled ? DARK_WEB : WHITE);
        if (WebViewFeature.isFeatureSupported(WebViewFeature.ALGORITHMIC_DARKENING)) {
            try {
                WebSettingsCompat.setAlgorithmicDarkeningAllowed(settings, enabled);
            } catch (RuntimeException ignored) {
            }
        }
        // Android 10-12 WebView builds commonly expose the support-library feature flag but
        // still implement darkening through the platform Force Dark API. Explicitly clear the
        // flag on every transition too; otherwise a site-level light override can remain dark.
        if (Build.VERSION.SDK_INT >= 29) {
            try {
                settings.setForceDark(enabled ? WebSettings.FORCE_DARK_ON : WebSettings.FORCE_DARK_OFF);
            } catch (RuntimeException ignored) {
            }
        }
        target.postInvalidateOnAnimation();
    }

    private boolean darkModeEnabled(WebView target) {
        String host = pageHostFor(target);
        SiteSettingsStore.SiteSettings site = siteSettingsStore == null
                ? new SiteSettingsStore.SiteSettings() : siteSettingsStore.forHost(host);
        int dark = site.get(SiteSettingsStore.DARK);
        boolean enabled = dark == SiteSettingsStore.ALLOW || (dark == SiteSettingsStore.INHERIT && nightMode);
        return enabled && !isInternalBrowserUrl(target == null ? null : target.getUrl());
    }

    private boolean isMediaCompatibilityHost(String host) {
        if (host == null) return false;
        String value = host.toLowerCase(Locale.US);
        return value.equals("youtube.com") || value.endsWith(".youtube.com") || value.equals("youtu.be") ||
                value.equals("youtube-nocookie.com") || value.endsWith(".youtube-nocookie.com");
    }

    private boolean isNetworkPage(String url) {
        return url != null && !isReservedInternalHost(url) &&
                (url.regionMatches(true, 0, "https://", 0, 8) ||
                        url.regionMatches(true, 0, "http://", 0, 7));
    }

    private boolean validSearchTemplate(String value) {
        return SearchEngineStore.validTemplate(value);
    }

    private static boolean sameSecureOrigin(String origin, String pageUrl) {
        try {
            URL expected = NetworkSecurity.parseHttpsUrl(origin);
            URL current = NetworkSecurity.parseHttpsUrl(pageUrl);
            return NetworkSecurity.sameOrigin(expected, current);
        } catch (Exception ignored) { return false; }
    }

    private boolean shouldUpgradeHttp(String url) {
        if (!httpsOnly || url == null || !url.regionMatches(true, 0, "http://", 0, 7)) return false;
        String host = hostOf(url);
        SiteSettingsStore.SiteSettings site = siteSettingsStore == null ? null : siteSettingsStore.forHost(host);
        if (site != null && site.compatibilityMode()) return false;
        return host.length() > 0 && !host.endsWith(".onion") && !NetworkSecurity.isObviouslyLocalHost(host);
    }

    private void confirmExternalNavigation(final String url) {
        String scheme;
        try { scheme = Uri.parse(url).getScheme(); } catch (Exception e) { scheme = "Application externe"; }
        new AlertDialog.Builder(this).setTitle("Ouvrir une application externe ?")
                .setMessage("La page demande d'ouvrir « " + (scheme == null ? "Inconnu" : scheme) + " ». Continuez uniquement si vous faites confiance à ce site.")
                .setPositiveButton("Continuer", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) { startExternalNavigation(url); }
                }).setNegativeButton("Annuler", null).show();
    }

    private void startExternalNavigation(String url) {
        try {
            Intent external;
            if (url.regionMatches(true, 0, "intent:", 0, 7)) {
                Intent parsed = Intent.parseUri(url, Intent.URI_INTENT_SCHEME);
                if (parsed.getData() == null) throw new IllegalArgumentException("Adresse externe invalide");
                external = new Intent(Intent.ACTION_VIEW, parsed.getData());
            } else external = new Intent(Intent.ACTION_VIEW, Uri.parse(url));
            external.addCategory(Intent.CATEGORY_BROWSABLE);
            external.setComponent(null);
            external.setPackage(null);
            external.setSelector(null);
            int unsafeGrants = Intent.FLAG_GRANT_READ_URI_PERMISSION | Intent.FLAG_GRANT_WRITE_URI_PERMISSION |
                    Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION | Intent.FLAG_GRANT_PREFIX_URI_PERMISSION;
            external.setFlags(external.getFlags() & ~unsafeGrants);
            external.setClipData(null);
            startActivity(external);
        } catch (Exception e) { toast("Impossible d'ouvrir ce lien"); }
    }

    private void handleWebPermissionRequest(final WebView source, final PermissionRequest request) {
        if (pendingPermissionRequest != null && pendingPermissionRequest != request) clearPendingWebPermission(true);
        if (request == null || source == null || source != webView || request.getOrigin() == null ||
                !sameSecureOrigin(request.getOrigin().toString(), source.getUrl())) {
            if (request != null) request.deny();
            return;
        }
        if (isQrScannerUrl(source.getUrl()) && qrScannerViews.contains(source)) {
            boolean wantsCamera = false;
            for (String resource : request.getResources()) {
                if (PermissionRequest.RESOURCE_VIDEO_CAPTURE.equals(resource)) wantsCamera = true;
            }
            if (!wantsCamera) { request.deny(); return; }
            ArrayList<String> webResources = new ArrayList<String>();
            webResources.add(PermissionRequest.RESOURCE_VIDEO_CAPTURE);
            ArrayList<String> androidPermissions = new ArrayList<String>();
            androidPermissions.add(Manifest.permission.CAMERA);
            grantWebPermission(source, request.getOrigin().toString(), request,
                    webResources, androidPermissions);
            return;
        }
        final ArrayList<String> webResources = new ArrayList<String>();
        final ArrayList<String> androidPermissions = new ArrayList<String>();
        StringBuilder names = new StringBuilder();
        boolean autoGrant = true;
        String originHost = request.getOrigin().getHost();
        if (originHost == null || originHost.length() == 0) { request.deny(); return; }
        final SiteSettingsStore.SiteSettings site = siteSettingsStore == null
                ? new SiteSettingsStore.SiteSettings() : siteSettingsStore.forHost(originHost);
        for (String resource : request.getResources()) {
            if (PermissionRequest.RESOURCE_VIDEO_CAPTURE.equals(resource)) {
                int camera = site.get(SiteSettingsStore.CAMERA);
                if (camera == SiteSettingsStore.BLOCK) continue;
                if (camera != SiteSettingsStore.ALLOW) autoGrant = false;
                webResources.add(resource);
                if (!androidPermissions.contains(Manifest.permission.CAMERA)) androidPermissions.add(Manifest.permission.CAMERA);
                if (names.length() > 0) names.append("、");
                names.append("Caméra");
            } else if (PermissionRequest.RESOURCE_AUDIO_CAPTURE.equals(resource)) {
                int microphone = site.get(SiteSettingsStore.MICROPHONE);
                if (microphone == SiteSettingsStore.BLOCK) continue;
                if (microphone != SiteSettingsStore.ALLOW) autoGrant = false;
                webResources.add(resource);
                if (!androidPermissions.contains(Manifest.permission.RECORD_AUDIO)) androidPermissions.add(Manifest.permission.RECORD_AUDIO);
                if (names.length() > 0) names.append("、");
                names.append("Microphone");
            }
        }
        if (webResources.size() == 0) { request.deny(); return; }
        final String expectedOrigin = request.getOrigin().toString();
        if (autoGrant) {
            grantWebPermission(source, expectedOrigin, request, webResources, androidPermissions);
            return;
        }
        DenyDialog deny = new DenyDialog(request, null);
        new AlertDialog.Builder(this).setTitle("Autoriser le site à utiliser" + names + "？")
                .setMessage((originHost == null ? "Site actuel" : originHost) + "\n\nN'autorisez que les sites que vous utilisez et auxquels vous faites confiance. Cette autorisation expire à la fermeture de la page.")
                .setPositiveButton("Autoriser cette fois uniquement", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        grantWebPermission(source, expectedOrigin, request, webResources, androidPermissions);
                    }
                }).setNegativeButton("Bloquer", deny).setOnCancelListener(deny).show();
    }

    private void grantWebPermission(WebView source, String origin, PermissionRequest request,
                                    List<String> webResources, List<String> androidPermissions) {
        if (origin == null || source != webView || !sameSecureOrigin(origin, source.getUrl())) { request.deny(); return; }
        ArrayList<String> missing = new ArrayList<String>();
        for (String permission : androidPermissions) if (checkSelfPermission(permission) != PackageManager.PERMISSION_GRANTED) missing.add(permission);
        if (missing.size() == 0) request.grant(webResources.toArray(new String[webResources.size()]));
        else {
            if (pendingPermissionRequest != null && pendingPermissionRequest != request) clearPendingWebPermission(true);
            pendingPermissionRequest = request;
            pendingPermissionView = source;
            pendingPermissionOrigin = origin;
            pendingWebPermissionResources = webResources.toArray(new String[webResources.size()]);
            requestPermissions(missing.toArray(new String[missing.size()]), WEB_PERMISSION_REQUEST);
        }
    }

    private void clearPendingWebPermission(boolean deny) {
        PermissionRequest pending = pendingPermissionRequest;
        pendingPermissionRequest = null;
        pendingWebPermissionResources = null;
        pendingPermissionView = null;
        pendingPermissionOrigin = null;
        if (deny && pending != null) pending.deny();
    }

    private void handleGeolocationRequest(final WebView source, final String origin, final GeolocationPermissions.Callback callback) {
        if (callback == null) return;
        if (pendingGeolocationCallback != null && pendingGeolocationCallback != callback) {
            pendingGeolocationCallback.invoke(pendingGeolocationOrigin, false, false);
            pendingGeolocationCallback = null;
            pendingGeolocationOrigin = null;
            pendingGeolocationView = null;
        }
        final String host = hostOf(origin);
        if (source == null || source != webView || !sameSecureOrigin(origin, source.getUrl())) {
            callback.invoke(origin, false, false);
            return;
        }
        SiteSettingsStore.SiteSettings site = siteSettingsStore == null
                ? new SiteSettingsStore.SiteSettings() : siteSettingsStore.forHost(host);
        int location = site.get(SiteSettingsStore.LOCATION);
        if (location == SiteSettingsStore.BLOCK) { callback.invoke(origin, false, false); return; }
        if (location == SiteSettingsStore.ALLOW) {
            grantGeolocation(source, host, origin, callback);
            return;
        }
        DenyDialog deny = new DenyDialog(callback, origin);
        new AlertDialog.Builder(this).setTitle("Autoriser ce site à accéder à votre position ?")
                .setMessage((host.length() == 0 ? "Site actuel" : host) + "\n\nMedian ne conserve pas cette autorisation ; le site peut néanmoins enregistrer la position que vous avez transmise.")
                .setPositiveButton("Autoriser cette fois uniquement", new DialogInterface.OnClickListener() {
                    @Override public void onClick(DialogInterface dialog, int which) {
                        grantGeolocation(source, host, origin, callback);
                    }
                }).setNegativeButton("Bloquer", deny).setOnCancelListener(deny).show();
    }

    private void grantGeolocation(WebView source, String host, String origin, GeolocationPermissions.Callback callback) {
        if (source != webView || !sameSecureOrigin(origin, source.getUrl())) { callback.invoke(origin, false, false); return; }
        if (checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED ||
                checkSelfPermission(Manifest.permission.ACCESS_COARSE_LOCATION) == PackageManager.PERMISSION_GRANTED) {
            callback.invoke(origin, true, false);
        } else {
            pendingGeolocationCallback = callback;
            pendingGeolocationOrigin = origin;
            pendingGeolocationView = source;
            requestPermissions(new String[] { Manifest.permission.ACCESS_COARSE_LOCATION, Manifest.permission.ACCESS_FINE_LOCATION },
                    GEOLOCATION_PERMISSION_REQUEST);
        }
    }

    @Override public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        boolean granted = grantResults.length > 0;
        for (int result : grantResults) if (result != PackageManager.PERMISSION_GRANTED) granted = false;
        if (requestCode == WEB_PERMISSION_REQUEST && pendingPermissionRequest != null) {
            if (granted && pendingWebPermissionResources != null && pendingPermissionView == webView &&
                    pendingPermissionOrigin != null && sameSecureOrigin(pendingPermissionOrigin, webView.getUrl()))
                pendingPermissionRequest.grant(pendingWebPermissionResources);
            else pendingPermissionRequest.deny();
            clearPendingWebPermission(false);
        } else if (requestCode == GEOLOCATION_PERMISSION_REQUEST && pendingGeolocationCallback != null) {
            boolean locationGranted = checkSelfPermission(Manifest.permission.ACCESS_COARSE_LOCATION) == PackageManager.PERMISSION_GRANTED ||
                    checkSelfPermission(Manifest.permission.ACCESS_FINE_LOCATION) == PackageManager.PERMISSION_GRANTED;
            pendingGeolocationCallback.invoke(pendingGeolocationOrigin,
                    locationGranted && pendingGeolocationView == webView &&
                            sameSecureOrigin(pendingGeolocationOrigin, webView.getUrl()), false);
            pendingGeolocationCallback = null;
            pendingGeolocationOrigin = null;
            pendingGeolocationView = null;
        }
    }

    private void updateChrome() {
        requestChromeUpdate();
    }

    private void requestChromeUpdate() {
        if (chromeUpdatePending || webView == null) return;
        chromeUpdatePending = true;
        Runnable update = new Runnable() {
            @Override public void run() {
                chromeUpdatePending = false;
                performChromeUpdate();
            }
        };
        rootFrame.postOnAnimation(update);
    }

    private void performChromeUpdate() {
        if (webView == null) return;
        updateImmersivePageLayout();
        updateAddressBar();
        boolean canBack = webView.canGoBack();
        boolean canForward = webView.canGoForward();
        EdgeNavigationController.updateSystemGestureExclusion(webView, edgeNavigationEnabled,
                canBack, canForward);
        if (renderedBackEnabled == null || renderedBackEnabled.booleanValue() != canBack) {
            renderedBackEnabled = Boolean.valueOf(canBack);
            backButton.setEnabled(canBack);
            backButton.setAlpha(canBack ? 1f : .32f);
        }
        if (renderedForwardEnabled == null || renderedForwardEnabled.booleanValue() != canForward) {
            renderedForwardEnabled = Boolean.valueOf(canForward);
            forwardButton.setEnabled(canForward);
            forwardButton.setAlpha(canForward ? 1f : .32f);
        }
        int tabCount = tabs.size();
        if (renderedTabCount == null || renderedTabCount.intValue() != tabCount) {
            renderedTabCount = Integer.valueOf(tabCount);
            tabButton.setCount(tabCount);
        }
        boolean shieldActive = isAdBlockActiveForHost(currentPageHost);
        if (renderedShieldActive == null || renderedShieldActive.booleanValue() != shieldActive) {
            renderedShieldActive = Boolean.valueOf(shieldActive);
            shieldButton.setActive(shieldActive);
        }
    }

    private void updateAddressBar() {
        if (addressBar == null || addressBar.hasFocus()) return;
        String url = currentPageUrl;
        String display = "";
        if (isQrScannerUrl(url)) {
            display = "Scanner un QR code";
        } else if (url != null && !isHomeUrl(url) && !"about:blank".equals(url)) {
            String host = currentPageHost;
            if (host != null && host.length() > 0) {
                Uri uri = currentUri();
                String scheme = uri == null ? "" : uri.getScheme();
                display = (scheme == null || scheme.length() == 0 ? "" : scheme.toLowerCase(Locale.US) + "://") + host;
            } else {
                display = url;
            }
        }
        if (!display.equals(renderedAddress) || !display.contentEquals(addressBar.getText())) {
            renderedAddress = display;
            addressBar.setText(display);
        }
    }

    private void scheduleProgressUpdate(int progress) {
        pendingProgress = progress;
        if (progressUpdatePending || webView == null) return;
        progressUpdatePending = true;
        Runnable update = new Runnable() {
            @Override public void run() {
                progressUpdatePending = false;
                int value = pendingProgress;
                if (value >= 100) {
                    // A navigation can begin while the previous 100% fade is still running.
                    // Cancel that end action before starting the new terminal fade.
                    cancelViewAnimationIfRunning(progressBar);
                    if (renderedProgress != 100) Motion.animateProgress(progressBar, renderedProgress, 100, reduceMotion());
                    renderedProgress = 100;
                    if (progressBar.getVisibility() != View.GONE) {
                        cancelViewAnimationIfRunning(progressBar);
                        progressBar.animate().alpha(0f).setDuration(reduceMotion() ? 70L : 130L).withEndAction(new Runnable() {
                            @Override public void run() { progressBar.setVisibility(View.GONE); progressBar.setAlpha(1f); }
                        }).start();
                    }
                    return;
                }
                if (renderedProgress >= 0 && renderedProgress < 100 && Math.abs(value - renderedProgress) < progressStep()) return;
                int previous = renderedProgress;
                renderedProgress = value;
                if (immersiveGestureActive) {
                    cancelViewAnimationIfRunning(progressBar);
                    syncChromeProgress(immersiveGestureOffset);
                    Motion.animateProgress(progressBar, previous, value, reduceMotion());
                    return;
                }
                if (chromeHiddenByScroll || isInPictureInPictureMode()) {
                    cancelViewAnimationIfRunning(progressBar);
                    progressBar.setVisibility(View.GONE);
                    return;
                }
                // Retire the old completion callback before exposing progress for a new load.
                if (previous == 100) cancelViewAnimationIfRunning(progressBar);
                progressBar.setAlpha(1f);
                if (progressBar.getVisibility() != View.VISIBLE) {
                    progressBar.setAlpha(0f);
                    progressBar.setVisibility(View.VISIBLE);
                    progressBar.animate().alpha(1f).setDuration(100L).start();
                }
                Motion.animateProgress(progressBar, previous, value, reduceMotion());
            }
        };
        rootFrame.postOnAnimation(update);
    }

    private Uri currentUri() {
        try {
            String url = currentPageUrl;
            return url == null ? null : Uri.parse(url);
        } catch (RuntimeException e) {
            return null;
        }
    }

    private String currentHost() {
        return currentPageHost == null ? "" : currentPageHost;
    }

    private boolean isCurrentPageCallback(WebView source, long sequence) {
        return !activityDestroyed && source != null && source == webView && sequence == navigationSequence;
    }

    private String hostOf(String url) {
        try {
            if (url == null) return "";
            Uri uri = Uri.parse(url);
            String host = uri.getHost();
            if ("content".equalsIgnoreCase(uri.getScheme()) && OfflineContentProvider.AUTHORITY.equals(uri.getAuthority())) return "";
            return host == null || "median.invalid".equalsIgnoreCase(host) ? "" : host.toLowerCase(Locale.US);
        } catch (RuntimeException e) {
            return "";
        }
    }

    private boolean isHomeUrl(String url) {
        return UrlCleaner.isInternalPage(url, "median.invalid");
    }

    private boolean isInternalBrowserUrl(String url) {
        if (!isReservedInternalHost(url)) return false;
        try { return "https".equalsIgnoreCase(Uri.parse(url).getScheme()); }
        catch (RuntimeException ignored) { return false; }
    }

    private boolean isReservedInternalHost(String url) {
        if (url == null) return false;
        try { return "median.invalid".equalsIgnoreCase(Uri.parse(url).getHost()); }
        catch (RuntimeException ignored) { return false; }
    }

    private static String navigationDocumentUrl(String url) {
        if (url == null) return "";
        int fragment = url.indexOf('#');
        return fragment < 0 ? url : url.substring(0, fragment);
    }

    private boolean isQrScannerUrl(String url) {
        if (!UrlCleaner.isHttpsOrigin(url, "median.invalid")) return false;
        try {
            Uri uri = Uri.parse(url);
            return "/scan".equals(uri.getPath()) && uri.getQuery() == null;
        } catch (RuntimeException ignored) {
            return false;
        }
    }

    private GradientDrawable roundRect(int color, int radiusDp) {
        GradientDrawable drawable = new GradientDrawable();
        drawable.setColor(color);
        drawable.setCornerRadius(dp(radiusDp));
        return drawable;
    }

    private android.graphics.drawable.Drawable sheetHandleDrawable() {
        return new android.graphics.drawable.InsetDrawable(
                roundRect(nightMode ? 0x505f6368 : 0x365f6368, 2), 0, dp(14), 0, dp(14));
    }

    private void hideKeyboard() {
        InputMethodManager manager = (InputMethodManager) getSystemService(Context.INPUT_METHOD_SERVICE);
        if (manager != null) manager.hideSoftInputFromWindow(addressBar.getWindowToken(), 0);
    }

    private void finishFileChooser(Uri[] result) {
        ValueCallback<Uri[]> callback = fileChooserCallback;
        fileChooserCallback = null;
        fileChooserView = null;
        fileChooserDocumentUrl = "";
        if (callback != null) try { callback.onReceiveValue(result); } catch (RuntimeException ignored) {}
    }

    private int dp(int value) {
        return Math.round(value * getResources().getDisplayMetrics().density);
    }

    private void toast(String message) {
        Toast.makeText(this, message, Toast.LENGTH_SHORT).show();
    }

    private String safeMessage(Exception e) {
        return ErrorText.message(e, 180);
    }

    private void writeBackup(final Uri uri) {
        if (uri == null || scriptExecutor == null || scriptExecutor.isShutdown()) return;
        String prepared;
        try {
            JSONObject root = new JSONObject(dataStore.exportJson());
            root.put("bookmarkFolders", new JSONObject(bookmarkFolders.exportJson()));
            prepared = root.toString();
        } catch (Exception error) { toast("Impossible de préparer la sauvegarde des signets"); return; }
        final String json = prepared;
        executeTask(scriptExecutor, new Runnable() {
            @Override public void run() {
                OutputStream output = null;
                Exception failure = null;
                try {
                    output = getContentResolver().openOutputStream(uri, "w");
                    if (output == null) throw new IllegalStateException("Impossible d'ouvrir le fichier cible");
                    output.write(json.getBytes("UTF-8"));
                    output.flush();
                } catch (Exception e) { failure = e; }
                finally { NetworkSecurity.closeQuietly(output); }
                final Exception error = failure;
                uiHandler.post(new Runnable() { @Override public void run() { toast(error == null ? "Sauvegarde des signets exportée" : "Échec de l'exportation : " + safeMessage(error)); } });
            }
        });
    }

    private void readBackup(final Uri uri) {
        if (uri == null || scriptExecutor == null || scriptExecutor.isShutdown()) return;
        toast("Vérification de la sauvegarde…");
        executeTask(scriptExecutor, new Runnable() {
            @Override public void run() {
                InputStream input = null;
                int imported = 0;
                Exception failure = null;
                try {
                    input = getContentResolver().openInputStream(uri);
                    if (input == null) throw new IllegalStateException("Impossible d'ouvrir le fichier de sauvegarde");
                    ByteArrayOutputStream output = new ByteArrayOutputStream(32 * 1024);
                    byte[] buffer = new byte[8192];
                    int read;
                    while ((read = input.read(buffer)) != -1) {
                        if (output.size() + read > 4 * 1024 * 1024) throw new IllegalArgumentException("Sauvegarde supérieure à 4 Mo");
                        output.write(buffer, 0, read);
                    }
                    String raw = output.toString("UTF-8");
                    String trimmed = raw.trim();
                    if (trimmed.startsWith("<")) {
                        imported = importBookmarkHtml(raw);
                    } else {
                        imported = dataStore.importJson(raw);
                        JSONObject root = new JSONObject(raw);
                        JSONObject folders = root.optJSONObject("bookmarkFolders");
                        if (folders != null) bookmarkFolders.mergeJson(folders.toString());
                    }
                } catch (Exception e) { failure = e; }
                finally { NetworkSecurity.closeQuietly(input); }
                final int count = imported;
                final Exception error = failure;
                uiHandler.post(new Runnable() { @Override public void run() {
                    if (error == null) refreshHomeAfterLibraryChange();
                    toast(error == null ? "Importé(s) : " + count + " nouveaux signets" : "Échec de l'importation : " + safeMessage(error));
                } });
            }
        });
    }

    private int importBookmarkHtml(String raw) {
        List<BookmarkHtmlParser.Item> items = BookmarkHtmlParser.parse(raw);
        if (items.isEmpty()) throw new IllegalArgumentException("Aucun signet web importable dans le HTML");
        HashMap<String, String> folderIds = new HashMap<String, String>();
        int imported = 0;
        for (BookmarkHtmlParser.Item item : items) {
            BrowserDataStore.Bookmark added = dataStore.addBookmark(item.title, item.url);
            if (added == null) continue;
            imported++;
            String parent = BookmarkFolderStore.ROOT;
            StringBuilder path = new StringBuilder();
            for (String name : item.folders) {
                if (path.length() > 0) path.append('/');
                path.append(name);
                String key = path.toString();
                String folderId = folderIds.get(key);
                if (folderId == null) {
                    BookmarkFolderStore.Folder found = null;
                    for (BookmarkFolderStore.Folder candidate : bookmarkFolders.foldersIn(parent))
                        if (candidate.name.equals(name)) { found = candidate; break; }
                    if (found == null) found = bookmarkFolders.create(name, parent, false);
                    if (found == null) break;
                    folderId = found.id;
                    folderIds.put(key, folderId);
                }
                parent = folderId;
            }
            bookmarkFolders.setParentForUrl(added.url, parent);
        }
        if (imported == 0) throw new IllegalArgumentException("Aucun nouveau signet web à importer");
        return imported;
    }

    private void showFullBackupPassword(final Uri uri, final boolean exporting) {
        if (uri == null) return;
        final EditText password = new EditText(this);
        password.setHint(exporting ? "Définir la phrase secrète de sauvegarde (10 caractères minimum)" : "Saisir la phrase secrète de sauvegarde");
        password.setSingleLine(true);
        password.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_PASSWORD);
        final EditText confirmation = new EditText(this);
        confirmation.setHint("Saisissez à nouveau la phrase secrète de sauvegarde");
        confirmation.setSingleLine(true);
        confirmation.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_PASSWORD);
        LinearLayout fields = new LinearLayout(this);
        fields.setOrientation(LinearLayout.VERTICAL);
        fields.setPadding(dp(18), 0, dp(18), 0);
        fields.addView(password);
        if (exporting) fields.addView(confirmation);
        final AlertDialog dialog = new AlertDialog.Builder(this)
                .setTitle(exporting ? "Sauvegarde complète chiffrée" : "Déchiffrer la sauvegarde complète")
                .setMessage(exporting ? "Inclut signets, historique, onglets, paramètres, scripts, abonnements de filtres et mots de passe. Les pages hors ligne et les fichiers téléchargés ne sont pas inclus. En cas d'oubli de la phrase secrète, la sauvegarde sera irrécupérable." :
                        "La restauration remplacera les données de navigation, scripts, paramètres et mots de passe actuels. La sauvegarde ne sera pas appliquée si la vérification AES-GCM échoue.")
                .setView(fields)
                .setPositiveButton(exporting ? "Export chiffré" : "Restaurer en déchiffrant", null)
                .setNegativeButton("Annuler", null).create();
        secureDialog(dialog);
        dialog.setOnShowListener(new DialogInterface.OnShowListener() {
            @Override public void onShow(DialogInterface ignored) {
                dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(new View.OnClickListener() {
                    @Override public void onClick(View ignored) {
                        String first = password.getText().toString();
                        if (first.length() < 10 || first.length() > 256) {
                            password.setError("La phrase secrète doit contenir 10 à 256 caractères");
                            return;
                        }
                        if (exporting && !first.equals(confirmation.getText().toString())) {
                            confirmation.setError("Les deux saisies de la phrase secrète ne correspondent pas");
                            return;
                        }
                        dialog.dismiss();
                        if (exporting) createFullBackup(uri, first.toCharArray());
                        else restoreFullBackup(uri, first.toCharArray());
                    }
                });
            }
        });
        dialog.show();
    }

    private void createFullBackup(final Uri uri, final char[] password) {
        toast("Chiffrement de la sauvegarde complète…");
        services.passwords().exportJson(new PasswordVault.Callback<String>() {
            @Override public void onComplete(final String vaultJson, Exception error) {
                if (error != null) {
                    java.util.Arrays.fill(password, '\0');
                    toast("Échec de la lecture du coffre : " + safeMessage(error));
                    return;
                }
                executeTask(scriptExecutor, new Runnable() {
                    @Override public void run() {
                        OutputStream output = null;
                        Exception failure = null;
                        try {
                            JSONObject root = new JSONObject();
                            root.put("format", "median-portable-state");
                            root.put("version", 1);
                            root.put("createdAt", System.currentTimeMillis());
                            root.put("browser", dataStore.exportPortable());
                            root.put("bookmarkFolders", new JSONObject(bookmarkFolders.exportJson()));
                            root.put("sites", new JSONObject(siteSettingsStore.exportJson()));
                            root.put("scripts", new JSONArray(scriptStore.exportJson()));
                            root.put("filters", new JSONArray(services.filters().exportJson()));
                            root.put("customFilters", prefs.getString("custom_filter_rules", ""));
                            root.put("settings", settingsSnapshot());
                            root.put("passwords", new JSONArray(vaultJson == null ? "[]" : vaultJson));
                            byte[] encoded = PortableBackupCodec.encrypt(root, password);
                            output = getContentResolver().openOutputStream(uri, "w");
                            if (output == null) throw new IllegalStateException("Impossible d'ouvrir le fichier cible");
                            output.write(encoded);
                            output.flush();
                        } catch (Exception e) { failure = e; }
                        finally {
                            java.util.Arrays.fill(password, '\0');
                            if (output != null) try { output.close(); } catch (Exception ignored) {}
                        }
                        final Exception result = failure;
                        uiHandler.post(new Runnable() {
                            @Override public void run() { toast(result == null ? "Sauvegarde complète chiffrée exportée" : "Échec de la sauvegarde complète : " + safeMessage(result)); }
                        });
                    }
                });
            }
        });
    }

    private JSONObject settingsSnapshot() throws Exception {
        JSONObject value = new JSONObject();
        value.put("adBlock", adBlockEnabled);
        value.put("desktop", desktopMode);
        value.put("night", nightMode);
        value.put("httpsOnly", httpsOnly);
        value.put("restoreTabs", restoreTabs);
        value.put("homeOpenMode", homeOpenMode());
        value.put("homeCustomUrl", normalizeConfiguredHomeUrl(prefs.getString("home_custom_url", "")));
        value.put("thirdPartyCookies", acceptThirdPartyCookies);
        value.put("searchEngine", searchEngine);
        List<SearchEngineStore.Engine> customEngines = searchEngines.customEngines();
        value.put("customSearch", customEngines.size() == 0 ? "" : customEngines.get(0).template);
        value.put("customSearchEngines", searchEngines.exportJson());
        value.put("performanceMode", performanceMode);
        // Retain the legacy field for older backup readers; the unsafe direct-network mode was
        // removed and is never restored.
        value.put("networkDirect", false);
        value.put("autoPip", autoPictureInPicture);
        value.put("cleanTracking", cleanTrackingParameters);
        value.put("passwordAutofill", passwordAutofillEnabled);
        value.put("passwordSavePrompts", passwordSavePromptsEnabled);
        value.put("siteExceptions", new JSONArray(siteExceptions));
        HomePageConfig home = homePageConfig();
        value.put("homeTitle", home.title);
        value.put("homeSubtitle", home.subtitle);
        value.put("homeLogoStyle", home.logoStyle);
        value.put("homeLogoCode", home.logoCode);
        value.put("homeLogoMode", home.logoMode);
        value.put("homeLogoLetterSpacing", home.logoLetterSpacing);
        value.put("homeLogoGradientAngle", home.logoGradientAngle);
        value.put("homeLogoFontSize", home.logoFontSize);
        value.put("homeLogoFontWeight", home.logoFontWeight);
        value.put("homeLogoImageWidth", home.logoImageWidth);
        value.put("homeLogoImageHeight", home.logoImageHeight);
        value.put("homeLogoImageRadius", home.logoImageRadius);
        value.put("homeAccent", home.accent);
        value.put("homeWallpaperDim", home.wallpaperDim);
        value.put("homeWallpaperBlur", home.wallpaperBlur);
        value.put("homeWallpaperFit", home.wallpaperFit);
        value.put("homeSearchStyle", home.searchStyle);
        value.put("homeLayout", home.layout);
        value.put("homeTileShape", home.tileShape);
        value.put("homeShortcutColumns", home.shortcutColumns);
        value.put("homeShowSearch", home.showSearch);
        value.put("homeShowEngines", home.showEngines);
        value.put("homeShowShortcuts", home.showShortcuts);
        value.put("homeShowCorner", home.showCornerBrand);
        value.put("homeShowClock", home.showClock);
        value.put("homeCustomCss", home.customCss);
        value.put("homeCustomHtmlEnabled", home.customHtmlEnabled);
        value.put("homeCustomHtml", CustomHomeHtml.clean(prefs.getString("home_custom_html", "")));
        value.put("homeCustomHtmlVersion", home.customHtmlVersion);
        return value;
    }

    private void restoreFullBackup(final Uri uri, final char[] password) {
        if (scriptExecutor == null || scriptExecutor.isShutdown()) return;
        toast("Vérification et restauration de la sauvegarde complète…");
        executeTask(scriptExecutor, new Runnable() {
            @Override public void run() {
                InputStream input = null;
                Exception failure = null;
                String passwords = null;
                int bookmarks = 0;
                try {
                    input = getContentResolver().openInputStream(uri);
                    if (input == null) throw new IllegalStateException("Impossible d'ouvrir le fichier de sauvegarde");
                    byte[] encoded = NetworkSecurity.readBounded(input, 20 * 1024 * 1024, "Sauvegarde supérieure à 20 Mo");
                    input = null;
                    JSONObject root = PortableBackupCodec.decrypt(encoded, password);
                    if (!"median-portable-state".equals(root.optString("format")) || root.optInt("version", 0) != 1)
                        throw new IllegalArgumentException("Version du contenu de sauvegarde non prise en charge");
                    JSONObject browser = root.getJSONObject("browser");
                    JSONObject sites = root.getJSONObject("sites");
                    JSONArray scripts = root.getJSONArray("scripts");
                    JSONArray filters = root.getJSONArray("filters");
                    JSONArray vault = root.getJSONArray("passwords");
                    JSONObject settings = root.getJSONObject("settings");
                    if (scripts.length() > 128 || filters.length() > 32 || vault.length() > 500)
                        throw new IllegalArgumentException("Les entrées de sauvegarde dépassent la limite de sécurité");
                    bookmarks = dataStore.importPortable(browser);
                    JSONObject folderState = root.optJSONObject("bookmarkFolders");
                    if (folderState != null) bookmarkFolders.importJson(folderState.toString());
                    siteSettingsStore.importJson(sites.toString());
                    scriptStore.importJson(scripts.toString());
                    services.filters().importJson(filters.toString());
                    String custom = root.optString("customFilters", "");
                    if (custom.length() > 256 * 1024) throw new IllegalArgumentException("Règles personnalisées au-delà de la limite");
                    prefs.edit().putString("custom_filter_rules", custom).commit();
                    applySettingsSnapshot(settings);
                    passwords = vault.toString();
                } catch (Exception e) { failure = e; }
                finally {
                    java.util.Arrays.fill(password, '\0');
                    if (input != null) try { input.close(); } catch (Exception ignored) {}
                }
                final Exception error = failure;
                final String vaultJson = passwords;
                final int bookmarkCount = bookmarks;
                uiHandler.post(new Runnable() {
                    @Override public void run() {
                        if (error != null) { toast("Échec de la restauration : " + safeMessage(error)); return; }
                        services.passwords().importJson(vaultJson, new PasswordVault.Callback<Integer>() {
                            @Override public void onComplete(Integer count, Exception vaultError) {
                                if (vaultError != null) { toast("Les autres données ont été restaurées, mais la restauration des mots de passe a échoué : " + safeMessage(vaultError)); return; }
                                finishFullRestore(bookmarkCount, count == null ? 0 : count.intValue());
                            }
                        });
                    }
                });
            }
        });
    }

    private void applySettingsSnapshot(JSONObject value) throws Exception {
        String restoredMode = value.optString("performanceMode", MODE_STANDARD);
        if (!MODE_PERFORMANCE.equals(restoredMode) && !MODE_POWER_SAVE.equals(restoredMode)) restoredMode = MODE_STANDARD;
        String restoredSearch = value.optString("searchEngine", "google");
        String restoredCustomSearch = value.optString("customSearch", "").trim();
        if (!validSearchTemplate(restoredCustomSearch)) restoredCustomSearch = "";
        JSONArray restoredCustomEngines = value.optJSONArray("customSearchEngines");
        boolean legacyRestoreTabs = value.optBoolean("restoreTabs", false);
        String restoredOpenMode = HomeOpenPolicy.normalize(value.optString("homeOpenMode", ""), legacyRestoreTabs);
        String restoredHomeUrl = normalizeConfiguredHomeUrl(value.optString("homeCustomUrl", ""));
        if (HomeOpenPolicy.OPEN_CUSTOM_URL.equals(restoredOpenMode) && restoredHomeUrl.length() == 0)
            restoredOpenMode = HomeOpenPolicy.OPEN_HOME;
        String restoredCustomHtml = CustomHomeHtml.clean(value.optString("homeCustomHtml", ""));
        boolean restoredCustomHtmlEnabled = value.optBoolean("homeCustomHtmlEnabled", false) &&
                CustomHomeHtml.valid(restoredCustomHtml);
        long restoredCustomHtmlVersion = Math.max(0L, value.optLong("homeCustomHtmlVersion", 0L));
        String restoredCustomCss = CustomHomeCss.clean(value.optString("homeCustomCss", ""));
        if (!CustomHomeCss.valid(restoredCustomCss)) restoredCustomCss = "";
        String restoredLogoMode = value.optString("homeLogoMode", "text");
        if (!"text".equals(restoredLogoMode) && !"image".equals(restoredLogoMode) && !"none".equals(restoredLogoMode))
            restoredLogoMode = "text";
        boolean restoredKeepLast = HomeOpenPolicy.KEEP_LAST.equals(restoredOpenMode);
        HashSet<String> exceptions = new HashSet<String>();
        JSONArray array = value.optJSONArray("siteExceptions");
        if (array != null) for (int i = 0; i < array.length() && exceptions.size() < 500; i++) {
            String host = array.optString(i, "").trim().toLowerCase(Locale.US);
            if (host.matches("[a-z0-9._-]{1,253}")) exceptions.add(host);
        }
        HomePageConfig restoredHome = HomePageConfig.createPersonalized(
                value.optString("homeTitle", HomePageConfig.DEFAULT_TITLE),
                value.optString("homeSubtitle", ""), value.optString("homeLogoStyle", "median"),
                value.optString("homeLogoCode", ""), value.optInt("homeLogoLetterSpacing", 0),
                value.optInt("homeLogoGradientAngle", 90), value.optString("homeAccent", "blue"),
                value.optInt("homeWallpaperDim", 28), value.optInt("homeWallpaperBlur", 0),
                value.optString("homeWallpaperFit", "cover"), value.optString("homeSearchStyle", "solid"),
                value.optString("homeLayout", "center"), value.optString("homeTileShape", "rounded"),
                value.optInt("homeShortcutColumns", 4), value.optBoolean("homeShowSearch", true),
                value.optBoolean("homeShowEngines", true), value.optBoolean("homeShowShortcuts", true),
                value.optBoolean("homeShowCorner", true), value.optBoolean("homeShowClock", false),
                restoredCustomHtmlEnabled, false, false, restoredCustomHtmlVersion, 0L, 0L,
                restoredLogoMode, value.optInt("homeLogoFontSize", 47),
                value.optInt("homeLogoFontWeight", 720), value.optInt("homeLogoImageWidth", 132),
                value.optInt("homeLogoImageHeight", 96), value.optInt("homeLogoImageRadius", 0),
                restoredCustomCss);
        SharedPreferences.Editor editor = prefs.edit()
                .putBoolean("adblock", value.optBoolean("adBlock", true))
                .putBoolean("desktop", value.optBoolean("desktop", false))
                .putBoolean("night_mode", value.optBoolean("night", false))
                .putBoolean("https_only", value.optBoolean("httpsOnly", true))
                .putBoolean("restore_tabs", restoredKeepLast)
                .putString("home_open_mode", restoredOpenMode)
                .putString("home_custom_url", restoredHomeUrl)
                .putBoolean("accept_third_party_cookies", value.optBoolean("thirdPartyCookies", false))
                .putString("search_engine", restoredSearch)
                .putString("custom_search_template", restoredCustomSearch)
                .putString("performance_mode", restoredMode)
                .putBoolean("auto_picture_in_picture", value.optBoolean("autoPip", false))
                .putBoolean("clean_tracking_parameters", value.optBoolean("cleanTracking", true))
                .putBoolean("password_autofill", value.optBoolean("passwordAutofill", true))
                .putBoolean("password_save_prompts", value.optBoolean("passwordSavePrompts", true))
                .putStringSet("site_exceptions", exceptions)
                .putString("home_title", restoredHome.title)
                .putString("home_subtitle", restoredHome.subtitle)
                .putString("home_logo_style", restoredHome.logoStyle)
                .putString("home_logo_code", restoredHome.logoCode)
                .putString("home_logo_mode", restoredHome.logoMode)
                .putInt("home_logo_letter_spacing", restoredHome.logoLetterSpacing)
                .putInt("home_logo_gradient_angle", restoredHome.logoGradientAngle)
                .putInt("home_logo_font_size", restoredHome.logoFontSize)
                .putInt("home_logo_font_weight", restoredHome.logoFontWeight)
                .putInt("home_logo_image_width", restoredHome.logoImageWidth)
                .putInt("home_logo_image_height", restoredHome.logoImageHeight)
                .putInt("home_logo_image_radius", restoredHome.logoImageRadius)
                .putString("home_accent", restoredHome.accent)
                .putInt("home_wallpaper_dim", restoredHome.wallpaperDim)
                .putInt("home_wallpaper_blur", restoredHome.wallpaperBlur)
                .putString("home_wallpaper_fit", restoredHome.wallpaperFit)
                .putString("home_search_style", restoredHome.searchStyle)
                .putString("home_layout", restoredHome.layout)
                .putString("home_tile_shape", restoredHome.tileShape)
                .putInt("home_shortcut_columns", restoredHome.shortcutColumns)
                .putBoolean("home_show_search", restoredHome.showSearch)
                .putBoolean("home_show_engines", restoredHome.showEngines)
                .putBoolean("home_show_shortcuts", restoredHome.showShortcuts)
                .putBoolean("home_show_corner", restoredHome.showCornerBrand)
                .putBoolean("home_show_clock", restoredHome.showClock)
                .putString("home_custom_css", restoredHome.customCss)
                .putString("home_custom_html", restoredCustomHtml)
                .putBoolean("home_custom_html_enabled", restoredCustomHtmlEnabled)
                .putLong("home_custom_html_version", restoredCustomHtmlVersion);
        if (!editor.commit()) throw new IllegalStateException("Impossible d'enregistrer les paramètres de restauration");
        searchEngines.replaceFromJson(restoredCustomEngines, restoredCustomSearch);
        if ("custom".equals(restoredSearch)) {
            List<SearchEngineStore.Engine> migrated = searchEngines.customEngines();
            restoredSearch = migrated.size() == 0 ? "google" : migrated.get(0).id;
        }
        if (!searchEngines.contains(restoredSearch)) restoredSearch = "google";
        prefs.edit().putString("search_engine", restoredSearch).apply();
        adBlockEnabled = value.optBoolean("adBlock", true);
        desktopMode = value.optBoolean("desktop", false);
        nightMode = value.optBoolean("night", false);
        httpsOnly = value.optBoolean("httpsOnly", true);
        restoreTabs = restoredKeepLast;
        acceptThirdPartyCookies = value.optBoolean("thirdPartyCookies", false);
        searchEngine = restoredSearch;
        performanceMode = restoredMode;
        autoPictureInPicture = value.optBoolean("autoPip", false);
        cleanTrackingParameters = value.optBoolean("cleanTracking", true);
        passwordAutofillEnabled = value.optBoolean("passwordAutofill", true);
        passwordSavePromptsEnabled = value.optBoolean("passwordSavePrompts", true);
        siteExceptions = exceptions;
    }

    private void finishFullRestore(int bookmarks, int passwords) {
        appliedSiteSettings.clear();
        refreshUserScriptRegistrations(false);
        rebuildAdBlockRulesAsync(false);
        applyDarkMode();
        applyPerformanceMode();
        applyRestoredTabs();
        updateFilterSubscriptions(false);
        toast("Sauvegarde complète restaurée : " + bookmarks + " signets, " + passwords + " entrées de mot de passe");
    }

    private void applyRestoredTabs() {
        webContainer.removeAllViews();
        ArrayList<WebView> oldViews = new ArrayList<WebView>();
        for (BrowserTab tab : tabs) if (tab.liveView != null && !oldViews.contains(tab.liveView)) oldViews.add(tab.liveView);
        for (WebView old : oldViews) destroyWebView(old);
        scriptTabValues.clear();
        tabs.clear();
        closedTabs.clear();
        if (restoreTabs) {
            List<BrowserDataStore.SessionTab> restored = dataStore.restoreSession();
            for (BrowserDataStore.SessionTab item : restored) {
                BrowserTab tab = new BrowserTab();
                tab.title = item.title;
                tab.url = item.url;
                tab.pinned = item.pinned;
                tabs.add(tab);
            }
        }
        if (tabs.size() == 0) {
            BrowserTab home = new BrowserTab();
            home.url = configuredHomeUrl();
            tabs.add(home);
        }
        currentTabIndex = restoreTabs ? Math.min(dataStore.restoredSessionIndex(), tabs.size() - 1) : 0;
        BrowserTab active = tabs.get(currentTabIndex);
        webView = createConfiguredWebView();
        bindWebViewToTab(active, webView);
        applyPerformanceMode(webView);
        active.lastActiveAt = SystemClock.uptimeMillis();
        webContainer.addView(webView, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        currentPageUrl = active.url;
        currentPageHost = hostOf(active.url);
        pageHosts.put(webView, currentPageHost);
        if (isHomeUrl(active.url)) showHome();
        else if (isQrScannerUrl(active.url)) showQrScannerPage();
        else loadNetworkUrl(webView, active.url);
        renderedTabCount = null;
        requestChromeUpdate();
    }

    private void persistSession() {
        if (dataStore == null) return;
        saveCurrentTab();
        ArrayList<BrowserDataStore.SessionTab> snapshot = new ArrayList<BrowserDataStore.SessionTab>();
        for (BrowserTab tab : tabs) snapshot.add(new BrowserDataStore.SessionTab(tab.title, tab.url, tab.pinned));
        dataStore.saveSession(snapshot, currentTabIndex);
    }

    @Override
    protected void onNewIntent(Intent intent) {
        super.onNewIntent(intent);
        setIntent(intent);
        if (isExternalHttpIntent(intent)) loadInput(intent.getData().toString());
        else if (intent != null && Intent.ACTION_VIEW.equals(intent.getAction())) toast("Adresse externe non HTTP(S) refusée");
        else if (intent != null && Intent.ACTION_MAIN.equals(intent.getAction()) &&
                intent.hasCategory(Intent.CATEGORY_LAUNCHER) &&
                !HomeOpenPolicy.KEEP_LAST.equals(homeOpenMode())) {
            // A fresh tap on the launcher follows the selected startup destination even
            // when Android reuses this task. Returning from another app keeps the page.
            dismissOverlayForNavigation();
            startupSessionPending = false;
            if (startupReady) openConfiguredHome();
            else {
                startupSavedState = null;
                startupExternalUrl = "";
                pendingStartupInput = null;
            }
        }
    }

    private static boolean isExternalHttpIntent(Intent intent) {
        if (intent == null || !Intent.ACTION_VIEW.equals(intent.getAction()) || intent.getData() == null) return false;
        try {
            NetworkSecurity.parseHttpUrl(intent.getData().toString());
            return true;
        } catch (Exception ignored) { return false; }
    }

    @Override
    protected void onSaveInstanceState(Bundle outState) {
        super.onSaveInstanceState(outState);
        saveCurrentTab();
        Bundle webViewState = captureWebViewState(webView);
        Bundle tabMetadata = captureTabMetadata();
        Bundle browserState = new Bundle();
        if (webViewState != null) browserState.putBundle(STATE_WEBVIEW, webViewState);
        if (tabMetadata != null) browserState.putBundle(STATE_TABS, tabMetadata);
        // Keep the combined browser contribution within the original history-only budget.
        // Tab identity/selection and a reloadable URL take precedence over optional history.
        if (!isBoundedTabState(browserState)) webViewState = null;
        if (webViewState != null) outState.putBundle(STATE_WEBVIEW, webViewState);
        if (tabMetadata != null) outState.putBundle(STATE_TABS, tabMetadata);
        persistSession();
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        super.onActivityResult(requestCode, resultCode, data);
        if (requestCode == DOWNLOAD_DIRECTORY_REQUEST) {
            DownloadDirectory.handlePickerResult(this, resultCode, data, new Runnable() {
                @Override public void run() { showDownloadSettings(); }
            });
        } else if (requestCode == QR_SCAN_REQUEST) {
            String scanned = "";
            if (resultCode == RESULT_OK && data != null) {
                scanned = data.getStringExtra("SCAN_RESULT");
                if (scanned == null || scanned.trim().length() == 0) scanned = data.getDataString();
                if (scanned == null || scanned.trim().length() == 0) scanned = data.getStringExtra("result");
            }
            String value = scanned == null ? "" : scanned.trim();
            if (value.length() > 16 * 1024) {
                toast("Contenu du QR code anormalement long");
                if (webView != null && isQrScannerUrl(webView.getUrl())) showQrScannerPage();
            } else if (value.length() > 0) showQrResult(value);
            else if (webView != null && isQrScannerUrl(webView.getUrl())) showQrScannerPage();
        } else if (requestCode == FILE_CHOOSER_REQUEST && fileChooserCallback != null) {
            Uri[] result = null;
            try { result = WebChromeClient.FileChooserParams.parseResult(resultCode, data); }
            catch (RuntimeException ignored) {}
            WebView chooserView = fileChooserView;
            String current = chooserView == null ? null : chooserView.getUrl();
            if (chooserView == null || chooserView != webView || activityDestroyed ||
                    !fileChooserDocumentUrl.equals(navigationDocumentUrl(current))) result = null;
            finishFileChooser(result);
        } else if (requestCode == BACKUP_EXPORT_REQUEST && resultCode == RESULT_OK && data != null) {
            writeBackup(data.getData());
        } else if (requestCode == BACKUP_IMPORT_REQUEST && resultCode == RESULT_OK && data != null) {
            readBackup(data.getData());
        } else if (requestCode == FULL_BACKUP_EXPORT_REQUEST && resultCode == RESULT_OK && data != null) {
            final Uri uri = data.getData();
            withVaultUnlock(new Runnable() { @Override public void run() { showFullBackupPassword(uri, true); } });
        } else if (requestCode == FULL_BACKUP_IMPORT_REQUEST && resultCode == RESULT_OK && data != null) {
            final Uri uri = data.getData();
            withVaultUnlock(new Runnable() { @Override public void run() { showFullBackupPassword(uri, false); } });
        } else if (requestCode == HOME_WALLPAPER_REQUEST) {
            homeCustomization().onImagePickerResult(HomeImageStore.Kind.WALLPAPER, resultCode, data);
        } else if (requestCode == HOME_LOGO_REQUEST) {
            homeCustomization().onImagePickerResult(HomeImageStore.Kind.LOGO, resultCode, data);
        } else if (requestCode == VAULT_UNLOCK_REQUEST) {
            Runnable action = pendingVaultAction;
            Runnable cancelAction = pendingVaultCancelAction;
            pendingVaultAction = null;
            pendingVaultCancelAction = null;
            if (resultCode == RESULT_OK) {
                uiHandler.removeCallbacks(vaultLock);
                vaultUnlockedUntil = SystemClock.elapsedRealtime() + VAULT_UNLOCK_WINDOW_MS;
                uiHandler.postDelayed(vaultLock, VAULT_UNLOCK_WINDOW_MS);
                if (action != null) action.run();
            } else {
                toast("Le coffre reste verrouillé");
                continueSettingsPanel(cancelAction);
            }
        }
    }

    @Override
    public void onBackPressed() {
        handleBrowserBack();
    }

    private void handleBrowserBack() {
        if (overlayDismissInProgress) {
            return;
        } else if (activeOverlay != null) {
            navigateOverlayBack();
        } else if (customView != null) {
            exitFullscreen();
        } else if (webView != null && adPickerSessions.containsKey(webView)) {
            finishAdPickerSession(webView, adPickerSessions.get(webView));
        } else if (webView != null && webView.canGoBack()) {
            goBackWebView(webView);
            scheduleRestoredHomeRepair(webView);
        } else if (tabs.size() > 1) {
            closeCurrentTab();
        } else {
            if (clearDataOnExit) clearDataForExit();
            finishAfterTransition();
        }
    }

    private void trimRuntimeCaches(boolean severe) {
        preparedInjection = null;
        adBlock.trimMemory();
        if (scriptStore != null) scriptStore.trimMemory();
        if (services != null) services.trimMemory();
        // The active WebView owns the rendered document; these Java strings are rebuildable.
        cachedHomeKey = "";
        cachedHomeHtml = "";
        if (severe) scriptTabValues.trimMemory();
    }

    @Override
    protected void onStop() {
        persistSession();
        if (dataStore != null) dataStore.flush();
        if (siteSettingsStore != null) siteSettingsStore.flush();
        if (scriptStore != null) scriptStore.flush();
        if (deferredStartupPending) {
            uiHandler.removeCallbacks(deferredStartup);
            deferredStartupPending = false;
        }
        uiHandler.removeCallbacks(vaultLock);
        vaultLock.run();
        // Preserve hot-tab resume behavior. Android's memory-pressure callbacks below own
        // renderer freezing; merely opening another Activity must not turn a hot tab cold.
        if (services != null) services.trimMemory();
        maybeTrimTransientCache();
        super.onStop();
    }

    @Override
    protected void onPause() {
        immersiveGestureActive = false;
        updatePageMargins();
        boolean pictureInPicture = isInPictureInPictureMode();
        activityResumed = pictureInPicture;
        startupReadiness.set(StartupReadiness.RESUMED, pictureInPicture);
        if (webView != null && !pictureInPicture) {
            webView.onPause();
        }
        super.onPause();
    }

    @Override
    protected void onResume() {
        super.onResume();
        activityResumed = true;
        if (webView != null) {
            webView.onResume();
            resumeQrScannerIfNeeded();
        }
        startupReadiness.set(StartupReadiness.RESUMED, true);
        maybeStartFastStartup();
        maybeCompleteStartup();
        if (pageFinished && isNetworkPage(currentPageUrl)) scheduleDeferredStartupWork();
    }

    @Override
    protected void onUserLeaveHint() {
        if (autoPictureInPicture && webView != null && isNetworkPage(currentPageUrl) &&
                !isInPictureInPictureMode()) enterPagePictureInPicture();
        super.onUserLeaveHint();
    }

    @Override
    public void onPictureInPictureModeChanged(boolean inPictureInPictureMode, android.content.res.Configuration newConfig) {
        super.onPictureInPictureModeChanged(inPictureInPictureMode, newConfig);
        updatePageMargins();
        if (rootFrame != null) rootFrame.requestApplyInsets();
        if (inPictureInPictureMode) {
            if (topBar != null) topBar.setVisibility(View.INVISIBLE);
            if (bottomBar != null) bottomBar.setVisibility(View.INVISIBLE);
            if (progressBar != null) progressBar.setVisibility(View.GONE);
        } else if (chromeHiddenByScroll) {
            if (topBar != null) topBar.setVisibility(View.INVISIBLE);
            if (bottomBar != null) bottomBar.setVisibility(View.INVISIBLE);
            setImmersiveSystemBars(true);
        } else {
            showBrowserChrome(false);
        }
        activityResumed = inPictureInPictureMode || hasWindowFocus();
        if (webView != null) {
            if (inPictureInPictureMode) webView.onResume();
            else requestChromeUpdate();
        }
    }

    @Override
    public void onTrimMemory(int level) {
        super.onTrimMemory(level);
        boolean runningPressure = level >= android.content.ComponentCallbacks2.TRIM_MEMORY_RUNNING_LOW &&
                level <= android.content.ComponentCallbacks2.TRIM_MEMORY_RUNNING_CRITICAL;
        if (runningPressure || level >= android.content.ComponentCallbacks2.TRIM_MEMORY_UI_HIDDEN) {
            boolean severe = level == android.content.ComponentCallbacks2.TRIM_MEMORY_RUNNING_CRITICAL ||
                    level >= android.content.ComponentCallbacks2.TRIM_MEMORY_COMPLETE;
            trimRuntimeCaches(severe);
        }

        boolean releaseTabs;
        if (MODE_POWER_SAVE.equals(performanceMode)) {
            releaseTabs = runningPressure || level >= android.content.ComponentCallbacks2.TRIM_MEMORY_UI_HIDDEN;
        } else if (MODE_PERFORMANCE.equals(performanceMode)) {
            releaseTabs = level == android.content.ComponentCallbacks2.TRIM_MEMORY_RUNNING_CRITICAL ||
                    level >= android.content.ComponentCallbacks2.TRIM_MEMORY_COMPLETE;
        } else {
            releaseTabs = level == android.content.ComponentCallbacks2.TRIM_MEMORY_RUNNING_CRITICAL ||
                    level >= android.content.ComponentCallbacks2.TRIM_MEMORY_MODERATE;
        }
        if (releaseTabs) {
            releaseInactiveTabStates();
            if (level == android.content.ComponentCallbacks2.TRIM_MEMORY_RUNNING_CRITICAL ||
                    level >= android.content.ComponentCallbacks2.TRIM_MEMORY_COMPLETE) clearColdTabBundles();
        }
    }

    @Override
    public void onLowMemory() {
        trimRuntimeCaches(true);
        releaseInactiveTabStates();
        clearColdTabBundles();
        super.onLowMemory();
    }

    private void releaseInactiveTabStates() {
        ArrayList<BrowserTab> inactive = new ArrayList<BrowserTab>();
        for (int i = 0; i < tabs.size(); i++) if (i != currentTabIndex && tabs.get(i).liveView != null) inactive.add(tabs.get(i));
        for (BrowserTab tab : inactive) freezeTab(tab);
    }

    private void clearColdTabBundles() {
        for (int i = 0; i < tabs.size(); i++) if (i != currentTabIndex) tabs.get(i).state = null;
    }

    @Override
    protected void onDestroy() {
        activityResumed = false;
        activityDestroyed = true;
        if (adBlockRuleLoader != null) adBlockRuleLoader.close();
        if (startupDataLoader != null) startupDataLoader.close();
        if (connectionHints != null) connectionHints.close();
        if (userScriptNetwork != null) userScriptNetwork.close();
        if (homeCustomizationController != null) homeCustomizationController.close();
        pendingVaultAction = null;
        pendingVaultCancelAction = null;
        uiHandler.removeCallbacks(vaultLock);
        vaultLock.run();
        unregisterPredictiveBack();
        if (!(clearDataOnExit && exitDataCleared)) persistSession();
        clearPendingWebPermission(true);
        if (pendingGeolocationCallback != null) pendingGeolocationCallback.invoke(pendingGeolocationOrigin, false, false);
        pendingGeolocationCallback = null;
        pendingGeolocationOrigin = null;
        pendingGeolocationView = null;
        finishFileChooser(null);
        dismissOverlay();
        uiHandler.removeCallbacksAndMessages(null);
        if (startupExecutor != null) startupExecutor.shutdownNow();
        // Provider startup is process-wide. Do not interrupt its queued work on Activity teardown;
        // its terminal callback retires this executor even if this Activity has been destroyed.
        if (navigationExecutor != null) navigationExecutor.shutdownNow();
        if (scriptExecutor != null) scriptExecutor.shutdownNow();
        if (scriptNetworkExecutor != null) scriptNetworkExecutor.shutdownNow();
        faviconFetchQueued.clear();
        scriptTabValues.clear();
        if (services != null) services.close();
        if (dataStore != null) dataStore.close();
        if (siteSettingsStore != null) siteSettingsStore.close();
        if (scriptStore != null) scriptStore.close();
        if (customView != null) exitFullscreen();
        ArrayList<WebView> views = new ArrayList<WebView>();
        for (BrowserTab tab : tabs) if (tab.liveView != null && !views.contains(tab.liveView)) views.add(tab.liveView);
        for (WebView view : views) destroyWebView(view);
        for (BrowserTab tab : tabs) tab.liveView = null;
        webView = null;
        super.onDestroy();
    }
}
