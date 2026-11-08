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
    private static final long FILTER_SUBSCRIPTION_IDLE_DELAY_MS = 3200L;
    private static final long INITIAL_NAVIGATION_ACK_MS = 1400L;
    private static final int MAX_WEBVIEW_STATE_BYTES = 262144;
    private static final int MAX_TAB_METADATA_BYTES = 262144;
    private static final int MAX_SAVED_TAB_URL_CHARS = 16384;
    private static final int MAX_SAVED_TAB_TITLE_CHARS = 256;
    private static final int SCRIPT_BRIDGE_MAX_MESSAGE_CHARS = 256 * 1024;
    private static final int SCRIPT_ASSET_MAX_BYTES = 8 * 1024 * 1024;
    private static final long SCRIPT_ASSET_TOTAL_MAX_BYTES = 32L * 1024L * 1024L;
    private static final byte[] EMPTY_RESPONSE = new byte[0];
    private static final String MODE_PERFORMANCE = "performance";
    private static final String MODE_STANDARD = "standard";
    private static final String MODE_POWER_SAVE = "power_save";

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
            "Mises à jour, versions et retours :\n" + GITHUB_URL +
            "\n\nCanal de test officiel et annonces :\n" + TELEGRAM_URL;

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
        prefs = getSharedPreferences(PREFS, MODE_PRIVATE);
        nightMode = prefs.getBoolean("night_mode", false);
        setTheme(nightMode ? R.style.AppThemeDark : R.style.AppTheme);
        super.onCreate(state);
        beginWebViewStartup();
        Window window = getWindow();
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
        rebuildAdBlockRulesAsync(false);

        BrowserTab first = new BrowserTab();
        tabs.add(first);
        beginStartupLoad(state, getIntent());
        buildUi();
        registerPredictiveBack();
    }

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
                if (startupStatus != null) startupStatus.setText("Échec du moteur web, veuillez redémarrer Median");
            }
        });
    }

    private void finishWebViewStartupExecutor() {
        if (webViewStartupExecutor != null) webViewStartupExecutor.shutdown();
        webViewStartupExecutor = null;
    }

    private void initializeInitialWebView() {
        if (activityDestroyed || isFinishing() || webView != null || webContainer == null) return;

        webView = createConfiguredWebView();
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
        webContainer.addView(initialView, 0, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        initialView.setAlpha(1f);

        applyPerformanceMode(webView);
        BrowserTab first = tabs.get(0);
        bindWebViewToTab(first, webView);
        first.lastActiveAt = SystemClock.uptimeMillis();
        if (activityResumed) webView.onResume();
        startupReadiness.set(StartupReadiness.VIEW, true);
        updateChrome();
        maybeStartFastStartup();
        maybeCompleteStartup();
    }

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
        if (webView.isAttachedToWindow()) launch.run();
        else postAfterUiTransition(launch);
    }

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
            startupSessionPending = false;
            loadInput(directInput);
        } else if (restoreWebViewState(webView, webViewState)) {
            startupSessionPending = false;
            active.url = webView.getUrl() == null ? HOME_URL : webView.getUrl();
            if (isHomeUrl(active.url)) {
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
        String actualUrl = webView.getUrl();
        if (!pageFinished && isNetworkPage(currentPageUrl)) prepareNavigationConnections(currentPageUrl);
        if (isNetworkPage(currentPageUrl) && isNetworkPage(actualUrl)) {
            applySiteSettings(webView, currentPageHost);
        } else if (!userHasNavigated && isHomeUrl(currentPageUrl) && isHomeUrl(actualUrl)) {
            showHome();
        }
    }

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
                    @Override public void run() { if (!activityDestroyed) toast("Tâches en arrière-plan occupées, réessayez"); }
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
            toast("Restauration des données locales en cours...");
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
        addressBar.setHint("Rechercher ou saisir une URL");
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
        startupStatus.setText("Préparation du moteur web...");
        startupStatus.setTextColor(nightMode ? DARK_MUTED : MUTED);
        startupStatus.setTextSize(12f);
        startupStatus.setGravity(Gravity.CENTER);
        startupStatus.setPadding(0, dp(8), 0, 0);
        ((LinearLayout) startupSurface).addView(startupStatus, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT));
        webContainer.addView(startupSurface, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

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
        forwardButton = iconButton(BrowserIconView.FORWARD, "Avancer");
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
        if (immersiveGestureActive && immersivePageLayout && !keyboardVisible &&
                customView == null && !isInPictureInPictureMode()) return;
        boolean fullscreen = isInPictureInPictureMode() || (immersivePageLayout && chromeHiddenByScroll);
        int top = fullscreen ? 0 : dp(62) + (immersivePageLayout ? systemInsetTop : 0);
        int bottom = fullscreen ? 0 : dp(62) +
                (immersivePageLayout && !keyboardVisible ? systemInsetBottom : 0);
        FrameLayout.LayoutParams params = (FrameLayout.LayoutParams) webContainer.getLayoutParams();
        if (params.topMargin == top && params.bottomMargin == bottom) return;
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
        button.setBackground(null);
        return button;
    }

    private WebView createConfiguredWebView() {
        WebView view = new WebView(this);
        styleWebView(view);
        configureWebView(view);
        pageHosts.put(view, "");
        return view;
    }

    private void observeImmersiveTouch(WebView source, MotionEvent event) {
        if (source != webView || activityDestroyed || event == null) return;
        int action = event.getActionMasked();
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
                deltaY = Math.signum(dy) * (Math.abs(dy) - slop);
            }
            if (immersiveGestureVertical) {
                float travel = Math.max(dp(62), Math.max(topBar.getHeight(), bottomBar.getHeight()));
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

    private static void cancelViewAnimationIfRunning(View view) {
        if (view == null) return;
        ViewPropertyAnimator animator = view.animate();
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

    private void installSheetDrag(final View target, final View panel) {
        if (target == null || panel == null) return;
        final float touchSlop = Math.max(dp(8), ViewConfiguration.get(target.getContext()).getScaledTouchSlop());
        target.setOnTouchListener(new View.OnTouchListener() {
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
                        dragging = dy > touchSlop && dy > Math.abs(dx) * 1.12f;
                        if (!dragging) cancelled = true;
                    }
                    if (dragging) {
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
        handle.setContentDescription("Glisser vers le bas pour fermer");
        installSheetDrag(handle, panel);

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.CENTER_VERTICAL);
        header.setPadding(backAction == null ? dp(10) : 0, 0, dp(2), dp(2));
        if (backAction != null) {
            BrowserIconView back = iconButton(BrowserIconView.BACK, "Retour");
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

    private void installPreparedDocumentStartUserScripts(WebView target) {
        if (target == null || !startupDataReady || startupScriptPayloadsApplied) return;
        startupScriptPayloadsApplied = true;
        String token = startupScriptToken;
        List<UserScriptStore.DocumentStartPayload> payloads = startupScriptPayloads;
        startupScriptToken = "";
        startupScriptPayloads = Collections.emptyList();
        installDocumentStartUserScripts(target, token, payloads);
    }

    private void installDocumentStartUserScripts(WebView target) {
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
                            toast("Permissions des scripts mises à jour, rechargement...");
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
        return generation == null ? 0L : generation.longValue();
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
                        @Override
                        public void run() {
                            if (!unresponsiveWebViews.remove(view) || isFinishing()) return;
                            if (!terminateRenderer.terminate()) {
                                try { view.stopLoading(); } catch (RuntimeException ignored) {}
                            }
                            toast("Page non réactive, redémarrage du moteur...");
                        }
                    }, 4500L);
                }

                @Override
                public void onResponsive(WebView view) {
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
            }

            @Override
            public void onPageStarted(WebView view, String url, android.graphics.Bitmap favicon) {
                super.onPageStarted(view, url, favicon);
                advanceScriptDocumentGeneration(view);
                NavigationGestureGuard gestureGuard = navigationGestureGuards.get(view);
                String initiatingDocument = protectedNavigationSourceDocument(view);
                long startedAt = SystemClock.uptimeMillis();
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
                    recordStartupNavigation("Premier vol validé", url);
                if (view != webView) return;
                pageCommitted = true;
                injectPreparedStart(navigationSequence);
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                super.onPageFinished(view, url);
                retireMainFrameNavigation(view, url);
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
                    recordStartupNavigation("Premier vol terminé", settledUrl);
                updateTabForView(view, settledUrl, view.getTitle());
                if (settledUrl != null) {
                    String finishedHost = hostOf(settledUrl);
                    pageHosts.put(view, finishedHost);
                    adBlockActiveByView.put(view, Boolean.valueOf(isAdBlockActiveForHost(finishedHost)));
                    if (isNetworkPage(settledUrl) && isAdBlockActiveForHost(finishedHost)) {
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
                if (url != null) rememberNavigationSourceDocument(view, url);
                updateTabForView(view, url, view.getTitle());
                if (url != null) pageHosts.put(view, hostOf(url));
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
                    toast("Échec de la validation du certificat, chargement arrêté");
                    String failed = error == null ? currentPageUrl : error.getUrl();
                    String current = view.getUrl();
                    if (failed != null && current != null &&
                            sameCredentialDocument(failed, current) &&
                            hostOf(failed).equalsIgnoreCase(currentPageHost)) {
                        maybeOfferCompatibilityMode(failed, "Échec du certificat ou du chargement HTTPS principal");
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
                        maybeOfferCompatibilityMode(failed, "Échec du chargement principal (" + error.getErrorCode() + ")");
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
                                    toast("La page a changé, authentification annulée");
                                    return;
                                }
                                handler.proceed(username.getText().toString(), password.getText().toString());
                            }
                        }).setNegativeButton("Annuler", deny).setOnCancelListener(deny).create();
                secureDialog(dialog);
                dialog.show();
            }
        });
        
        // ... (تكملة إعدادات WebChromeClient وبقية الكود في السطر التالي)
        target.setWebChromeClient(new WebChromeClient() {
            @Override
            public void onProgressChanged(WebView view, int newProgress) {
                if (view == webView) {
                    InitialNavigationGuard guard = initialNavigationGuards.get(view);
                    if (newProgress > 10 && guard != null && !guard.isAcknowledged()) {
                        String url = view.getUrl();
                        if (guard.acknowledge(url) && startupNavigationAt != 0L)
                            recordStartupNavigation("Premier vol répondu", url);
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
                NavigationGestureGuard gestureGuard = navigationGestureGuards.get(view);
                String sourceDocument = navigationSourceDocument(view);
                if (popups != SiteSettingsStore.ALLOW && isUserGesture &&
                        navigationProtectionActive(navigationSourceHost(view, sourceDocument)) &&
                        gestureGuard != null && gestureGuard.hasRecentDrag(sourceDocument, SystemClock.uptimeMillis())) return false;
                if (tabs.size() >= MAX_TABS) {
                    if (isUserGesture) toast("Limite de " + MAX_TABS + " onglets atteinte");
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

// ... (تكملة بقية الدوال في السطر التالي)
// ... يتبع الجزء الثاني في الرسالة القادمة ...