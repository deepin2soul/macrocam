package com.example.macrocam

import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.content.ClipData
import android.content.ClipboardManager
import android.content.ContentValues
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.content.SharedPreferences
import android.content.pm.ActivityInfo
import android.content.pm.PackageManager
import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Paint
import android.graphics.ImageFormat
import android.graphics.Matrix
import android.graphics.Rect
import android.graphics.YuvImage
import android.graphics.RectF
import android.graphics.SurfaceTexture
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.hardware.display.DisplayManager
import android.hardware.camera2.*
import android.hardware.camera2.params.OutputConfiguration
import android.hardware.camera2.params.SessionConfiguration
import android.hardware.camera2.params.StreamConfigurationMap
import android.media.CamcorderProfile
import android.media.AudioAttributes
import android.media.AudioFormat
import android.media.AudioTrack
import android.media.ExifInterface
import android.media.MediaCodec
import android.media.MediaCodecInfo
import android.media.MediaCodecList
import android.media.MediaFormat
import android.media.MediaMuxer
import android.media.MediaMetadataRetriever
import android.media.Image
import android.media.ImageReader
import android.media.MediaRecorder
import android.os.BatteryManager
import android.os.Build
import android.os.Environment
import android.os.StatFs
import android.os.Bundle
import android.os.Handler
import android.os.HandlerThread
import android.os.Looper
import android.os.SystemClock
import android.os.ParcelFileDescriptor
import android.provider.MediaStore
import android.util.Range
import android.util.Size
import android.view.Surface
import android.net.Uri
import android.view.HapticFeedbackConstants
import android.view.MotionEvent
import android.view.TextureView
import android.view.View
import android.view.WindowInsets
import android.view.WindowInsetsController
import android.view.WindowManager
import android.content.res.ColorStateList
import android.graphics.Color
import android.view.Gravity
import android.view.ViewGroup
import android.widget.Button
import android.widget.FrameLayout
import android.widget.LinearLayout
import android.widget.CheckBox
import android.widget.EditText
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import java.io.BufferedReader
import java.io.ByteArrayOutputStream
import java.io.InputStreamReader
import java.io.OutputStream
import java.net.ServerSocket
import java.net.Socket
import java.net.URLDecoder
import java.util.concurrent.CountDownLatch
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger
import java.io.FileInputStream
import java.io.FileOutputStream
import java.nio.ByteBuffer
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.io.File
import kotlin.math.max
import kotlin.math.min
import kotlin.math.pow

class MainActivity : Activity() {

    private lateinit var prefs: SharedPreferences
    private lateinit var cm: CameraManager
    private lateinit var texture: TextureView
    private lateinit var logView: TextView
    private lateinit var logScroll: ScrollView
    private var cameraId = "3"
    private val camIds = arrayOf("3", "0", "4")
    private lateinit var btnCam: Button
    @Volatile private var opening = false
    private lateinit var sbIso: TickSeekBar
    private lateinit var sbExp: TickSeekBar
    private lateinit var sbFocus: TickSeekBar
    private lateinit var tvIso: TextView
    private lateinit var tvExp: TextView
    private lateinit var tvFocus: TextView
    private lateinit var cbExp: CheckBox
    private lateinit var cbFocus: CheckBox
    private lateinit var cbFlip: CheckBox
    private lateinit var btnRec: Button
    private lateinit var btnAspect: Button
    private lateinit var btnRes: Button
    private lateinit var btnCodec: Button
    private lateinit var sbZoom: TickSeekBar
    private lateinit var tvZoom: TextView
    private lateinit var thread: HandlerThread
    private lateinit var handler: Handler

    private var device: CameraDevice? = null
    private var session: CameraCaptureSession? = null
    private var builder: CaptureRequest.Builder? = null
    private var imageReader: ImageReader? = null

    private var chars: CameraCharacteristics? = null
    private var isoRange: Range<Int>? = null
    private var expRange: Range<Long>? = null
    private var minFocus: Float = 0f
    private var maxZoom: Float = 1f
    private var streamMap: StreamConfigurationMap? = null
    private var aspectMode = 0
    private lateinit var btnServer: Button
    private val logBuf = ArrayList<String>()
    // полный журнал для экспорта (с временем), хранится в памяти до ~100 тыс. символов
    private val fullLog = StringBuilder()
    private val logTimeFmt = SimpleDateFormat("HH:mm:ss.SSS", Locale.US)
    private var serverSocket: ServerSocket? = null
    @Volatile private var serverOn = false
    private var pin = ""
    private val clients = AtomicInteger(0)
    @Volatile private var latestJpeg: ByteArray? = null
    @Volatile private var frameSeq = 0L
    private var streamBmp: Bitmap? = null
    private var loupeBmp: Bitmap? = null
    private lateinit var btnPause: Button
    private lateinit var btnGallery: Button
    private lateinit var btnTorch: Button
    private lateinit var btnSave: Button
    private lateinit var saveOverlay: FrameLayout
    private var paused = false
    private var torchOn = false
    private var torchId: String? = null
    private var torchCb: CameraManager.TorchCallback? = null
    private var saveMode = false
    private var lastTap = 0L
    private var lastMediaUri: Uri? = null
    private var lastMediaMime: String? = null
    private var videoUri: Uri? = null
    private var videoInfo: String? = null
    private var pendingInfo: String? = null
    private var pendingExpSec: Double? = null
    private var pendingIso: Int? = null
    private var pendingDist: Double? = null
    private var pendingTag: String? = null
    private var stackFrameExpNs: Long = 0L
    private var stackTotalNs = 0L          // заданная «долгая выдержка», нс
    private val stackMaxFrameNs = 30_000_000_000L // самый длинный кадр серии: 30 с
    private var stackT0 = 0L
    private var mode = 0 // 0 = фото, 1 = видео
    private lateinit var btnMode: Button
    private lateinit var btnPhoto: Button
    private var persistentSurface: Surface? = null
    private var previewSurface: Surface? = null
    private var previewBuilder: CaptureRequest.Builder? = null
    private var usePersistent = true
    @Volatile private var sessionHasRecorder = false
    private var recordingPersistent = false
    @Volatile private var focusOverride: Float? = null
    @Volatile private var rampActive = false
    @Volatile private var rampToken = 0
    private var boostRange: Range<Int>? = null
    private var maxFrameDuration: Long = Long.MAX_VALUE
    private lateinit var btnStack: Button
    private lateinit var btnNr: Button
    private lateinit var btnEdge: Button
    private var nrMode = -1
    private var edgeMode = -1
    private lateinit var btnBitrate: Button
    private lateinit var btnStab: Button
    private var stabOn = true
    // для растянутого превью после возврата из галереи
    private var lastLandscapeDeg = 90
    private var appliedTransformKey = ""
    private var frameCounter = 0
    // размер вида, с которым запущено превью; камера стартует только после стабилизации размера
    private var startedViewW = 0
    private var startedViewH = 0
    private var reopenPending = false
    private val restartRunnable = Runnable {
        reopenPending = false
        if (!recording && !stacking && !tlRunning && !opening) {
            log("Перезапуск камеры (экран " + texture.width + "x" + texture.height + ")")
            if (device != null) openById(cameraId) else tryAutoOpen()
        }
    }
    private fun scheduleRestart(delayMs: Long) {
        reopenPending = true
        texture.removeCallbacks(restartRunnable)
        texture.postDelayed(restartRunnable, delayMs)
    }
    private var useHevc = true // true = H.265, false = H.264
    // два варианта битрейта (Мбит/с): H.265 экономнее при том же качестве
    private val bitrates: IntArray get() = if (useHevc) intArrayOf(12, 25) else intArrayOf(20, 40)
    private var bitrateIdx = 0
    private val fpsChoices = intArrayOf(24, 30, 60, 120, 240) // какие частоты предлагать в видео
    private var hsActive = false          // сессия сейчас скоростная (constrained high-speed), 120+ к/с
    private var hsDisabled = false        // скоростная сессия не настроилась, дальше не пробуем
    private var hsSizes: Set<String> = emptySet() // размеры, которые камера снимает в скоростном режиме
    private var vFps = 30                              // выбранная частота кадров видео
    private var fpsAvail: List<Int> = emptyList()      // что реально тянут камера, разрешение и кодер
    private lateinit var btnFps: Button
    private var resIdx = 1 // 0 = макс, 1 = норм (1080p)
    private lateinit var sbStack: TickSeekBar
    private lateinit var tvStack: TextView
    private lateinit var cbStackSum: CheckBox
    private lateinit var sbBoost: TickSeekBar
    private lateinit var tvBoost: TextView

    // долгая выдержка (наложение кадров)
    @Volatile private var stacking = false
    @Volatile private var stackCancel = false
    private var stackReader: ImageReader? = null
    private var stackSurface: Surface? = null
    private var stackCount = 0
    private var stackTarget = 0
    private var stackSubmitted = 0
    private var stackLogged = 0
    private var stackLastT = 0L
    private var stackSum = true
    private var stackW = 0
    private var stackH = 0
    private var yAcc: IntArray? = null
    private var uAcc: IntArray? = null
    private var vAcc: IntArray? = null
    private val lin = IntArray(256) { Math.pow(it / 255.0, 2.2).times(65535.0).toInt() }
    private val invLut = IntArray(16384) {
        Math.pow(min(it * 4, 65535) / 65535.0, 1.0 / 2.2).times(255.0).toInt()
    }
    private var videoCandidates: List<Size> = emptyList()
    private lateinit var panel: View
    private lateinit var btnPanel: Button
    private var previewSize = Size(640, 480)
    private var videoSize = Size(1280, 720)
    private var photoSize = Size(1280, 960)

    private var recorder: MediaRecorder? = null
    private var pfd: ParcelFileDescriptor? = null
    @Volatile private var recording = false
    @Volatile private var previewOff = false
    private lateinit var previewCover: View
    @Volatile private var coverPending = false
    private lateinit var btnPreview: Button

    // ---------- таймлапс (режим 2) ----------
    // доступные интервалы между кадрами, секунды
    private val tlIntervals = intArrayOf(1, 2, 3, 4, 5, 6, 8, 10, 15, 20, 30, 45, 60, 90, 120, 180, 300, 600)
    private val tlFps = 30            // частота кадров готового ролика (можно поставить 24)
    private val tlMinBattery = 5      // авто-остановка при заряде не выше, %, если телефон не на зарядке
    private val tlMinFreeMb = 300L    // авто-остановка, если свободного места меньше, МБ
    private lateinit var sbTl: TickSeekBar
    private lateinit var tvTl: TextView
    private lateinit var cbTlJpeg: CheckBox
    private lateinit var cbTlLock: CheckBox
    private lateinit var btnTl: Button
    @Volatile private var tlRunning = false
    @Volatile private var tlLockEngaged = false
    private var tlReader: ImageReader? = null
    private var tlCodec: MediaCodec? = null
    private var tlMuxer: MediaMuxer? = null
    private var tlTrack = -1
    private var tlMuxStarted = false
    private var tlFrames = 0
    private var tlW = 0
    private var tlH = 0
    private var tlIntervalMs = 5000L
    private var tlStartUptime = 0L
    private var tlShotIdx = 0L
    @Volatile private var tlPendingSince = 0L
    private var tlFailStreak = 0
    private var tlSkipped = 0
    private var tlSaveJpeg = false
    private var tlJpegDir = ""
    private var tlRotation = 0
    private var tlInfo = ""
    private var tlJpegExec: ExecutorService? = null
    private val tlJpegPending = AtomicInteger(0)
    private val tlTickToken = Any()

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).toInt()

    private fun mkBtn(label: String): Button {
        val b = Button(this)
        b.text = label
        return b
    }

    private fun mkTv(label: String): TextView {
        val t = TextView(this)
        t.text = label
        t.setTextColor(Color.WHITE)
        return t
    }

    private fun mkCb(label: String, checked: Boolean = false): CheckBox {
        val c = CheckBox(this)
        c.text = label
        c.setTextColor(Color.WHITE)
        c.buttonTintList = ColorStateList.valueOf(Color.WHITE)
        c.isChecked = checked
        return c
    }

    private fun mkSb(maxValue: Int, progressValue: Int): TickSeekBar {
        val sb = TickSeekBar(this)
        sb.max = maxValue
        sb.progress = progressValue
        return sb
    }

    // Весь интерфейс создаётся здесь, в коде, поэтому xml-файл разметки больше не нужен
    private fun buildUi() {
        val match = ViewGroup.LayoutParams.MATCH_PARENT
        val wrap = ViewGroup.LayoutParams.WRAP_CONTENT

        val root = FrameLayout(this)
        root.setBackgroundColor(Color.BLACK)

        texture = TextureView(this)
        root.addView(texture, FrameLayout.LayoutParams(match, match))

        // чёрная заслонка: при включении превью стирает старый кадр, пока не придёт новый
        previewCover = View(this)
        previewCover.setBackgroundColor(Color.BLACK)
        previewCover.visibility = View.GONE
        root.addView(previewCover, FrameLayout.LayoutParams(match, match))

        // колонка кнопок съёмки, теперь справа, всегда на экране
        btnPanel = mkBtn("Панель")
        btnMode = mkBtn("Режим")
        btnPhoto = mkBtn("Фото")
        btnStack = mkBtn("Выдержка")
        btnRec = mkBtn("Видео")
        btnTl = mkBtn("Таймлапс")
        btnTl.visibility = View.GONE
        btnPause = mkBtn("Пауза")
        btnPause.visibility = View.GONE
        btnGallery = mkBtn("Галерея")
        btnPreview = mkBtn("Превью: вкл")
        val actions = LinearLayout(this)
        actions.orientation = LinearLayout.VERTICAL
        actions.addView(btnMode)
        actions.addView(btnRec)
        actions.addView(btnTl)
        actions.addView(btnPause)
        actions.addView(btnPhoto)
        actions.addView(btnStack)
        actions.addView(btnPreview)
        actions.addView(btnPanel)
        actions.addView(btnGallery)
        val actionsLp = FrameLayout.LayoutParams(wrap, wrap, Gravity.END or Gravity.CENTER_VERTICAL)
        actionsLp.rightMargin = dp(8)
        root.addView(actions, actionsLp)

        // панель настроек, теперь слева
        btnServer = mkBtn("Трансляция: выкл")
        btnCam = mkBtn("Камера")
        btnTorch = mkBtn("Фонарик: выкл")
        btnSave = mkBtn("Экономия (чёрный экран)")
        btnAspect = mkBtn("Формат: 4:3")
        btnStab = mkBtn("Стабилизация: вкл")
        cbFlip = mkCb("Перевернуть 180°")
        tvZoom = mkTv("Зум")
        sbZoom = mkSb(1000, 0)
        cbExp = mkCb("Ручные ISO и выдержка")
        tvIso = mkTv("ISO")
        sbIso = mkSb(1000, 200)
        tvExp = mkTv("Выдержка")
        sbExp = mkSb(1000, 500)
        cbFocus = mkCb("Ручной фокус")
        tvFocus = mkTv("Фокус")
        sbFocus = mkSb(1000, 200)
        tvBoost = mkTv("Цифровое усиление")
        tvBoost.visibility = View.GONE
        sbBoost = mkSb(1000, 0)
        sbBoost.visibility = View.GONE
        tvStack = mkTv("Долгая выдержка")
        sbStack = mkSb(118, 28)
        cbStackSum = mkCb("Суммировать (ярче); выкл. = среднее", true)
        btnNr = mkBtn("Шумоподавление: авто")
        btnEdge = mkBtn("Контуры: авто")
        btnBitrate = mkBtn("Битрейт: 20 Мбит/с")
        btnFps = mkBtn("Кадры: 30")
        btnRes = mkBtn("Разрешение: Норм")
        btnCodec = mkBtn("Кодек: H.265")
        tvTl = mkTv("Интервал")
        sbTl = mkSb(tlIntervals.size - 1, 4)
        cbTlLock = mkCb("Блокировать экспозицию и баланс белого")
        cbTlJpeg = mkCb("Сохранять и JPEG-кадры")

        val col = LinearLayout(this)
        col.orientation = LinearLayout.VERTICAL
        col.addView(btnServer)
        col.addView(btnCam)
        col.addView(btnTorch)
        col.addView(btnSave)
        col.addView(btnAspect)
        col.addView(btnRes)
        col.addView(btnCodec)
        col.addView(btnBitrate)
        col.addView(btnFps)
        col.addView(tvTl)
        col.addView(sbTl)
        col.addView(cbTlLock)
        col.addView(cbTlJpeg)
        col.addView(cbFlip)
        col.addView(tvZoom)
        col.addView(sbZoom)
        col.addView(cbExp)
        col.addView(tvIso)
        col.addView(sbIso)
        col.addView(tvExp)
        col.addView(sbExp)
        col.addView(cbFocus)
        col.addView(tvFocus)
        col.addView(sbFocus)
        col.addView(tvBoost)
        col.addView(sbBoost)
        col.addView(tvStack)
        col.addView(sbStack)
        col.addView(btnNr)
        col.addView(btnEdge)

        val panelScroll = ScrollView(this)
        panelScroll.setBackgroundColor(Color.argb(0x99, 0, 0, 0))
        panelScroll.setPadding(dp(8), dp(8), dp(8), dp(8))
        panelScroll.addView(col)
        panel = panelScroll
        root.addView(panelScroll, FrameLayout.LayoutParams(dp(320), match, Gravity.START))

        // лог внизу справа, левее колонки кнопок
        logView = TextView(this)
        logView.setTextColor(Color.WHITE)
        logView.textSize = 11f
        logView.setTextIsSelectable(true) // долгое нажатие: выделить текст, «Выбрать все», «Копировать»
        logScroll = ScrollView(this)
        logScroll.setBackgroundColor(Color.argb(0x66, 0, 0, 0))
        logScroll.addView(logView)
        val logLp = FrameLayout.LayoutParams(dp(380), dp(88), Gravity.BOTTOM or Gravity.END)
        logLp.rightMargin = dp(116)
        root.addView(logScroll, logLp)

        // чёрный экран для экономии батареи (поверх всего)
        saveOverlay = FrameLayout(this)
        saveOverlay.setBackgroundColor(Color.BLACK)
        saveOverlay.visibility = View.GONE
        saveOverlay.isClickable = true
        val hint = TextView(this)
        hint.text = "Экономия: нажмите дважды, чтобы выйти"
        hint.setTextColor(Color.rgb(60, 60, 60))
        hint.textSize = 12f
        saveOverlay.addView(hint, FrameLayout.LayoutParams(wrap, wrap, Gravity.CENTER))
        root.addView(saveOverlay, FrameLayout.LayoutParams(match, match))
        saveOverlay.setOnClickListener {
            val now = System.currentTimeMillis()
            if (now - lastTap < 600) setSaveMode(false) else lastTap = now
        }

        setContentView(root)
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        requestedOrientation = ActivityInfo.SCREEN_ORIENTATION_LANDSCAPE
        if (Build.VERSION.SDK_INT >= 28) {
            val lp = window.attributes
            lp.layoutInDisplayCutoutMode =
                WindowManager.LayoutParams.LAYOUT_IN_DISPLAY_CUTOUT_MODE_SHORT_EDGES
            window.attributes = lp
        }
        buildUi()
        hideSystemUi()

        prefs = getSharedPreferences("macro", MODE_PRIVATE)
        cm = getSystemService(CAMERA_SERVICE) as CameraManager
        thread = HandlerThread("cam").also { it.start() }
        handler = Handler(thread.looper)

        // восстановить сохранённые настройки
        sbIso.progress = prefs.getInt("iso", 200)
        sbExp.progress = prefs.getInt("exp", 500)
        sbFocus.progress = prefs.getInt("focus", 200)
        sbStack.progress = prefs.getInt("stack", 28)
        cbStackSum.isChecked = true
        sbBoost.progress = prefs.getInt("boost", 0)
        sbTl.progress = prefs.getInt("tlIdx", 4).coerceIn(0, tlIntervals.size - 1)
        cbTlJpeg.isChecked = prefs.getBoolean("tlJpeg", false)
        cbTlLock.isChecked = prefs.getBoolean("tlLock", false)
        mode = prefs.getInt("mode", 0).coerceIn(0, 2)
        cameraId = prefs.getString("camId", "3") ?: "3"
        if (!camIds.contains(cameraId)) cameraId = "3"
        btnCam.text = "Камера: " + camLabel(cameraId)
        updateModeUi()
        nrMode = prefs.getInt("nrMode", -1)
        edgeMode = prefs.getInt("edgeMode", -1)
        updateModeButtons()
        useHevc = prefs.getBoolean("hevc", true) && hasHevcEncoder()
        btnCodec.text = codecLabel()
        bitrateIdx = prefs.getInt("bitrate2", 0).coerceIn(0, bitrates.size - 1)
        vFps = prefs.getInt("vfps", 30)
        btnBitrate.text = bitrateLabel()
        resIdx = prefs.getInt("res", 1).coerceIn(0, 1)
        usePersistent = (mode == 1)
        btnRes.text = resLabel()
        cbExp.isChecked = prefs.getBoolean("manExp", false)
        cbFocus.isChecked = prefs.getBoolean("manFocus", false)
        cbFlip.isChecked = prefs.getBoolean("flip", false)
        sbZoom.progress = prefs.getInt("zoom", 0)
        aspectMode = prefs.getInt("aspect", 0).coerceIn(0, 2)
        btnAspect.text = aspectLabel()
        updateModeUi()
        texture.rotation = if (cbFlip.isChecked) 180f else 0f
        texture.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ -> updateTransform() }
        texture.surfaceTextureListener = object : TextureView.SurfaceTextureListener {
            override fun onSurfaceTextureAvailable(st: SurfaceTexture, w: Int, h: Int) {
                updateTransform()
                if (!reopenPending) tryAutoOpen()
            }
            override fun onSurfaceTextureSizeChanged(st: SurfaceTexture, w: Int, h: Int) {
                updateTransform()
                // размер экрана изменился уже после запуска камеры (так бывает при возврате из галереи):
                // перезапускаем камеру, когда размер устоится
                if (device != null && !recording && !stacking && !tlRunning && startedViewW > 0 &&
                    (w != startedViewW || h != startedViewH)
                ) scheduleRestart(600)
            }
            override fun onSurfaceTextureDestroyed(st: SurfaceTexture): Boolean = true
            override fun onSurfaceTextureUpdated(st: SurfaceTexture) {
                if (coverPending) {
                    coverPending = false
                    previewCover.visibility = View.GONE
                }
                // самолечение: раз в 10 кадров проверяем, не устарела ли матрица превью
                // (после возврата из галереи система могла сообщить неверный поворот или размер)
                if (++frameCounter % 10 == 0 && transformKey() != appliedTransformKey) updateTransform()
            }
        }

        btnPhoto.setOnClickListener { takePhoto() }
        btnRec.setOnClickListener {
            if (recording) stopRecording() else startRecording()
        }
        btnTl.setOnClickListener {
            if (tlRunning) handler.post { finishTimelapse(null, true) } else startTimelapse()
        }

        val seekListener = object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(s: SeekBar?, p: Int, fromUser: Boolean) {
                updateLabels()
                if (fromUser) {
                    savePrefs()
                    updateRepeating()
                }
            }
            override fun onStartTrackingTouch(s: SeekBar?) {}
            override fun onStopTrackingTouch(s: SeekBar?) {}
        }
        sbIso.setOnSeekBarChangeListener(seekListener)
        sbExp.setOnSeekBarChangeListener(seekListener)
        sbFocus.setOnSeekBarChangeListener(seekListener)
        sbZoom.setOnSeekBarChangeListener(seekListener)
        sbStack.setOnSeekBarChangeListener(seekListener)
        sbBoost.setOnSeekBarChangeListener(seekListener)
        sbTl.setOnSeekBarChangeListener(seekListener)
        btnStack.setOnClickListener { startStack() }
        btnMode.setOnClickListener { toggleMode() }
        btnPause.setOnClickListener { togglePause() }
        btnGallery.setOnClickListener { openGallery() }
        btnTorch.setOnClickListener { toggleTorch() }
        btnCam.setOnClickListener { switchCamera() }
        btnServer.setOnClickListener { toggleServer() }
        btnSave.setOnClickListener { setSaveMode(true) }
        val tapViews = listOf<View>(
            btnPanel, btnMode, btnPhoto, btnStack, btnRec,
            btnAspect, btnRes, btnCodec, btnNr, btnEdge, btnBitrate, cbExp, cbFocus, cbFlip, cbStackSum,
            btnPause, btnGallery, btnTorch, btnSave, btnServer, btnCam, btnTl, btnPreview, btnFps, cbTlJpeg, cbTlLock
        )
        for (v in tapViews) {
            v.setOnTouchListener { vv, ev ->
                if (ev.action == MotionEvent.ACTION_DOWN) {
                    vv.performHapticFeedback(
                        HapticFeedbackConstants.KEYBOARD_TAP,
                        HapticFeedbackConstants.FLAG_IGNORE_GLOBAL_SETTING
                    )
                }
                false
            }
        }
        btnNr.setOnClickListener {
            nrMode = nextMode(
                nrMode,
                chars?.get(CameraCharacteristics.NOISE_REDUCTION_AVAILABLE_NOISE_REDUCTION_MODES),
                intArrayOf(0, 1, 2, 3, 4)
            )
            updateModeButtons()
            savePrefs()
            updateRepeating()
        }
        btnEdge.setOnClickListener {
            edgeMode = nextMode(
                edgeMode,
                chars?.get(CameraCharacteristics.EDGE_AVAILABLE_EDGE_MODES),
                intArrayOf(0, 1, 2, 3)
            )
            updateModeButtons()
            savePrefs()
            updateRepeating()
        }
        btnFps.setOnClickListener {
            if (recording || stacking || tlRunning) { log("Сначала остановите запись, долгую выдержку или таймлапс"); return@setOnClickListener }
            val av = fpsOptions()
            if (av.size <= 1) {
                log("Эта камера с выбранным разрешением и кодеком даёт только " + effectiveFps() + " к/с")
                return@setOnClickListener
            }
            val cur = effectiveFps()
            val next = av[(av.indexOf(cur) + 1) % av.size]
            vFps = next
            btnFps.text = fpsLabel()
            savePrefs()
            log("Частота кадров видео: " + next + " к/с" + (if (next > 60) " (скоростной режим: ручные ISO/выдержка не работают)" else ""))
            if ((cur > 60) != (next > 60)) restartSession() else updateRepeating()
        }
        btnBitrate.setOnClickListener {
            if (recording) {
                log("Битрейт нельзя менять во время записи")
            } else {
                bitrateIdx = (bitrateIdx + 1) % bitrates.size
                btnBitrate.text = bitrateLabel()
                savePrefs()
            }
        }
        cbStackSum.setOnCheckedChangeListener { _, _ -> savePrefs() }
        cbTlJpeg.setOnCheckedChangeListener { _, _ -> savePrefs() }
        cbTlLock.setOnCheckedChangeListener { _, _ -> savePrefs(); updateRepeating() }
        btnAspect.setOnClickListener { toggleAspect() }
        btnRes.setOnClickListener { toggleResolution() }
        btnCodec.setOnClickListener { toggleCodec() }
        btnPreview.setOnClickListener { setPreviewEnabled(previewOff) }
        btnPanel.setOnClickListener {
            panel.visibility = if (panel.visibility == View.VISIBLE) View.GONE else View.VISIBLE
        }
        cbExp.setOnCheckedChangeListener { _, _ -> savePrefs(); updateRepeating() }
        cbFocus.setOnCheckedChangeListener { _, _ -> savePrefs(); updateRepeating() }
        cbFlip.setOnCheckedChangeListener { _, checked ->
            texture.rotation = if (checked) 180f else 0f
            savePrefs()
        }
        applyTicks()
        updateLabels()

        val need = ArrayList<String>()
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
            need.add(Manifest.permission.CAMERA)
        }
        if (checkSelfPermission(Manifest.permission.RECORD_AUDIO) != PackageManager.PERMISSION_GRANTED) {
            need.add(Manifest.permission.RECORD_AUDIO)
        }
        if (need.isNotEmpty()) requestPermissions(need.toTypedArray(), 1)

        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        torchCb = object : CameraManager.TorchCallback() {
            override fun onTorchModeChanged(cameraId: String, enabled: Boolean) {
                // пока камера открыта, фонарик управляется через сессию камеры, а не системой
                if (cameraId == torchId && device == null) {
                    torchOn = enabled
                    runOnUiThread { btnTorch.text = if (enabled) "Фонарик: вкл" else "Фонарик: выкл" }
                }
            }
        }
        try { cm.registerTorchCallback(torchCb!!, handler) } catch (_: Exception) {}
    }

    private fun savePrefs() {
        prefs.edit()
            .putInt("iso", sbIso.progress)
            .putInt("exp", sbExp.progress)
            .putInt("focus", sbFocus.progress)
            .putBoolean("manExp", cbExp.isChecked)
            .putBoolean("manFocus", cbFocus.isChecked)
            .putBoolean("flip", cbFlip.isChecked)
            .putInt("zoom", sbZoom.progress)
            .putInt("stack", sbStack.progress)
            .putBoolean("stackSum", cbStackSum.isChecked)
            .putInt("boost", sbBoost.progress)
            .putInt("nrMode", nrMode)
            .putInt("mode", mode)
            .putString("camId", cameraId)
            .putInt("edgeMode", edgeMode)
            .putInt("bitrate2", bitrateIdx)
            .putInt("vfps", vFps)
            .putBoolean("hevc", useHevc)
            .putInt("res", resIdx)
            .putInt("aspect", aspectMode)
            .putInt("tlIdx", sbTl.progress)
            .putBoolean("tlJpeg", cbTlJpeg.isChecked)
            .putBoolean("tlLock", cbTlLock.isChecked)
            .apply()
    }

    private fun log(s: String) {
        synchronized(logBuf) {
            logBuf.add(s)
            if (logBuf.size > 40) logBuf.removeAt(0)
            fullLog.append(logTimeFmt.format(Date())).append(' ').append(s).append('\n')
            if (fullLog.length > 100_000) fullLog.delete(0, fullLog.length - 80_000)
        }
        runOnUiThread {
            logView.append(s + "\n")
            logScroll.post { logScroll.fullScroll(ScrollView.FOCUS_DOWN) }
        }
    }

    // ---------- метаданные и звук ----------

    private fun stamp(): String =
        SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(Date())

    private fun nrTag(m: Int): String =
        if (m < 0) "auto" else arrayOf("off", "fast", "hq", "min", "zsl").getOrElse(m) { m.toString() }

    private fun edgeTag(m: Int): String =
        if (m < 0) "auto" else arrayOf("off", "fast", "hq", "zsl").getOrElse(m) { m.toString() }

    private fun fmtExp(ns: Long): String =
        if (ns >= 300_000_000L) String.format(Locale.US, "%.2f s", ns / 1e9)
        else "1/" + (1_000_000_000.0 / ns).toInt() + " s"

    private fun tagExp(ns: Long): String =
        if (ns >= 300_000_000L) String.format(Locale.US, "%.2fs", ns / 1e9)
        else "1-" + (1_000_000_000.0 / ns).toInt() + "s"

    private fun focusText(): String {
        if (!cbFocus.isChecked) return "auto"
        val f = currentFocus()
        return if (f < 0.01f) "infinity" else String.format(Locale.US, "%.1f cm (%.1f D)", 100f / f, f)
    }

    private fun shotInfo(longFrames: Int = 0, frameExpNs: Long = 0L, totalNs: Long = 0L): String {
        val sb = StringBuilder("Exposure ")
        if (longFrames == 1) {
            sb.append(String.format(Locale.US, "%.1f s single long exposure", (if (totalNs > 0L) totalNs else frameExpNs) / 1e9))
        } else if (longFrames > 1) {
            sb.append(String.format(Locale.US, "%.1f s total (%d frames, up to %s each)",
                (if (totalNs > 0L) totalNs else longFrames * frameExpNs) / 1e9, longFrames, fmtExp(frameExpNs)))
        } else {
            sb.append(if (cbExp.isChecked) fmtExp(currentExp()) else "auto")
        }
        sb.append("; ISO ").append(if (cbExp.isChecked) currentIso().toString() else "auto")
        val br = boostRange
        sb.append("; digital gain ")
            .append(if (cbExp.isChecked && br != null && br.upper > 100) currentBoost().toString() + "%" else "none")
        sb.append("; noise reduction ").append(nrTag(nrMode))
        sb.append("; edge ").append(edgeTag(edgeMode))
        sb.append("; focus ").append(focusText())
        sb.append("; zoom ").append(String.format(Locale.US, "%.1fx", currentZoom()))
        return sb.toString()
    }

    private fun fileTag(longFrames: Int = 0, frameExpNs: Long = 0L, totalNs: Long = 0L): String {
        val sb = StringBuilder()
        if (longFrames > 0) {
            sb.append("long").append(String.format(Locale.US, "%.0fs", (if (totalNs > 0L) totalNs else longFrames * frameExpNs) / 1e9))
            if (longFrames > 1) sb.append("_").append(longFrames).append("x").append(tagExp(frameExpNs))
        } else {
            sb.append("exp").append(if (cbExp.isChecked) tagExp(currentExp()) else "auto")
        }
        sb.append("_ISO").append(if (cbExp.isChecked) currentIso().toString() else "auto")
        val br = boostRange
        if (cbExp.isChecked && br != null && br.upper > 100) sb.append("_G").append(currentBoost())
        sb.append("_NR").append(nrTag(nrMode))
        sb.append("_ED").append(edgeTag(edgeMode))
        val f = currentFocus()
        sb.append("_F").append(
            if (!cbFocus.isChecked) "auto"
            else if (f < 0.01f) "inf"
            else String.format(Locale.US, "%.1fcm", 100f / f)
        )
        return sb.toString()
    }

    private fun videoName(): String {
        if (mode == 2) {
            val iv = tlInterval()
            videoInfo = shotInfo() + "; timelapse interval " + iv + " s, " + tlFps + " fps, speed x" + (iv * tlFps)
            return "macro_" + stamp() + "_tl" + iv + "s_" + fileTag()
        }
        videoInfo = shotInfo() + "; video " + activeFps() + " fps; video stabilization " + (if (stabOn) "on" else "off")
        return "macro_" + stamp() + "_" + fileTag()
    }

    private fun beep() {
        Thread {
            try {
                val sr = 44100
                val n = sr * 80 / 1000
                val data = ShortArray(n)
                for (i in 0 until n) {
                    val fade = min(1.0, min(i, n - i) / (sr * 0.005))
                    data[i] = (Math.sin(2.0 * Math.PI * 1000.0 * i / sr) * 12000.0 * fade).toInt().toShort()
                }
                val track = AudioTrack.Builder()
                    .setAudioAttributes(
                        AudioAttributes.Builder()
                            .setUsage(AudioAttributes.USAGE_MEDIA)
                            .setContentType(AudioAttributes.CONTENT_TYPE_SONIFICATION)
                            .build()
                    )
                    .setAudioFormat(
                        AudioFormat.Builder()
                            .setEncoding(AudioFormat.ENCODING_PCM_16BIT)
                            .setSampleRate(sr)
                            .setChannelMask(AudioFormat.CHANNEL_OUT_MONO)
                            .build()
                    )
                    .setBufferSizeInBytes(n * 2)
                    .setTransferMode(AudioTrack.MODE_STATIC)
                    .build()
                track.write(data, 0, n)
                track.play()
                Thread.sleep(200)
                track.release()
            } catch (_: Exception) {
            }
        }.start()
    }

    // Записывает текст в MP4 как атом ©cmt внутри udta (в конец moov), только если moov стоит в конце файла
    private fun embedMp4Comment(uri: Uri, text: String) {
        try {
            val rw = contentResolver.openFileDescriptor(uri, "rw")
            if (rw == null) { log("Видео: не удалось открыть файл для метаданных"); return }
            rw.use { p ->
                val inCh = FileInputStream(p.fileDescriptor).channel
                val outCh = FileOutputStream(p.fileDescriptor).channel
                val len = inCh.size()
                var pos = 0L
                var moovPos = -1L
                var moovSize = 0L
                val hdr = ByteBuffer.allocate(8)
                while (pos + 8 <= len) {
                    hdr.clear()
                    if (inCh.read(hdr, pos) < 8) break
                    hdr.flip()
                    val size32 = hdr.int.toLong() and 0xFFFFFFFFL
                    val type = hdr.int
                    if (size32 < 8) break
                    if (type == 0x6D6F6F76) { moovPos = pos; moovSize = size32 }
                    pos += size32
                }
                if (moovPos < 0 || moovPos + moovSize != len) {
                    log("Видео: метаданные в файл не записаны (нестандартная структура), они есть в имени файла")
                    return@use
                }
                val bytes = text.toByteArray(Charsets.US_ASCII)
                val cmtSize = 8 + 4 + bytes.size
                val udtaSize = 8 + cmtSize
                val buf = ByteBuffer.allocate(udtaSize)
                buf.putInt(udtaSize)
                buf.putInt(0x75647461)
                buf.putInt(cmtSize)
                buf.putInt(0xA9636D74L.toInt())
                buf.putShort(bytes.size.toShort())
                buf.putShort(0x15C7.toShort())
                buf.put(bytes)
                buf.flip()
                val newMoov = ByteBuffer.allocate(4)
                newMoov.putInt((moovSize + udtaSize).toInt())
                newMoov.flip()
                outCh.write(buf, len)
                outCh.write(newMoov, moovPos)
                log("Видео: параметры записаны в файл (комментарий) и в имя")
            }
        } catch (e: Exception) {
            log("Видео: метаданные не записаны: $e")
        }
    }

    // размер файла по uri в байтах; -1, если файл недоступен
    private fun mediaSize(uri: Uri): Long = try {
        contentResolver.openFileDescriptor(uri, "r")?.use { it.statSize } ?: -1L
    } catch (_: Exception) {
        -1L
    }

    // «имя, размер», если запись о файле есть в галерее (MediaStore); null, если записи нет
    private fun describeMedia(uri: Uri): String? = try {
        contentResolver.query(
            uri,
            arrayOf(MediaStore.MediaColumns.DISPLAY_NAME, MediaStore.MediaColumns.SIZE),
            null, null, null
        )?.use { c ->
            if (c.moveToFirst()) {
                val size = c.getLong(1)
                val sz = if (size >= 1_048_576L) String.format(Locale.US, "%.1f МБ", size / 1048576.0)
                else (size / 1024).toString() + " КБ"
                c.getString(0) + ", " + sz
            } else null
        }
    } catch (_: Exception) {
        null
    }

    // Файл создаётся скрытым (IS_PENDING=1) и появляется в галерее только после успешной записи
    private fun createVideoEntry(): Uri? {
        val values = ContentValues().apply {
            put(MediaStore.Video.Media.DISPLAY_NAME, videoName() + ".mp4")
            put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
            put(MediaStore.Video.Media.RELATIVE_PATH, "Movies/MacroCam")
            put(MediaStore.Video.Media.IS_PENDING, 1)
        }
        val uri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
        videoUri = uri
        return uri
    }

    // убрать недозаписанный файл, если запись не началась
    private fun discardVideoEntry() {
        val u = videoUri
        videoUri = null
        videoInfo = null
        if (u != null) {
            try { contentResolver.delete(u, null, null) } catch (_: Exception) {}
        }
    }

    // Проверяет, что файл реально записан, и пишет в лог итог: сохранено или нет и почему
    private fun finishVideoFile(stopOk: Boolean, why: String?) {
        beep()
        val u = videoUri
        val info = videoInfo
        paused = false
        videoUri = null
        videoInfo = null
        if (u == null) {
            log("Видео НЕ сохранено: файл не был создан")
            return
        }
        val size = mediaSize(u)
        if (!stopOk || size < 2048) {
            try { contentResolver.delete(u, null, null) } catch (_: Exception) {}
            log("Видео НЕ сохранено: " + (why ?: "в файл не попало ни одного кадра") +
                " (размер файла " + size + " байт)")
            return
        }
        if (info != null) embedMp4Comment(u, info)
        try {
            val done = ContentValues()
            done.put(MediaStore.Video.Media.IS_PENDING, 0)
            contentResolver.update(u, done, null, null)
        } catch (e: Exception) {
            log("Видео записано, но не добавлено в галерею: $e")
            return
        }
        val desc = describeMedia(u)
        if (desc == null) {
            log("Видео НЕ найдено в галерее после сохранения (запись о файле пропала)")
        } else {
            rememberLast(u, "video/mp4")
            log("Видео сохранено: Movies/MacroCam/$desc")
        }
    }

    // ---------- значения ползунков ----------

    private fun currentIso(): Int {
        val r = isoRange ?: return 100
        return (r.lower + (r.upper - r.lower) * (sbIso.progress / 1000.0)).toInt()
    }

    private fun currentExp(): Long {
        val r = expRange ?: return 10_000_000L
        val lo = r.lower.toDouble()
        val hi = max(5_000_000_000L, r.lower + 1).toDouble() // ползунок «Выдержка» доходит до 5 с
        return (lo * (hi / lo).pow(sbExp.progress / 1000.0)).toLong()
    }

    private fun currentBoost(): Int {
        val r = boostRange ?: return 100
        return (r.lower + (r.upper - r.lower) * (sbBoost.progress / 1000.0)).toInt()
    }

    private fun currentFocus(): Float = (1f - sbFocus.progress / 1000f) * minFocus

    private fun currentZoom(): Float =
        maxZoom.toDouble().pow(sbZoom.progress / 1000.0).toFloat()

    private fun codecLabel(): String = "Кодек: " + (if (useHevc) "H.265" else "H.264")

    private fun hasHevcEncoder(): Boolean = try {
        MediaCodecList(MediaCodecList.REGULAR_CODECS).codecInfos.any { it.isEncoder && it.supportedTypes.contains("video/hevc") }
    } catch (_: Exception) {
        false
    }

    private fun videoEncoderType(): Int =
        if (useHevc) MediaRecorder.VideoEncoder.HEVC else MediaRecorder.VideoEncoder.H264

    private fun toggleCodec() {
        if (recording || stacking || tlRunning) { log("Сначала остановите запись, долгую выдержку или таймлапс"); return }
        if (!useHevc && !hasHevcEncoder()) { log("Кодер H.265 на этом телефоне недоступен"); return }
        useHevc = !useHevc
        bitrateIdx = bitrateIdx.coerceIn(0, bitrates.size - 1)
        btnCodec.text = codecLabel()
        btnBitrate.text = bitrateLabel()
        savePrefs()
        restartSession()
    }

    private fun bitrateLabel(): String {
        val v = bitrates[bitrateIdx]
        return "Битрейт: $v Мбит/с"
    }

    private fun aspectLabel(): String = "Формат: " + arrayOf("4:3", "16:9", "20:9")[aspectMode]

    private fun stabLabel(): String = "Стабилизация: " + (if (stabOn) "вкл" else "выкл")

    // что умеет текущая камера: электронная (EIS) и оптическая (OIS) стабилизация
    private fun hasEis(): Boolean =
        chars?.get(CameraCharacteristics.CONTROL_AVAILABLE_VIDEO_STABILIZATION_MODES)
            ?.contains(CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_ON) == true

    private fun hasOis(): Boolean =
        chars?.get(CameraCharacteristics.LENS_INFO_AVAILABLE_OPTICAL_STABILIZATION)
            ?.contains(CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON) == true

    private fun stabSupportText(): String =
        "электронная " + (if (hasEis()) "есть" else "нет") + ", оптическая " + (if (hasOis()) "есть" else "нет")

    // Стабилизация действует в превью и при записи видео, чтобы эффект был виден сразу;
    // фото и долгая выдержка (stab=false) идут как раньше
    private fun applyStabilization(b: CaptureRequest.Builder) {
        if (hasEis()) {
            b.set(
                CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE,
                if (stabOn) CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_ON
                else CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_OFF
            )
        }
        if (hasOis()) {
            b.set(
                CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE,
                if (stabOn) CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON
                else CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_OFF
            )
        }
    }

    private fun updateLabels() {
        tvIso.text = "ISO: " + currentIso()
        val exp = currentExp()
        val er0 = expRange
        val devMax0 = if (er0 != null) min(er0.upper, maxFrameDuration) else Long.MAX_VALUE
        val warn = if (exp > devMax0) String.format(Locale.US, " (камера даёт до %.1f с)", devMax0 / 1e9) else ""
        tvExp.text = (if (exp >= 300_000_000L) String.format("Выдержка: %.2f с", exp / 1e9)
        else "Выдержка: 1/" + (1_000_000_000.0 / exp).toInt() + " с") + warn
        val total = sbStack.progress + 2
        val nFr = (total + 29) / 30
        tvStack.text = if (nFr <= 1) "Долгая выдержка: " + total + " с (один кадр)"
        else "Долгая выдержка: " + total + " с (кадров: " + nFr + " — по 30 с, последний " + (total - (nFr - 1) * 30) + " с)"
        val br = boostRange
        if (br != null && br.upper > 100) {
            tvBoost.text = "Цифровое усиление: " + currentBoost() + "% (ISO ≈ " + (currentIso() * currentBoost() / 100) + ")"
        }
        val f = currentFocus()
        val dist = if (f < 0.01f) "бесконечность" else String.format("%.1f см", 100f / f)
        tvFocus.text = String.format("Фокус: %.1f дптр (%s)", f, dist)
        tvZoom.text = String.format("Зум: %.1fx", currentZoom())
        tvTl.text = tlLabel()
    }

    private fun applyZoom(b: CaptureRequest.Builder) {
        val z = currentZoom()
        val ratioRange = if (Build.VERSION.SDK_INT >= 30)
            chars?.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE) else null
        if (Build.VERSION.SDK_INT >= 30 && ratioRange != null) {
            b.set(CaptureRequest.CONTROL_ZOOM_RATIO, z.coerceIn(ratioRange.lower, ratioRange.upper))
        } else {
            val a = chars?.get(CameraCharacteristics.SENSOR_INFO_ACTIVE_ARRAY_SIZE)
            if (a != null) {
                val w = (a.width() / z).toInt()
                val h = (a.height() / z).toInt()
                val l = a.left + (a.width() - w) / 2
                val t = a.top + (a.height() - h) / 2
                b.set(CaptureRequest.SCALER_CROP_REGION, Rect(l, t, l + w, t + h))
            }
        }
    }

    private fun nrName(m: Int): String = when (m) {
        -1 -> "авто"
        0 -> "выкл"
        1 -> "быстрое"
        2 -> "высокое"
        3 -> "минимальное"
        4 -> "ZSL"
        else -> m.toString()
    }

    private fun edgeName(m: Int): String = when (m) {
        -1 -> "авто"
        0 -> "выкл"
        1 -> "быстрый"
        2 -> "высокий"
        3 -> "ZSL"
        else -> m.toString()
    }

    private fun nextMode(current: Int, supported: IntArray?, fallback: IntArray): Int {
        val list = listOf(-1) + (supported ?: fallback).sorted()
        val i = list.indexOf(current)
        return list[(i + 1) % list.size]
    }

    private fun updateModeButtons() {
        btnNr.text = "Шумоподавление: " + nrName(nrMode)
        btnEdge.text = "Контуры: " + edgeName(edgeMode)
    }

    private fun applyProcessing(b: CaptureRequest.Builder) {
        val c = chars ?: return
        if (nrMode >= 0) {
            val m = c.get(CameraCharacteristics.NOISE_REDUCTION_AVAILABLE_NOISE_REDUCTION_MODES)
            if (m != null && m.contains(nrMode)) {
                b.set(CaptureRequest.NOISE_REDUCTION_MODE, nrMode)
            }
        }
        if (edgeMode >= 0) {
            val e = c.get(CameraCharacteristics.EDGE_AVAILABLE_EDGE_MODES)
            if (e != null && e.contains(edgeMode)) {
                b.set(CaptureRequest.EDGE_MODE, edgeMode)
            }
        }
    }

    private fun applyControls(b: CaptureRequest.Builder, record: Boolean, stab: Boolean = true) {
        if (hsActive && mode == 1) { applyHsControls(b); return }
        applyZoom(b)
        applyProcessing(b)
        if (stab) applyStabilization(b)
        if (cbExp.isChecked && isoRange != null && expRange != null) {
            val exp = currentExp()
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_OFF)
            b.set(CaptureRequest.SENSOR_SENSITIVITY, currentIso())
            b.set(CaptureRequest.SENSOR_EXPOSURE_TIME, exp)
            val minDur = if (mode == 1) 1_000_000_000L / activeFps() else 33_333_333L
            b.set(CaptureRequest.SENSOR_FRAME_DURATION, max(exp, minDur))
            val br = boostRange
            if (br != null && br.upper > 100) {
                b.set(CaptureRequest.CONTROL_POST_RAW_SENSITIVITY_BOOST, currentBoost())
            }
        } else {
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_ON)
        }
        if (mode == 1) {
            val fr = fpsRangeFor(activeFps())
            if (fr != null) b.set(CaptureRequest.CONTROL_AE_TARGET_FPS_RANGE, fr)
        }
        // builder переиспользуется, поэтому выключение нужно задавать явно, иначе «фонарик» остаётся в запросе
        b.set(
            CaptureRequest.FLASH_MODE,
            if (torchOn) CameraMetadata.FLASH_MODE_TORCH else CameraMetadata.FLASH_MODE_OFF
        )
        if (cbFocus.isChecked) {
            b.set(CaptureRequest.CONTROL_AF_MODE, CameraMetadata.CONTROL_AF_MODE_OFF)
            b.set(CaptureRequest.LENS_FOCUS_DISTANCE, focusOverride ?: currentFocus())
        } else {
            val want = if (record) CameraMetadata.CONTROL_AF_MODE_CONTINUOUS_VIDEO
            else CameraMetadata.CONTROL_AF_MODE_CONTINUOUS_PICTURE
            val modes = chars?.get(CameraCharacteristics.CONTROL_AF_AVAILABLE_MODES)
            if (modes != null && modes.contains(want)) {
                b.set(CaptureRequest.CONTROL_AF_MODE, want)
            }
        }
        // таймлапс: блокировка экспозиции и баланса белого, чтобы кадры не мигали;
        // во время съёмки блокировка включается после короткого прогрева автоэкспозиции
        val lock = mode == 2 && cbTlLock.isChecked && (!tlRunning || tlLockEngaged)
        val cc = chars
        if (cc?.get(CameraCharacteristics.CONTROL_AE_LOCK_AVAILABLE) == true) {
            b.set(CaptureRequest.CONTROL_AE_LOCK, lock && !cbExp.isChecked)
        }
        if (cc?.get(CameraCharacteristics.CONTROL_AWB_LOCK_AVAILABLE) == true) {
            b.set(CaptureRequest.CONTROL_AWB_LOCK, lock)
        }
    }

    // сессия с параметрами (стабилизация передаётся камере при создании сессии, как требуют многие телефоны)
    private fun createSessionWithParams(
        cam: CameraDevice, targets: List<Surface>, params: CaptureRequest?, cb: CameraCaptureSession.StateCallback
    ) {
        if (Build.VERSION.SDK_INT >= 28 && params != null) {
            try {
                val outs = targets.map { OutputConfiguration(it) }
                val cfg = SessionConfiguration(
                    SessionConfiguration.SESSION_REGULAR, outs, { r -> handler.post(r) }, cb
                )
                cfg.sessionParameters = params
                cam.createCaptureSession(cfg)
                return
            } catch (e: Exception) {
                log("Сессия с параметрами не создалась ($e), создаю обычную")
            }
        }
        cam.createCaptureSession(targets, cb, handler)
    }

    private fun updateRepeating() {
        if (previewOff) return
        val b = builder ?: return
        val s = session ?: return
        try {
            applyControls(b, recording, !stacking && !tlRunning)
            setRepeatingAny(s, b)
        } catch (e: Exception) {
            log("Ошибка обновления: $e")
        }
    }

    // ---------- открытие камеры ----------

    private fun closeAll() {
        clearPreviewOff()
        try { session?.close() } catch (_: Exception) {}
        try { device?.close() } catch (_: Exception) {}
        try { imageReader?.close() } catch (_: Exception) {}
        try { persistentSurface?.release() } catch (_: Exception) {}
        persistentSurface = null
        sessionHasRecorder = false
        hsActive = false
        rampToken++
        rampActive = false
        focusOverride = null
        session = null
        device = null
        builder = null
        imageReader = null
    }

    private fun readCharacteristics(id: String) {
        chars = null
        isoRange = null
        expRange = null
        minFocus = 0f
        maxZoom = 1f
        streamMap = null
        boostRange = null
        maxFrameDuration = Long.MAX_VALUE
        try {
            val c = cm.getCameraCharacteristics(id)
            chars = c
            hsDisabled = false
            isoRange = c.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE)
            expRange = c.get(CameraCharacteristics.SENSOR_INFO_EXPOSURE_TIME_RANGE)
            minFocus = c.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE) ?: 0f
            log("ISO $isoRange, выдержка $expRange нс, мин. фокус $minFocus дптр")
            maxFrameDuration = c.get(CameraCharacteristics.SENSOR_INFO_MAX_FRAME_DURATION) ?: Long.MAX_VALUE
            boostRange = c.get(CameraCharacteristics.CONTROL_POST_RAW_SENSITIVITY_BOOST_RANGE)
            log("Цифровое усиление (post-RAW boost): $boostRange; макс. длительность кадра $maxFrameDuration нс")
            log("Шумоподавление: " + c.get(CameraCharacteristics.NOISE_REDUCTION_AVAILABLE_NOISE_REDUCTION_MODES)?.joinToString() +
                "; контуры: " + c.get(CameraCharacteristics.EDGE_AVAILABLE_EDGE_MODES)?.joinToString() +
                "; стабилизация видео: " + c.get(CameraCharacteristics.CONTROL_AVAILABLE_VIDEO_STABILIZATION_MODES)?.joinToString() +
                "; OIS: " + c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_OPTICAL_STABILIZATION)?.joinToString())

            val rr = if (Build.VERSION.SDK_INT >= 30)
                c.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE) else null
            val rawMax = rr?.upper
                ?: (c.get(CameraCharacteristics.SCALER_AVAILABLE_MAX_DIGITAL_ZOOM) ?: 1f)
            maxZoom = max(1f, min(rawMax, 10f))
            streamMap = c.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)
            computeSizes()
        } catch (e: Exception) {
            log("Характеристики недоступны: $e")
        }
        runOnUiThread {
            val br = boostRange
            val show = if (br != null && br.upper > 100) View.VISIBLE else View.GONE
            tvBoost.visibility = show
            sbBoost.visibility = show
            updateLabels()
        }
    }

    private fun sizesFor(sizes: Array<Size>?, maxPixels: Int = Int.MAX_VALUE): List<Size> {
        if (sizes == null) return emptyList()
        val target = doubleArrayOf(4.0 / 3.0, 16.0 / 9.0, 20.0 / 9.0)[aspectMode]
        return sizes
            .filter { it.width.toLong() * it.height <= maxPixels }
            .filter { Math.abs(it.width.toDouble() / it.height - target) < 0.02 }
            .sortedByDescending { it.width * it.height }
    }

    // размеры видео, на которых запись уже сломалась (ошибка рекордера): больше их не предлагаем
    private val badVideoSizes = HashSet<String>()

    // кодер H.264 должен реально поддерживать размер (иначе запись ломается уже в процессе)
    private fun encoderSupports(w: Int, h: Int): Boolean = try {
        val mime = if (useHevc) "video/hevc" else "video/avc"
        MediaCodecList(MediaCodecList.REGULAR_CODECS).codecInfos.any { ci ->
            ci.isEncoder && ci.supportedTypes.contains(mime) &&
                ci.getCapabilitiesForType(mime).videoCapabilities.isSizeSupported(w, h)
        }
    } catch (_: Exception) {
        true
    }

    private var lastSizesLogKey = ""

    private fun computeSizes() {
        val map = streamMap ?: return
        // видео: не больше 4K, только размеры, которые тянет кодер, и не помеченные как сбойные
        val vids = sizesFor(map.getOutputSizes(MediaRecorder::class.java), 3840 * 2160)
            .filter { !badVideoSizes.contains(it.toString()) && encoderSupports(it.width, it.height) }
        // «Макс» = самый большой размер выбранного формата, «Норм» = самый большой не больше ~2,1 Мпикс
        // (16:9 это 1920x1080, 4:3 это 1600x1200); в формате 20:9 один размер, самый большой
        val chosen: Size? = if (resIdx == 1 && aspectMode != 2) {
            vids.firstOrNull { it.width.toLong() * it.height <= 2_100_000L } ?: vids.firstOrNull()
        } else {
            vids.firstOrNull()
        }
        videoCandidates = if (chosen == null) vids else {
            listOf(chosen) + vids.filter { it != chosen && it.width.toLong() * it.height < chosen.width.toLong() * chosen.height }
        }
        videoSize = videoCandidates.firstOrNull() ?: videoSize
        // превью: в режиме фото максимальное (фото берётся из превью), в режиме видео не больше размера видео
        val previewMax = when (mode) {
            0 -> 13_000_000
            2 -> min(videoSize.width * videoSize.height, 2_100_000)
            else -> videoSize.width * videoSize.height
        }
        previewSize = sizesFor(map.getOutputSizes(SurfaceTexture::class.java), previewMax).firstOrNull() ?: previewSize
        photoSize = sizesFor(map.getOutputSizes(ImageFormat.YUV_420_888), 13_000_000).firstOrNull() ?: photoSize
        log(aspectLabel() + ": превью $previewSize, видео $videoSize, фото $photoSize")
        // один раз для камеры и формата: почему каждый размер видео подходит или нет
        val key = cameraId + "/" + aspectMode
        if (key != lastSizesLogKey) {
            lastSizesLogKey = key
            val all = sizesFor(map.getOutputSizes(MediaRecorder::class.java), Int.MAX_VALUE)
            log("Размеры видео камеры " + cameraId + ", " + aspectLabel() + ": " + all.joinToString("; ") {
                it.toString() + " " + when {
                    it.width.toLong() * it.height > 3840L * 2160L -> "больше 4K, пропущен"
                    badVideoSizes.contains(it.toString()) -> "ранее сбоил, пропущен"
                    !encoderSupports(it.width, it.height) -> "кодер не поддерживает"
                    else -> "подходит"
                }
            })
        }
        refreshFpsOptions()
        if (isHsMode() && previewSize != videoSize) previewSize = videoSize
        runOnUiThread { btnRes.text = resLabel(); btnFps.text = fpsLabel() }
        updateTransform()
    }

    // ---------- частота кадров видео ----------

    // диапазон AE для нужной частоты: лучше точный [f,f], иначе самый «жёсткий» из подходящих
    private fun fpsRangeFor(f: Int): android.util.Range<Int>? {
        val rs = chars?.get(CameraCharacteristics.CONTROL_AE_AVAILABLE_TARGET_FPS_RANGES) ?: return null
        return rs.firstOrNull { it.lower == f && it.upper == f }
            ?: rs.filter { it.upper == f }.maxByOrNull { it.lower }
            ?: rs.filter { it.lower <= f && it.upper >= f }.maxByOrNull { it.lower }
    }

    // то же для скоростного режима (120/240 к/с): диапазон обязан быть из списка камеры для этого размера
    private fun hsRangeFor(f: Int): android.util.Range<Int>? {
        val rs = (try { streamMap?.getHighSpeedVideoFpsRangesFor(videoSize) } catch (_: Exception) { null }) ?: return null
        return rs.firstOrNull { it.lower == f && it.upper == f }
            ?: rs.filter { it.upper == f }.maxByOrNull { it.lower }
    }

    // какие частоты потянут камера (диапазон и длительность кадра для текущего размера) и кодер
    private fun refreshFpsOptions() {
        val map = streamMap
        val mime = if (useHevc) "video/hevc" else "video/avc"
        hsSizes = try {
            map?.highSpeedVideoSizes?.map { it.toString() }?.toSet() ?: emptySet()
        } catch (_: Exception) { emptySet() }
        val list = ArrayList<Int>()
        for (f in fpsChoices) {
            if (f > 60) {
                if (!hsSizes.contains(videoSize.toString()) || hsRangeFor(f) == null) continue
            } else {
                if (fpsRangeFor(f) == null) continue
                try {
                    val minDur = map?.getOutputMinFrameDuration(MediaRecorder::class.java, videoSize) ?: 0L
                    if (minDur > 0L && minDur > 1_000_000_000L / f * 1.03) continue
                } catch (_: Exception) {}
            }
            var codecOk = true
            try {
                codecOk = MediaCodecList(MediaCodecList.REGULAR_CODECS).codecInfos.any { ci ->
                    ci.isEncoder && ci.supportedTypes.contains(mime) &&
                        ci.getCapabilitiesForType(mime).videoCapabilities
                            .areSizeAndRateSupported(videoSize.width, videoSize.height, f.toDouble())
                }
            } catch (_: Exception) {}
            if (codecOk) list.add(f)
        }
        if (list.isEmpty()) list.add(30)
        fpsAvail = list
        log("Частоты видео для " + videoSize + ": " + list.joinToString(", ") + " к/с" +
            (if (hsSizes.isNotEmpty()) " (скоростной режим: " + hsSizes.joinToString(", ") + ")" else ""))
    }

    // что реально можно выбрать сейчас: скоростные частоты только с постоянной поверхностью записи
    private fun fpsOptions(): List<Int> =
        fpsAvail.filter { it <= 60 || (usePersistent && !hsDisabled) }

    private fun effectiveFps(): Int {
        val av = fpsOptions()
        if (av.isEmpty()) return 30
        if (av.contains(vFps)) return vFps
        return av.lastOrNull { it <= vFps } ?: av.first()
    }

    private fun isHsMode(): Boolean =
        mode == 1 && usePersistent && !hsDisabled && effectiveFps() > 60 && hsSizes.contains(videoSize.toString())

    // частота, с которой реально работает текущая сессия
    private fun activeFps(): Int = if (hsActive) effectiveFps() else min(effectiveFps(), 60)

    // в скоростной сессии камера принимает мало параметров: зум, автоэкспозиция, непрерывный автофокус, диапазон FPS
    private fun applyHsControls(b: CaptureRequest.Builder) {
        applyZoom(b)
        b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_ON)
        val fr = hsRangeFor(effectiveFps())
        if (fr != null) b.set(CaptureRequest.CONTROL_AE_TARGET_FPS_RANGE, fr)
        val afModes = chars?.get(CameraCharacteristics.CONTROL_AF_AVAILABLE_MODES)
        if (afModes != null && afModes.contains(CameraMetadata.CONTROL_AF_MODE_CONTINUOUS_VIDEO)) {
            b.set(CaptureRequest.CONTROL_AF_MODE, CameraMetadata.CONTROL_AF_MODE_CONTINUOUS_VIDEO)
        }
    }

    private fun setRepeatingAny(s: CameraCaptureSession, b: CaptureRequest.Builder) {
        if (s is CameraConstrainedHighSpeedCaptureSession) {
            val list = s.createHighSpeedRequestList(b.build())
            s.setRepeatingBurst(list, null, handler)
        } else {
            s.setRepeatingRequest(b.build(), null, handler)
        }
    }

    private fun fpsLabel(): String = "Кадры: " + effectiveFps() + " к/с"

    private fun resLabel(): String =
        "Разрешение: " + (if (resIdx == 0) "Макс " else "Норм ") + videoSize.width + "x" + videoSize.height

    // перезапуск сессии под новые параметры (формат, разрешение, режим), чтобы запись потом стартовала без перенастройки
    private fun restartSession() {
        usePersistent = (mode == 1)
        if (device != null) {
            try { session?.close() } catch (_: Exception) {}
            session = null
            computeSizes()
            startPreview()
        } else {
            computeSizes()
        }
    }

    private fun toggleResolution() {
        if (recording || stacking || tlRunning) { log("Сначала остановите запись, долгую выдержку или таймлапс"); return }
        resIdx = 1 - resIdx
        savePrefs()
        restartSession()
    }

    private fun displayDegrees(): Int {
        val rotation = windowManager.defaultDisplay.rotation
        val deg = when (rotation) {
            Surface.ROTATION_90 -> 90
            Surface.ROTATION_180 -> 180
            Surface.ROTATION_270 -> 270
            else -> 0
        }
        // приложение всегда альбомное, но после возврата из галереи система может ещё сообщать
        // портретный поворот. Ориентируемся на форму окна, а при неверном значении берём
        // последний известный альбомный поворот (90 или 270), а не фиксированные 90
        val vw = texture.width
        val vh = texture.height
        if (vw > vh) {
            if (deg == 90 || deg == 270) {
                lastLandscapeDeg = deg
                return deg
            }
            return lastLandscapeDeg
        }
        if (vh > vw && (deg == 90 || deg == 270)) return 0
        return deg
    }

    private fun transformKey(): String =
        texture.width.toString() + "x" + texture.height + "/" + displayDegrees() + "/" + previewSize

    private val displayListener = object : DisplayManager.DisplayListener {
        override fun onDisplayAdded(displayId: Int) {}
        override fun onDisplayRemoved(displayId: Int) {}
        override fun onDisplayChanged(displayId: Int) {
            updateTransform()
        }
    }

    // Поворот для файлов (видео и фото) с учётом ориентации экрана и переворота 180°
    private fun outputRotation(): Int {
        val so = chars?.get(CameraCharacteristics.SENSOR_ORIENTATION) ?: 90
        val base = (so - displayDegrees() + 360) % 360
        return (base + (if (cbFlip.isChecked) 180 else 0)) % 360
    }

    private fun updateTransform() {
        runOnUiThread {
            val vw = texture.width.toFloat()
            val vh = texture.height.toFloat()
            if (vw > 0f && vh > 0f) {
                val pw = previewSize.width.toFloat()
                val ph = previewSize.height.toFloat()
                val cx = vw / 2f
                val cy = vh / 2f
                val m = Matrix()
                val deg = displayDegrees()
                val key = transformKey()
                if (key != appliedTransformKey) {
                    appliedTransformKey = key
                    log("Экран: " + vw.toInt() + "x" + vh.toInt() + ", поворот экрана " + deg + "°")
                }
                if (deg == 90 || deg == 270) {
                    // TextureView показывает кадр как в портрете: снимаем растяжение,
                    // вписываем в экран и поворачиваем в альбомную ориентацию
                    val viewRect = RectF(0f, 0f, vw, vh)
                    val bufRect = RectF(0f, 0f, ph, pw)
                    bufRect.offset(cx - bufRect.centerX(), cy - bufRect.centerY())
                    m.setRectToRect(viewRect, bufRect, Matrix.ScaleToFit.FILL)
                    val scale = min(vh / ph, vw / pw)
                    m.postScale(scale, scale, cx, cy)
                    m.postRotate(if (deg == 90) -90f else 90f, cx, cy)
                } else if (deg == 180) {
                    m.postRotate(180f, cx, cy)
                }
                texture.setTransform(m)
            }
        }
    }

    private fun makeReader() {
        try { imageReader?.close() } catch (_: Exception) {}
        val reader = ImageReader.newInstance(photoSize.width, photoSize.height, ImageFormat.JPEG, 2)
        reader.setOnImageAvailableListener({ r ->
            val img = r.acquireLatestImage()
            if (img != null) {
                try {
                    val buf = img.planes[0].buffer
                    val bytes = ByteArray(buf.remaining())
                    buf.get(bytes)
                    savePhoto(bytes, -1, pendingInfo, pendingExpSec, pendingIso, pendingDist, pendingTag)
                } finally {
                    img.close()
                }
            }
        }, handler)
        imageReader = reader
    }

    private fun toggleAspect() {
        if (recording || stacking || tlRunning) { log("Сначала остановите запись, долгую выдержку или таймлапс"); return }
        aspectMode = (aspectMode + 1) % 3
        btnAspect.text = aspectLabel()
        savePrefs()
        updateModeUi()
        restartSession()
    }

    private fun tryAutoOpen() {
        if (device == null && !opening && texture.isAvailable &&
            checkSelfPermission(Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED
        ) {
            openById(cameraId)
        }
    }

    private fun openById(id: String) {
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
            log("Нет разрешения на камеру"); return
        }
        if (!texture.isAvailable) { log("Превью не готово, повторите"); return }
        if (recording) { log("Сначала остановите запись"); return }

        savePrefs()
        opening = true
        closeAll()
        log("--- Открываю ID $id ---")
        readCharacteristics(id)
        runOnUiThread { applyTicks() }

        try {

            cm.openCamera(id, object : CameraDevice.StateCallback() {
                override fun onOpened(camera: CameraDevice) {
                    log("ОТКРЫЛАСЬ: ID $id")
                    opening = false
                    device = camera
                    startPreview()
                }
                override fun onDisconnected(camera: CameraDevice) {
                    log("Отключена"); opening = false; device = null; camera.close()
                    if (tlRunning) finishTimelapse("камера отключилась", false)
                }
                override fun onError(camera: CameraDevice, error: Int) {
                    log("Ошибка камеры, код $error"); opening = false; device = null; camera.close()
                    if (tlRunning) finishTimelapse("ошибка камеры", false)
                }
            }, handler)
        } catch (e: Exception) {
            opening = false
            log("openCamera не удалось: $e")
        }
    }

    private fun updateModeUi() {
        val photo = mode == 0
        val vis = if (photo) View.VISIBLE else View.GONE
        val visVideo = if (photo) View.GONE else View.VISIBLE
        val tlVis = if (mode == 2) View.VISIBLE else View.GONE
        btnMode.text = when (mode) {
            0 -> "Режим: Фото"
            1 -> "Режим: Видео"
            else -> "Режим: Таймлапс"
        }
        btnTl.visibility = tlVis
        btnFps.visibility = if (mode == 1) View.VISIBLE else View.GONE
        tvTl.visibility = tlVis
        sbTl.visibility = tlVis
        cbTlLock.visibility = tlVis
        cbTlJpeg.visibility = tlVis
        btnPhoto.visibility = vis
        btnStack.visibility = vis
        tvStack.visibility = vis
        sbStack.visibility = vis
        cbStackSum.visibility = vis
        btnRec.visibility = if (mode == 1) View.VISIBLE else View.GONE
        btnRes.visibility = if (photo || aspectMode == 2) View.GONE else View.VISIBLE
        btnCodec.visibility = visVideo
        btnBitrate.visibility = visVideo
        updatePauseUi()
    }

    private fun updatePauseUi() {
        runOnUiThread {
            btnPause.visibility = if (recording) View.VISIBLE else View.GONE
            btnPause.text = if (paused) "Продолжить" else "Пауза"
        }
    }

    private fun togglePause() {
        val r = recorder
        if (!recording || r == null) { log("Запись не идёт"); return }
        try {
            if (paused) {
                r.resume()
                paused = false
                log("Запись продолжена")
            } else {
                r.pause()
                paused = true
                log("Пауза")
            }
        } catch (e: Exception) {
            log("Пауза недоступна: $e")
        }
        updatePauseUi()
    }

    // ---------- трансляция на планшет ----------

    private fun recentLog(): String = synchronized(logBuf) { logBuf.takeLast(8).joinToString("\n") }

    private fun esc(s: String): String =
        s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\r", " ").replace("\t", " ")

    private fun localIps(): List<String> {
        val res = ArrayList<String>()
        try {
            val en = java.net.NetworkInterface.getNetworkInterfaces()
            while (en.hasMoreElements()) {
                val ni = en.nextElement()
                if (!ni.isUp || ni.isLoopback) continue
                val ad = ni.inetAddresses
                while (ad.hasMoreElements()) {
                    val a = ad.nextElement()
                    if (a is java.net.Inet4Address && !a.isLoopbackAddress) {
                        res.add("http://" + a.hostAddress + ":8080")
                    }
                }
            }
        } catch (_: Exception) {
        }
        return res
    }

    private fun toggleServer() {
        if (serverOn) {
            stopServer()
            btnServer.text = "Трансляция: выкл"
            log("Трансляция выключена")
        } else {
            startServer()
        }
    }

    private fun startServer() {
        if (serverOn) return
        var p = prefs.getString("pin", null)
        if (p == null) {
            p = (1000 + java.util.Random().nextInt(9000)).toString()
            prefs.edit().putString("pin", p).apply()
        }
        pin = p
        try {
            val ss = ServerSocket(8080)
            serverSocket = ss
            serverOn = true
            Thread { acceptLoop(ss) }.start()
            Thread { producerLoop() }.start()
            btnServer.text = "Трансляция: вкл"
            val ips = localIps()
            val msg = (if (ips.isEmpty()) "Нет сети Wi-Fi или USB" else ips.joinToString("\n")) + "\n\nPIN: " + pin
            AlertDialog.Builder(this)
                .setTitle("Откройте на планшете")
                .setMessage(msg)
                .setPositiveButton("OK", null)
                .show()
            log("Трансляция: порт 8080, PIN $pin")
        } catch (e: Exception) {
            log("Сервер не запустился: $e")
        }
    }

    private fun stopServer() {
        serverOn = false
        try { serverSocket?.close() } catch (_: Exception) {}
        serverSocket = null
    }

    private fun acceptLoop(ss: ServerSocket) {
        while (serverOn) {
            try {
                val s = ss.accept()
                Thread { handleClient(s) }.start()
            } catch (e: Exception) {
                if (!serverOn) break
            }
        }
    }

    private fun writeHttp(out: OutputStream, code: Int, type: String, body: ByteArray) {
        val head = "HTTP/1.1 " + code + " " + (if (code == 200) "OK" else "Error") +
            "\r\nContent-Type: " + type +
            "\r\nContent-Length: " + body.size +
            "\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n"
        out.write(head.toByteArray(Charsets.ISO_8859_1))
        out.write(body)
        out.flush()
    }

    private fun handleClient(sock: Socket) {
        try {
            sock.soTimeout = 10000
            val input = BufferedReader(InputStreamReader(sock.getInputStream(), Charsets.ISO_8859_1))
            val first = input.readLine() ?: return
            while (true) {
                val l = input.readLine() ?: break
                if (l.isEmpty()) break
            }
            val parts = first.split(" ")
            if (parts.size < 2) return
            val target = parts[1]
            val qi = target.indexOf('?')
            val path = if (qi >= 0) target.substring(0, qi) else target
            val params = HashMap<String, String>()
            if (qi >= 0) {
                for (kv in target.substring(qi + 1).split("&")) {
                    val e = kv.indexOf('=')
                    if (e > 0) {
                        params[URLDecoder.decode(kv.substring(0, e), "UTF-8")] =
                            URLDecoder.decode(kv.substring(e + 1), "UTF-8")
                    }
                }
            }
            val out = sock.getOutputStream()
            if (path == "/") {
                writeHttp(out, 200, "text/html; charset=utf-8", WEB_PAGE.toByteArray(Charsets.UTF_8))
                return
            }
            if (params["pin"] != pin) {
                writeHttp(out, 403, "text/plain", "PIN".toByteArray())
                return
            }
            when (path) {
                "/state" -> writeHttp(out, 200, "application/json; charset=utf-8", stateJson().toByteArray(Charsets.UTF_8))
                "/cmd" -> {
                    handleCmd(params)
                    writeHttp(out, 200, "text/plain", "ok".toByteArray())
                }
                "/loupe" -> {
                    val rx = (params["x"]?.toFloatOrNull() ?: 0.5f).coerceIn(0f, 1f)
                    val ry = (params["y"]?.toFloatOrNull() ?: 0.5f).coerceIn(0f, 1f)
                    val bmp = grabLoupe(rx, ry)
                    if (bmp == null) {
                        writeHttp(out, 500, "text/plain", "no frame".toByteArray())
                    } else {
                        val bos = ByteArrayOutputStream()
                        bmp.compress(Bitmap.CompressFormat.JPEG, 92, bos)
                        bmp.recycle()
                        writeHttp(out, 200, "image/jpeg", bos.toByteArray())
                    }
                }
                "/stream" -> streamTo(sock, out)
                "/loupestream" -> {
                    val lx = (params["x"]?.toFloatOrNull() ?: 0.5f).coerceIn(0f, 1f)
                    val ly = (params["y"]?.toFloatOrNull() ?: 0.5f).coerceIn(0f, 1f)
                    loupeStreamTo(sock, out, lx, ly)
                }
                else -> writeHttp(out, 404, "text/plain", "404".toByteArray())
            }
        } catch (_: Exception) {
        } finally {
            try { sock.close() } catch (_: Exception) {}
        }
    }

    private fun streamTo(sock: Socket, out: OutputStream) {
        clients.incrementAndGet()
        try {
            out.write(
                ("HTTP/1.1 200 OK\r\nContent-Type: multipart/x-mixed-replace; boundary=frame\r\n" +
                    "Cache-Control: no-store\r\nConnection: close\r\n\r\n").toByteArray()
            )
            var seen = -1L
            while (serverOn && !sock.isClosed) {
                val j = latestJpeg
                if (j != null && frameSeq != seen) {
                    seen = frameSeq
                    out.write(("--frame\r\nContent-Type: image/jpeg\r\nContent-Length: " + j.size + "\r\n\r\n").toByteArray())
                    out.write(j)
                    out.write("\r\n".toByteArray())
                    out.flush()
                } else {
                    Thread.sleep(15)
                }
            }
        } finally {
            clients.decrementAndGet()
        }
    }

    private fun loupeStreamTo(sock: Socket, out: OutputStream, rx: Float, ry: Float) {
        out.write(
            ("HTTP/1.1 200 OK\r\nContent-Type: multipart/x-mixed-replace; boundary=frame\r\n" +
                "Cache-Control: no-store\r\nConnection: close\r\n\r\n").toByteArray()
        )
        while (serverOn && !sock.isClosed) {
            val t0 = System.currentTimeMillis()
            val bmp = grabLoupe(rx, ry)
            if (bmp != null) {
                val bos = ByteArrayOutputStream(150_000)
                bmp.compress(Bitmap.CompressFormat.JPEG, 88, bos)
                bmp.recycle()
                val j = bos.toByteArray()
                out.write(("--frame\r\nContent-Type: image/jpeg\r\nContent-Length: " + j.size + "\r\n\r\n").toByteArray())
                out.write(j)
                out.write("\r\n".toByteArray())
                out.flush()
            }
            val dt = System.currentTimeMillis() - t0
            if (dt < 120) Thread.sleep(120 - dt)
        }
    }

    private fun producerLoop() {
        while (serverOn) {
            try {
                if (clients.get() > 0) {
                    val t0 = System.currentTimeMillis()
                    val bmp = grabStream()
                    if (bmp != null) {
                        val bos = ByteArrayOutputStream(200_000)
                        bmp.compress(Bitmap.CompressFormat.JPEG, 80, bos)
                        bmp.recycle()
                        latestJpeg = bos.toByteArray()
                        frameSeq++
                    }
                    val dt = System.currentTimeMillis() - t0
                    if (dt < 80) Thread.sleep(80 - dt)
                } else {
                    Thread.sleep(100)
                }
            } catch (_: Throwable) {
                try { Thread.sleep(200) } catch (_: Throwable) {}
            }
        }
    }

    private fun grabStream(): Bitmap? {
        val latch = CountDownLatch(1)
        var res: Bitmap? = null
        runOnUiThread {
            try {
                res = uiCaptureStream()
            } catch (_: Throwable) {
            } finally {
                latch.countDown()
            }
        }
        latch.await(800, TimeUnit.MILLISECONDS)
        return res
    }

    private fun grabLoupe(rx: Float, ry: Float): Bitmap? {
        val latch = CountDownLatch(1)
        var res: Bitmap? = null
        runOnUiThread {
            try {
                res = uiCaptureLoupe(rx, ry)
            } catch (_: Throwable) {
            } finally {
                latch.countDown()
            }
        }
        latch.await(3000, TimeUnit.MILLISECONDS)
        return res
    }

    // размер изображения внутри вида (без чёрных полей) в пикселях вида
    private fun imageRectSize(): FloatArray? {
        val vw = texture.width
        val vh = texture.height
        if (vw == 0 || vh == 0) return null
        val ca = previewSize.width.toFloat() / previewSize.height
        val va = vw.toFloat() / vh
        return if (va > ca) floatArrayOf(vh * ca, vh.toFloat()) else floatArrayOf(vw.toFloat(), vw / ca)
    }

    private fun uiCaptureStream(): Bitmap? {
        if (!texture.isAvailable) return null
        val pw = previewSize.width
        val ph = previewSize.height
        val srcW = 900
        val srcH = max(2, srcW * pw / ph)
        var sb = streamBmp
        if (sb == null || sb.width != srcW || sb.height != srcH) {
            sb = Bitmap.createBitmap(srcW, srcH, Bitmap.Config.ARGB_8888)
            streamBmp = sb
        }
        texture.getBitmap(sb)
        val m = Matrix()
        val rot = displayDegrees()
        if (rot == 90) m.postRotate(-90f) else if (rot == 270) m.postRotate(90f)
        return Bitmap.createBitmap(sb, 0, 0, srcW, srcH, m, false)
    }

    private fun uiCaptureLoupe(rx: Float, ry: Float): Bitmap? {
        if (!texture.isAvailable) return null
        val lw = previewSize.width
        val lh = previewSize.height
        val wp = lh
        val hp = lw
        var full = loupeBmp
        if (full == null || full.width != wp || full.height != hp) {
            full = try { Bitmap.createBitmap(wp, hp, Bitmap.Config.ARGB_8888) } catch (e: OutOfMemoryError) { null }
            loupeBmp = full
        }
        if (full == null) return null
        texture.getBitmap(full)
        val cw = min(800, lw)
        val ch = min(600, lh)
        val cx = (rx * lw - cw / 2f).toInt().coerceIn(0, lw - cw)
        val cy = (ry * lh - ch / 2f).toInt().coerceIn(0, lh - ch)
        val m = Matrix()
        val crop: Bitmap
        if (displayDegrees() == 270) {
            crop = Bitmap.createBitmap(full, cy, hp - (cx + cw), ch, cw)
            m.postRotate(90f)
        } else {
            crop = Bitmap.createBitmap(full, wp - (cy + ch), cx, ch, cw)
            m.postRotate(-90f)
        }
        val out = Bitmap.createBitmap(crop, 0, 0, crop.width, crop.height, m, false)
        crop.recycle()
        return out
    }

    private fun stateJson(): String {
        val sb = StringBuilder("{")
        fun s(k: String, v: String) { sb.append("\"").append(k).append("\":\"").append(esc(v)).append("\",") }
        fun n(k: String, v: Int) { sb.append("\"").append(k).append("\":").append(v).append(",") }
        fun b(k: String, v: Boolean) { sb.append("\"").append(k).append("\":").append(if (v) "true" else "false").append(",") }
        n("mode", mode)
        b("rec", recording)
        s("modeBtn", btnMode.text.toString())
        s("recBtn", btnRec.text.toString())
        s("pauseBtn", btnPause.text.toString())
        s("stackBtn", btnStack.text.toString())
        n("zoom", sbZoom.progress)
        n("iso", sbIso.progress)
        n("exp", sbExp.progress)
        n("focus", sbFocus.progress)
        n("boost", sbBoost.progress)
        n("stack", sbStack.progress)
        s("zoomLabel", tvZoom.text.toString())
        s("isoLabel", tvIso.text.toString())
        s("expLabel", tvExp.text.toString())
        s("focusLabel", tvFocus.text.toString())
        s("stackLabel", tvStack.text.toString())
        s("boostLabel", tvBoost.text.toString())
        b("boostOn", tvBoost.visibility == View.VISIBLE)
        b("manExp", cbExp.isChecked)
        b("manFocus", cbFocus.isChecked)
        b("flip", cbFlip.isChecked)
        b("stackSum", cbStackSum.isChecked)
        s("aspect", btnAspect.text.toString())
        s("stab", btnStab.text.toString())
        s("nr", btnNr.text.toString())
        s("edge", btnEdge.text.toString())
        s("bitrate", btnBitrate.text.toString())
        s("torch", btnTorch.text.toString())
        s("cam", btnCam.text.toString())
        sb.append("\"log\":\"").append(esc(recentLog())).append("\"}")
        return sb.toString()
    }

    private fun handleCmd(p: Map<String, String>) {
        val c = p["c"] ?: return
        val n = p["n"] ?: ""
        val v = p["v"] ?: ""
        runOnUiThread { applyCmd(c, n, v) }
    }

    private fun applyCmd(c: String, n: String, v: String) {
        try {
                when (c) {
                    "click" -> {
                        when (n) {
                            "mode" -> btnMode.performClick()
                            "photo" -> btnPhoto.performClick()
                            "rec" -> btnRec.performClick()
                            "pause" -> btnPause.performClick()
                            "stack" -> btnStack.performClick()
                            "aspect" -> btnAspect.performClick()
                            "stab" -> btnStab.performClick()
                            "nr" -> btnNr.performClick()
                            "edge" -> btnEdge.performClick()
                            "bitrate" -> btnBitrate.performClick()
                            "torch" -> btnTorch.performClick()
                            "cam" -> btnCam.performClick()
                            else -> {}
                        }
                    }
                    "set" -> {
                        val value = (v.toIntOrNull() ?: 0).coerceIn(0, 1000)
                        when (n) {
                            "zoom" -> sbZoom.progress = value
                            "iso" -> sbIso.progress = value
                            "exp" -> sbExp.progress = value
                            "focus" -> sbFocus.progress = value
                            "boost" -> sbBoost.progress = value
                            "stack" -> sbStack.progress = value
                            else -> {}
                        }
                        updateLabels()
                        savePrefs()
                        updateRepeating()
                    }
                    "check" -> {
                        val on = v == "1"
                        when (n) {
                            "manExp" -> cbExp.isChecked = on
                            "manFocus" -> cbFocus.isChecked = on
                            "flip" -> cbFlip.isChecked = on
                            "stackSum" -> cbStackSum.isChecked = on
                            else -> {}
                        }
                    }
                    else -> {}
                }
        } catch (e: Exception) {
            log("Команда с планшета: $e")
        }
    }

    // ---------- галерея, фонарик, экономия ----------

    private fun rememberLast(uri: Uri, mime: String) {
        lastMediaUri = uri
        lastMediaMime = mime
        prefs.edit().putString("lastUri", uri.toString()).putString("lastMime", mime).apply()
    }

    // Файл можно открыть, только если он ещё есть и приложение имеет к нему доступ
    private fun mediaAccessible(u: Uri): Boolean = mediaSize(u) > 0

    // Самый новый файл из Movies/MacroCam и Pictures/MacroCam, к которому есть доступ
    private fun newestOwnMedia(): Pair<Uri, String>? {
        var best: Pair<Uri, String>? = null
        var bestDate = -1L
        val sources = listOf(
            MediaStore.Video.Media.EXTERNAL_CONTENT_URI to "video/mp4",
            MediaStore.Images.Media.EXTERNAL_CONTENT_URI to "image/jpeg"
        )
        for ((base, mime) in sources) {
            try {
                contentResolver.query(
                    base,
                    arrayOf(MediaStore.MediaColumns._ID, MediaStore.MediaColumns.DATE_ADDED),
                    MediaStore.MediaColumns.RELATIVE_PATH + " LIKE ?",
                    arrayOf("%MacroCam%"),
                    MediaStore.MediaColumns.DATE_ADDED + " DESC"
                )?.use { c ->
                    var tries = 0
                    while (c.moveToNext() && tries < 5) {
                        tries++
                        val uri = android.content.ContentUris.withAppendedId(base, c.getLong(0))
                        if (mediaAccessible(uri)) {
                            val d = c.getLong(1)
                            if (d > bestDate) { bestDate = d; best = Pair(uri, mime) }
                            break
                        }
                    }
                }
            } catch (e: Exception) {
                log("Поиск последнего файла: $e")
            }
        }
        return best
    }

    // Запасной вариант: просто открыть приложение «Галерея»
    private fun openGalleryApp() {
        try {
            startActivity(Intent.makeMainSelectorActivity(Intent.ACTION_MAIN, Intent.CATEGORY_APP_GALLERY))
        } catch (e: Exception) {
            try {
                val i = Intent(Intent.ACTION_VIEW)
                i.setDataAndType(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, "image/*")
                startActivity(i)
            } catch (e2: Exception) {
                log("Галерея не открылась: $e2")
            }
        }
    }

    private fun openGallery() {
        if (recording || stacking || tlRunning) { log("Сначала остановите запись, долгую выдержку или таймлапс"); return }
        var u = lastMediaUri ?: prefs.getString("lastUri", null)?.let { Uri.parse(it) }
        var mime = lastMediaMime ?: prefs.getString("lastMime", null)
        if (u != null && !mediaAccessible(u)) {
            // файл удалён или принадлежит прежней установке приложения: открытие дало бы SecurityException
            log("Последний файл недоступен (удалён или нет прав), ищу другой")
            lastMediaUri = null
            lastMediaMime = null
            prefs.edit().remove("lastUri").remove("lastMime").apply()
            val alt = newestOwnMedia()
            u = alt?.first
            mime = alt?.second
            if (u == null) log("Своих файлов в галерее не найдено, открываю саму галерею")
        }
        if (u == null) { openGalleryApp(); return }
        try {
            val i = Intent(Intent.ACTION_VIEW)
            i.setDataAndType(u, mime ?: "*/*")
            i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
            startActivity(i)
        } catch (e: Exception) {
            log("Не удалось открыть файл в галерее: $e")
            openGalleryApp()
        }
    }

    private fun findTorchId(): String? {
        try {
            for (id in cm.cameraIdList) {
                val c = cm.getCameraCharacteristics(id)
                if (c.get(CameraCharacteristics.FLASH_INFO_AVAILABLE) == true &&
                    c.get(CameraCharacteristics.LENS_FACING) == CameraCharacteristics.LENS_FACING_BACK
                ) return id
            }
        } catch (e: Exception) {
            log("Поиск вспышки: $e")
        }
        return null
    }

    private fun camLabel(id: String): String = when (id) {
        "3" -> "Макро (3)"
        "0" -> "Основная (0)"
        "4" -> "Сверхширокая (4)"
        else -> id
    }

    private fun switchCamera() {
        if (recording || stacking || tlRunning) { log("Сначала остановите запись, долгую выдержку или таймлапс"); return }
        val i = camIds.indexOf(cameraId)
        cameraId = camIds[(i + 1) % camIds.size]
        btnCam.text = "Камера: " + camLabel(cameraId)
        savePrefs()
        log("Переключаю на камеру: " + camLabel(cameraId))
        closeAll()
        btnCam.postDelayed({ tryAutoOpen() }, 400)
    }

    private fun toggleTorch() {
        if (device != null) {
            // камера открыта: система не даёт включить фонарик отдельно (CAMERA_IN_USE),
            // поэтому включаем его запросом самой камеры
            torchOn = !torchOn
            btnTorch.text = if (torchOn) "Фонарик: вкл" else "Фонарик: выкл"
            if (torchOn && chars?.get(CameraCharacteristics.FLASH_INFO_AVAILABLE) != true) {
                log("Эта камера сообщает, что у неё нет вспышки, фонарик может не загореться (попробуйте основную камеру)")
            }
            updateRepeating()
            return
        }
        var id = torchId
        if (id == null) {
            id = findTorchId()
            torchId = id
        }
        if (id == null) { log("Вспышка не найдена"); return }
        try {
            cm.setTorchMode(id, !torchOn)
            torchOn = !torchOn
            btnTorch.text = if (torchOn) "Фонарик: вкл" else "Фонарик: выкл"
        } catch (e: Exception) {
            log("Фонарик не включился: $e")
        }
    }

    private fun setSaveMode(on: Boolean) {
        saveMode = on
        saveOverlay.visibility = if (on) View.VISIBLE else View.GONE
        val lp = window.attributes
        lp.screenBrightness = if (on) 0.01f else WindowManager.LayoutParams.BRIGHTNESS_OVERRIDE_NONE
        window.attributes = lp
        log(if (on) "Экономия включена" else "Экономия выключена")
    }

    override fun onBackPressed() {
        if (saveMode) setSaveMode(false) else super.onBackPressed()
    }

    private fun toggleMode() {
        if (recording || stacking || tlRunning) { log("Сначала остановите запись, долгую выдержку или таймлапс"); return }
        if (rampActive) { log("Подождите, линза встаёт на место"); return }
        mode = (mode + 1) % 3
        savePrefs()
        updateModeUi()
        restartSession()
    }

    // Плавный возврат линзы: после пересоздания сессии камера уезжает на бесконечность,
    // поэтому ручной фокус возвращаем плавно (около 1,2 с), затем ждём, пока линза успокоится
    private fun startFocusRamp(onDone: () -> Unit) {
        rampToken++
        val tok = rampToken
        if (!cbFocus.isChecked || minFocus <= 0f) {
            focusOverride = null
            rampActive = false
            onDone()
            return
        }
        rampActive = true
        val t0 = System.currentTimeMillis()
        val dur = 1200L
        val step = object : Runnable {
            override fun run() {
                if (tok != rampToken) return
                val t = ((System.currentTimeMillis() - t0).toFloat() / dur).coerceIn(0f, 1f)
                val e = t * t * (3f - 2f * t)
                focusOverride = currentFocus() * e
                updateRepeating()
                if (t < 1f) {
                    handler.postDelayed(this, 40)
                } else {
                    focusOverride = null
                    updateRepeating()
                    handler.postDelayed({
                        if (tok == rampToken) {
                            rampActive = false
                            onDone()
                        }
                    }, 600)
                }
            }
        }
        handler.post(step)
    }

    private fun createPersistentSurface(): Surface? {
        try { persistentSurface?.release() } catch (_: Exception) {}
        persistentSurface = null
        val cands = if (videoCandidates.isEmpty()) listOf(videoSize) else videoCandidates.take(4)
        for (sz in cands) {
            val tmp = File(cacheDir, "tmp_rec.mp4")
            var surf: Surface? = null
            val t = MediaRecorder()
            try {
                surf = MediaCodec.createPersistentInputSurface()
                t.setVideoSource(MediaRecorder.VideoSource.SURFACE)
                t.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
                t.setOutputFile(tmp.absolutePath)
                t.setVideoEncoder(videoEncoderType())
                t.setVideoEncodingBitRate(10_000_000)
                t.setVideoFrameRate(30)
                t.setVideoSize(sz.width, sz.height)
                t.setInputSurface(surf)
                t.prepare()
                t.release()
                tmp.delete()
                videoSize = sz
                persistentSurface = surf
                return surf
            } catch (e: Exception) {
                log("Видео " + sz.width + "x" + sz.height + " не подошло: " + e)
                try { t.reset() } catch (_: Exception) {}
                try { t.release() } catch (_: Exception) {}
                try { surf?.release() } catch (_: Exception) {}
            }
        }
        return null
    }

    private fun startPreview() {
        val cam = device ?: return
        try {
            try { session?.close() } catch (_: Exception) {}
            session = null
            sessionHasRecorder = false
            hsActive = false
            var ps: Surface? = null
            if (usePersistent) ps = createPersistentSurface()
            // 120/240 к/с: скоростная сессия (только превью и запись, размер превью = размеру видео)
            val hsNow = ps != null && isHsMode()
            hsActive = hsNow
            val st = texture.surfaceTexture!!
            val bufSize = if (hsNow) videoSize else previewSize
            st.setDefaultBufferSize(bufSize.width, bufSize.height)
            val surface = Surface(st)
            previewSurface = surface
            startedViewW = texture.width
            startedViewH = texture.height
            focusOverride = if (cbFocus.isChecked && minFocus > 0f) 0f else null
            val b = cam.createCaptureRequest(if (hsNow) CameraDevice.TEMPLATE_RECORD else CameraDevice.TEMPLATE_PREVIEW)
            b.addTarget(surface)
            applyControls(b, false)
            builder = b
            previewBuilder = b
            val targets = ArrayList<Surface>()
            targets.add(surface)
            if (ps != null) targets.add(ps)
            val hasRec = ps != null
            val cb = object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    sessionHasRecorder = hasRec
                    try {
                        if (!previewOff) setRepeatingAny(s, b)
                    } catch (e: Exception) {
                        log("Ошибка запроса: $e")
                    }
                    startFocusRamp { }
                }
                override fun onConfigureFailed(s: CameraCaptureSession) {
                    if (hsNow) {
                        log("Скоростной режим " + effectiveFps() + " к/с не настроился, возвращаю обычный")
                        hsDisabled = true
                        hsActive = false
                        runOnUiThread { btnFps.text = fpsLabel() }
                        startPreview()
                    } else if (hasRec) {
                        log("Сессия с видео не настроилась, запись будет с перенастройкой камеры")
                        usePersistent = false
                        try { persistentSurface?.release() } catch (_: Exception) {}
                        persistentSurface = null
                        startPreview()
                    } else {
                        log("Сессия не настроилась")
                    }
                }
            }
            if (hsNow) {
                log("Скоростной режим " + effectiveFps() + " к/с, " + videoSize +
                    (if (cbExp.isChecked) ": ручные ISO и выдержка здесь не работают, камера в авто" else ""))
                cam.createConstrainedHighSpeedCaptureSession(targets, cb, handler)
            } else {
                createSessionWithParams(cam, targets, b.build(), cb)
            }
        } catch (e: Exception) {
            log("Ошибка превью: $e")
        }
    }

    // ---------- фото ----------

    // Кадр берётся из превью (полное разрешение выбранного формата), JPEG качества 100 делает приложение
    private fun uiCapturePhoto(): Bitmap? {
        if (!texture.isAvailable) return null
        val lw = previewSize.width
        val lh = previewSize.height
        val full: Bitmap = (try { texture.getBitmap(lh, lw) } catch (e: OutOfMemoryError) { null }) ?: return null
        var deg = when (displayDegrees()) {
            90 -> -90f
            270 -> 90f
            else -> 0f
        }
        if (cbFlip.isChecked) deg += 180f
        if (deg % 360f == 0f) return full
        val m = Matrix()
        m.postRotate(deg)
        val out = Bitmap.createBitmap(full, 0, 0, full.width, full.height, m, false)
        if (out !== full) full.recycle()
        return out
    }

    private fun takePhoto() {
        if (device == null || session == null) { log("Сначала откройте камеру"); return }
        if (recording) { log("Во время записи фото недоступно"); return }
        if (tlRunning) { log("Во время таймлапса фото недоступно"); return }
        if (stacking) { log("Идёт долгая выдержка"); return }
        if (previewOff) { log("Фото берётся из превью: включите превью и дождитесь кадра"); return }
        if (rampActive) { log("Подождите, линза встаёт на место"); return }
        val info = shotInfo()
        val tag = fileTag()
        val expSec: Double? = if (cbExp.isChecked) currentExp() / 1e9 else null
        val iso: Int? = if (cbExp.isChecked) currentIso() else null
        val fNow = currentFocus()
        val dist: Double? = if (cbFocus.isChecked && fNow > 0.01f) 1.0 / fNow else null
        val bmp = try { uiCapturePhoto() } catch (e: Throwable) { null }
        if (bmp == null) { log("Кадр недоступен"); return }
        val w = bmp.width
        val h = bmp.height
        Thread {
            try {
                val bos = ByteArrayOutputStream(4_000_000)
                bmp.compress(Bitmap.CompressFormat.JPEG, 100, bos)
                bmp.recycle()
                savePhoto(bos.toByteArray(), -1, info, expSec, iso, dist, tag)
                log("Фото " + w + "x" + h + ", качество JPEG 100")
            } catch (e: Throwable) {
                log("Ошибка фото: $e")
            }
        }.start()
    }

    private fun savePhoto(
        bytes: ByteArray,
        rotation: Int = -1,
        info: String? = null,
        expSec: Double? = null,
        iso: Int? = null,
        distM: Double? = null,
        tag: String? = null,
        subDir: String? = null,
        quiet: Boolean = false
    ) {
        var created: Uri? = null
        try {
            val name = "macro_" + stamp() + (if (tag != null) "_$tag" else "")
            val values = ContentValues().apply {
                put(MediaStore.Images.Media.DISPLAY_NAME, "$name.jpg")
                put(MediaStore.Images.Media.MIME_TYPE, "image/jpeg")
                put(MediaStore.Images.Media.RELATIVE_PATH, "Pictures/MacroCam" + (if (subDir != null) "/" + subDir else ""))
                put(MediaStore.Images.Media.IS_PENDING, 1)
            }
            val uri = contentResolver.insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, values)
            if (uri == null) { log("Не удалось создать файл фото"); return }
            created = uri
            val os = contentResolver.openOutputStream(uri)
            if (os == null) throw java.io.IOException("не удалось открыть файл для записи")
            os.use { it.write(bytes) }
            // ошибка записи метаданных не должна терять сам снимок
            try {
            if (rotation >= 0 || info != null) {
                val rw = contentResolver.openFileDescriptor(uri, "rw")
                if (rw != null) {
                    rw.use {
                        val exif = ExifInterface(it.fileDescriptor)
                        if (rotation >= 0) {
                            val o = when (rotation) {
                                90 -> ExifInterface.ORIENTATION_ROTATE_90
                                180 -> ExifInterface.ORIENTATION_ROTATE_180
                                270 -> ExifInterface.ORIENTATION_ROTATE_270
                                else -> ExifInterface.ORIENTATION_NORMAL
                            }
                            exif.setAttribute(ExifInterface.TAG_ORIENTATION, o.toString())
                        }
                        if (info != null) {
                            exif.setAttribute(ExifInterface.TAG_USER_COMMENT, info)
                            exif.setAttribute(ExifInterface.TAG_IMAGE_DESCRIPTION, info)
                        }
                        if (expSec != null) {
                            exif.setAttribute(ExifInterface.TAG_EXPOSURE_TIME, String.format(Locale.US, "%.6f", expSec))
                        }
                        if (iso != null) {
                            exif.setAttribute("ISOSpeedRatings", iso.toString())
                        }
                        if (distM != null) {
                            exif.setAttribute(ExifInterface.TAG_SUBJECT_DISTANCE, String.format(Locale.US, "%.4f", distM))
                        }
                        exif.saveAttributes()
                    }
                }
            }
            } catch (e: Exception) {
                log("Фото: метаданные не записаны: $e")
            }
            val done = ContentValues()
            done.put(MediaStore.Images.Media.IS_PENDING, 0)
            contentResolver.update(uri, done, null, null)
            if (!quiet) {
                val desc = describeMedia(uri)
                if (desc == null) {
                    log("Фото НЕ найдено в галерее после сохранения (запись о файле пропала)")
                } else {
                    rememberLast(uri, "image/jpeg")
                    log("Фото сохранено: Pictures/MacroCam/$desc")
                }
            }
        } catch (e: Exception) {
            log("Фото НЕ сохранено: $e")
            val c = created
            if (c != null) {
                try { contentResolver.delete(c, null, null) } catch (_: Exception) {}
            }
        }
    }

    // ---------- долгая выдержка (наложение кадров) ----------

    private fun cleanupStack() {
        try { session?.close() } catch (_: Exception) {}
        session = null
        try { stackReader?.close() } catch (_: Exception) {}
        stackReader = null
        stackSurface = null
        sessionHasRecorder = false
        yAcc = null
        uAcc = null
        vAcc = null
        runOnUiThread { btnStack.text = "Выдержка" }
    }

    private fun stackFrameNs(i: Int): Long =
        if (i >= stackTarget - 1) stackTotalNs - (stackTarget - 1) * stackMaxFrameNs else stackMaxFrameNs

    private fun startStack() {
        if (stacking) {
            stackCancel = true
            log("Останавливаю, обработаю уже снятые кадры...")
            if (stackCount == 0) handler.post { if (stacking && stackCount == 0) finishStack() }
            return
        }
        val cam = device
        if (cam == null) { log("Сначала откройте камеру"); return }
        if (recording) { log("Остановите запись"); return }
        if (tlRunning) { log("Идёт таймлапс"); return }
        clearPreviewOff()
        if (rampActive) { log("Подождите, линза встаёт на место"); return }
        if (!cbExp.isChecked || isoRange == null || expRange == null) {
            log("Включите «Ручные ISO и выдержка»: ISO берётся оттуда, выдержка — с ползунка «Долгая выдержка»")
            return
        }
        // Долгая выдержка по ползунку «Долгая выдержка» (ползунок «Выдержка» вверху на неё не влияет).
        // До 30 с: один кадр. Больше: кадры по 30 с и последний кадр с остатком времени; потом всё складывается.
        val totalNs = (sbStack.progress + 2) * 1_000_000_000L
        var n = ((totalNs + stackMaxFrameNs - 1) / stackMaxFrameNs).toInt()
        if (n < 1) n = 1
        val exp = min(totalNs, stackMaxFrameNs)
        stackTotalNs = totalNs
        stackW = photoSize.width
        stackH = photoSize.height
        try {
            yAcc = IntArray(stackW * stackH)
            uAcc = IntArray((stackW / 2) * (stackH / 2))
            vAcc = IntArray((stackW / 2) * (stackH / 2))
        } catch (e: OutOfMemoryError) {
            yAcc = null; uAcc = null; vAcc = null
            log("Не хватает памяти")
            return
        }
        stackTarget = n
        stackFrameExpNs = exp
        stackCount = 0
        stackSubmitted = 0
        stackLogged = 0
        stackCancel = false
        stackSum = n > 1 // один кадр копится как есть, несколько кадров складываются как свет
        try {
            val reader = ImageReader.newInstance(stackW, stackH, ImageFormat.YUV_420_888, 4)
            reader.setOnImageAvailableListener({ r -> onStackImage(r) }, handler)
            stackReader = reader
            stacking = true
            runOnUiThread { btnStack.text = "Стоп 0/" + (stackTotalNs / 1_000_000_000L) + " с" }

            try { session?.close() } catch (_: Exception) {}
            session = null
            val st = texture.surfaceTexture!!
            st.setDefaultBufferSize(previewSize.width, previewSize.height)
            val pSurface = Surface(st)
            stackSurface = pSurface
            sessionHasRecorder = false
            focusOverride = if (cbFocus.isChecked && minFocus > 0f) 0f else null
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
            b.addTarget(pSurface)
            applyControls(b, false, false)
            builder = b
            cam.createCaptureSession(listOf(pSurface, reader.surface), object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    if (stackTarget == 1) {
                        log("Долгая выдержка " + (stackTotalNs / 1_000_000_000L) + " с: один кадр")
                    } else {
                        log("Долгая выдержка " + (stackTotalNs / 1_000_000_000L) + " с: " + stackTarget +
                            " кадров (по 30 с, последний " + (stackFrameNs(stackTarget - 1) / 1_000_000_000L) + " с), затем сложение")
                    }
                    startFocusRamp { beginStackCaptures() }
                }
                override fun onConfigureFailed(s: CameraCaptureSession) {
                    log("Сессия не настроилась")
                    stacking = false
                    cleanupStack()
                    startPreview()
                }
            }, handler)
        } catch (e: Exception) {
            log("Ошибка запуска долгой выдержки: $e")
            stacking = false
            cleanupStack()
            startPreview()
        }
    }

    // Результат кадра: проверяем, какую выдержку реально дала камера
    private val stackCb = object : CameraCaptureSession.CaptureCallback() {
        override fun onCaptureCompleted(
            session: CameraCaptureSession,
            request: CaptureRequest,
            result: TotalCaptureResult
        ) {
            val e = result.get(CaptureResult.SENSOR_EXPOSURE_TIME)
            val want = request.get(CaptureRequest.SENSOR_EXPOSURE_TIME) ?: stackFrameExpNs
            if (e != null && want > 0 && stackLogged < 3) {
                val ratio = e.toDouble() / want
                if (stackLogged == 0 || ratio < 0.9 || ratio > 1.1) {
                    stackLogged++
                    log("Выдержка кадра по данным камеры: " + fmtExp(e) + " (задано " + fmtExp(want) + ")")
                }
            }
        }

        override fun onCaptureFailed(
            session: CameraCaptureSession,
            request: CaptureRequest,
            failure: CaptureFailure
        ) {
            if (!stacking) return
            log("Долгая выдержка: кадр не снят (код " + failure.reason + ")")
            finishStack()
        }
    }

    // таймер на кнопке, пока идёт долгая выдержка
    private val stackTicker = object : Runnable {
        override fun run() {
            if (!stacking || stackCancel) return
            val el = ((SystemClock.uptimeMillis() - stackT0) / 1000L).toInt()
            val tot = (stackTotalNs / 1_000_000_000L).toInt()
            val extra = if (stackTarget > 1) "\nкадр " + min(stackCount + 1, stackTarget) + "/" + stackTarget else ""
            runOnUiThread { btnStack.text = "Стоп " + min(el, tot) + "/" + tot + " с" + extra }
            handler.postDelayed(this, 500L)
        }
    }

    // Превью замирает на последнем кадре: запрос превью останавливаем и больше не отправляем кадры на экран.
    // Камера занимается только серией снимков, которые ставятся в очередь по несколько штук.
    private fun beginStackCaptures() {
        try { session?.stopRepeating() } catch (_: Exception) {}
        stackLastT = System.currentTimeMillis()
        log("Превью заморожено, идёт серия кадров")
        val first = min(2, stackTarget)
        for (i in 0 until first) captureStackFrame()
        stackT0 = SystemClock.uptimeMillis()
        handler.post(stackTicker)
    }

    private fun captureStackFrame() {
        val cam = device
        val s = session
        val reader = stackReader
        if (cam == null || s == null || reader == null) return
        try {
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_STILL_CAPTURE)
            b.addTarget(reader.surface)
            applyControls(b, false, false)
            if (Build.VERSION.SDK_INT >= 30) b.set(CaptureRequest.CONTROL_ENABLE_ZSL, false)
            // выдержка кадра серии (для одного длинного кадра это вся «долгая выдержка»)
            val fe = stackFrameNs(stackSubmitted)
            b.set(CaptureRequest.SENSOR_EXPOSURE_TIME, fe)
            b.set(CaptureRequest.SENSOR_FRAME_DURATION, max(fe, 33_333_333L))
            s.capture(b.build(), stackCb, handler)
            stackSubmitted++
        } catch (e: Exception) {
            log("Ошибка кадра: $e")
            finishStack()
        }
    }

    private fun onStackImage(r: ImageReader) {
        val img = r.acquireNextImage() ?: return
        try {
            accumulate(img)
        } catch (e: Exception) {
            log("Ошибка обработки кадра: $e")
        } finally {
            img.close()
        }
        if (!stacking) return
        stackCount++
        val cnt = stackCount
        val tgt = stackTarget
        val now = System.currentTimeMillis()
        if (cnt <= 5) {
            log("Кадр " + cnt + "/" + tgt + ": +" + String.format(Locale.US, "%.2f", (now - stackLastT) / 1000.0) + " с")
        }
        stackLastT = now
        if (stackCancel || cnt >= tgt) finishStack()
        else if (stackSubmitted < tgt) captureStackFrame()
    }

    private fun accumulate(img: Image) {
        val ya = yAcc ?: return
        val ua = uAcc ?: return
        val va = vAcc ?: return
        val w = stackW
        val h = stackH
        if (img.width != w || img.height != h) return
        val yp = img.planes[0]
        val up = img.planes[1]
        val vp = img.planes[2]
        val yb = yp.buffer
        val ub = up.buffer
        val vb = vp.buffer
        val row = ByteArray(w)
        val sum = stackSum
        for (y in 0 until h) {
            yb.position(y * yp.rowStride)
            yb.get(row, 0, w)
            val o = y * w
            if (sum) {
                for (x in 0 until w) ya[o + x] += lin[row[x].toInt() and 0xFF]
            } else {
                for (x in 0 until w) ya[o + x] += row[x].toInt() and 0xFF
            }
        }
        val cw = w / 2
        val ch = h / 2
        for (y in 0 until ch) {
            for (x in 0 until cw) {
                val ui = y * up.rowStride + x * up.pixelStride
                val vi = y * vp.rowStride + x * vp.pixelStride
                ua[y * cw + x] += ub.get(ui).toInt() and 0xFF
                va[y * cw + x] += vb.get(vi).toInt() and 0xFF
            }
        }
    }

    private fun buildStackJpeg(n: Int): ByteArray? {
        val ya = yAcc ?: return null
        val ua = uAcc ?: return null
        val va = vAcc ?: return null
        val w = stackW
        val h = stackH
        val nv = ByteArray(w * h * 3 / 2)
        val inv = invLut
        val sum = stackSum
        for (i in 0 until w * h) {
            nv[i] = if (sum) inv[min(ya[i] shr 2, 16383)].toByte() else (ya[i] / n).toByte()
        }
        val cw = w / 2
        val ch = h / 2
        var p = w * h
        for (y in 0 until ch) {
            for (x in 0 until cw) {
                val ci = y * cw + x
                var u = ua[ci].toFloat() / n - 128f
                var v = va[ci].toFloat() / n - 128f
                if (sum) {
                    val sl = ya[(2 * y) * w + 2 * x]
                    val outY = inv[min(sl shr 2, 16383)]
                    val avgY = inv[min((sl / n) shr 2, 16383)]
                    val k = if (avgY > 0) min(outY.toFloat() / avgY, 8f) else 1f
                    u *= k
                    v *= k
                }
                nv[p++] = (v + 128f).coerceIn(0f, 255f).toInt().toByte()
                nv[p++] = (u + 128f).coerceIn(0f, 255f).toInt().toByte()
            }
        }
        val yuv = YuvImage(nv, ImageFormat.NV21, w, h, null)
        val out = ByteArrayOutputStream()
        yuv.compressToJpeg(Rect(0, 0, w, h), 100, out)
        return out.toByteArray()
    }

    private fun finishStack() {
        val n = stackCount
        stacking = false
        beep()
        try {
            if (n == 0) {
                log("Кадров нет")
            } else {
                log("Обработка $n кадров...")
                val jpeg = buildStackJpeg(n)
                if (jpeg != null) {
                    val fNow = currentFocus()
                    var doneNs = 0L
                    for (i in 0 until n) doneNs += stackFrameNs(i)
                    savePhoto(
                        jpeg, outputRotation(),
                        shotInfo(n, stackFrameExpNs, doneNs),
                        doneNs / 1e9,
                        if (cbExp.isChecked) currentIso() else null,
                        if (cbFocus.isChecked && fNow > 0.01f) 1.0 / fNow else null,
                        fileTag(n, stackFrameExpNs, doneNs)
                    )
                } else log("Нет данных")
            }
        } catch (e: Throwable) {
            log("Ошибка обработки: $e")
        }
        cleanupStack()
        startPreview()
    }

    // ---------- запись видео ----------

    private fun cleanupRecorder() {
        try { recorder?.reset() } catch (_: Exception) {}
        try { recorder?.release() } catch (_: Exception) {}
        recorder = null
        try { pfd?.close() } catch (_: Exception) {}
        pfd = null
    }

    private fun startRecording() {
        if (mode == 2) { log("В режиме таймлапса используйте кнопку «Таймлапс»"); return }
        if (tlRunning) { log("Идёт таймлапс"); return }
        if (stacking) { log("Идёт долгая выдержка"); return }
        if (device == null) { log("Камера ещё не открыта"); return }
        clearPreviewOff()
        if (rampActive) { log("Подождите, линза встаёт на место"); return }
        if (sessionHasRecorder && persistentSurface != null) startRecordingPersistent()
        else startRecordingLegacy()
    }

    private fun restorePreview() {
        val sess = session ?: return
        val pb = previewBuilder ?: return
        builder = pb
        try {
            applyControls(pb, false)
            setRepeatingAny(sess, pb)
        } catch (e: Exception) {
            log("Ошибка возврата превью: $e")
        }
    }

    private fun startRecordingPersistent() {
        val cam = device
        val sess = session
        val ps = persistentSurface
        val pv = previewSurface
        if (cam == null || sess == null || ps == null || pv == null) { startRecordingLegacy(); return }
        try {
            val uri = createVideoEntry()
            if (uri == null) { log("Не удалось создать файл видео в галерее"); return }
            val fd = contentResolver.openFileDescriptor(uri, "w")
            if (fd == null) { log("Не удалось открыть файл видео"); discardVideoEntry(); return }
            pfd = fd

            val fixed = bitrates[bitrateIdx]
            val br = if (fixed > 0) fixed * 1_000_000
            else (videoSize.width.toLong() * videoSize.height * 30 * 0.15).toLong()
                .coerceIn(8_000_000L, 50_000_000L).toInt()
            val r = MediaRecorder()
            r.setOnErrorListener { _, what, extra -> log("Ошибка рекордера: what=$what extra=$extra") }
            r.setOnInfoListener { _, what, extra -> log("Рекордер: info what=$what extra=$extra") }
            val withAudio = checkSelfPermission(Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED
            if (withAudio) r.setAudioSource(MediaRecorder.AudioSource.MIC) else log("Нет разрешения на микрофон, запись без звука")
            r.setVideoSource(MediaRecorder.VideoSource.SURFACE)
            r.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
            r.setOutputFile(fd.fileDescriptor)
            if (withAudio) {
                r.setAudioEncoder(MediaRecorder.AudioEncoder.AAC)
                r.setAudioEncodingBitRate(128_000)
                r.setAudioSamplingRate(44_100)
            }
            r.setVideoEncoder(videoEncoderType())
            r.setVideoEncodingBitRate(br)
            r.setVideoFrameRate(activeFps())
            r.setVideoSize(videoSize.width, videoSize.height)
            r.setOrientationHint(outputRotation())
            r.setInputSurface(ps)
            r.prepare()
            recorder = r

            val rb = cam.createCaptureRequest(CameraDevice.TEMPLATE_RECORD)
            rb.addTarget(pv)
            rb.addTarget(ps)
            applyControls(rb, true)
            builder = rb
            setRepeatingAny(sess, rb)
            r.start()
            recording = true
            recordingPersistent = true
            btnRec.text = "Стоп"
            updatePauseUi()
            log("ЗАПИСЬ ИДЁТ: " + videoSize.width + "x" + videoSize.height + ", " + (br / 1_000_000) +
                " Мбит/с, " + (if (useHevc) "H.265" else "H.264"))
        } catch (e: Exception) {
            log("Ошибка записи: $e")
            cleanupRecorder()
            discardVideoEntry()
            recording = false
            recordingPersistent = false
            btnRec.text = "Видео"
            updatePauseUi()
            restorePreview()
        }
    }

    private fun stopRecordingPersistent() {
        var ok = true
        var why: String? = null
        try {
            restorePreview()
            try {
                recorder?.stop()
            } catch (e: Exception) {
                ok = false
                why = "рекордер не смог завершить файл: $e"
            }
            cleanupRecorder()
            finishVideoFile(ok, why)
        } catch (e: Throwable) {
            log("Видео: ошибка при завершении записи: $e")
            discardVideoEntry()
        } finally {
            recording = false
            recordingPersistent = false
            btnRec.text = "Видео"
            updatePauseUi()
        }
        if (!ok) markVideoSizeBad()
    }

    // Запись на этом размере сломалась: пробуем следующий и пересоздаём превью с новым кодером
    private fun markVideoSizeBad() {
        badVideoSizes.add(videoSize.toString())
        val old = videoSize
        computeSizes()
        log("Размер видео $old не работает, следующая запись будет в $videoSize")
        if (!recordingPersistent) startPreview()
    }

    private fun startRecordingLegacy() {
        val cam = device
        if (cam == null) { log("Сначала откройте камеру"); return }
        if (stacking) { log("Идёт долгая выдержка"); return }
        try {
            val uri = createVideoEntry()
            if (uri == null) { log("Не удалось создать файл видео в галерее"); return }
            val fd = contentResolver.openFileDescriptor(uri, "w")
            if (fd == null) { log("Не удалось открыть файл видео"); discardVideoEntry(); return }
            pfd = fd

            val cands = if (videoCandidates.isEmpty()) listOf(videoSize) else videoCandidates.take(4)
            var made: MediaRecorder? = null
            for (sz in cands) {
                val t = MediaRecorder()
                try {
                    val withAudio = checkSelfPermission(Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED
                    if (withAudio) t.setAudioSource(MediaRecorder.AudioSource.MIC)
                    t.setVideoSource(MediaRecorder.VideoSource.SURFACE)
                    t.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
                    t.setOutputFile(fd.fileDescriptor)
                    if (withAudio) {
                        t.setAudioEncoder(MediaRecorder.AudioEncoder.AAC)
                        t.setAudioEncodingBitRate(128_000)
                        t.setAudioSamplingRate(44_100)
                    }
                    t.setVideoEncoder(videoEncoderType())
                    val fixed = bitrates[bitrateIdx]
                    val br = if (fixed > 0) fixed * 1_000_000
                    else (sz.width.toLong() * sz.height * activeFps() * 0.15).toLong()
                        .coerceIn(8_000_000L, 50_000_000L).toInt()
                    t.setVideoEncodingBitRate(br)
                    t.setVideoFrameRate(activeFps())
                    t.setVideoSize(sz.width, sz.height)
                    t.setOrientationHint(outputRotation())
                    t.prepare()
                    made = t
                    videoSize = sz
                    log("Видео: " + sz.width + "x" + sz.height + ", " + (br / 1_000_000) + " Мбит/с, " + (if (useHevc) "H.265" else "H.264"))
                    break
                } catch (e: Exception) {
                    log("Размер " + sz.width + "x" + sz.height + " не подошёл: " + e)
                    try { t.reset() } catch (_: Exception) {}
                    try { t.release() } catch (_: Exception) {}
                }
            }
            val rec: MediaRecorder = made ?: run {
                log("Не удалось подготовить запись")
                cleanupRecorder()
                discardVideoEntry()
                return
            }
            rec.setOnErrorListener { _, what, extra -> log("Ошибка рекордера: what=$what extra=$extra") }
            rec.setOnInfoListener { _, what, extra -> log("Рекордер: info what=$what extra=$extra") }
            recorder = rec

            val st = texture.surfaceTexture!!
            st.setDefaultBufferSize(previewSize.width, previewSize.height)
            val pSurface = Surface(st)
            val rSurface = rec.surface
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_RECORD)
            b.addTarget(pSurface)
            b.addTarget(rSurface)
            applyControls(b, true)
            builder = b

            try { session?.close() } catch (_: Exception) {}
            session = null
            sessionHasRecorder = false
            createSessionWithParams(cam, listOf(pSurface, rSurface), b.build(), object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    try {
                        s.setRepeatingRequest(b.build(), null, handler)
                        rec.start()
                        recording = true
                        runOnUiThread { btnRec.text = "Стоп" }
                        updatePauseUi()
                        log("ЗАПИСЬ ИДЁТ")
                    } catch (e: Exception) {
                        log("Ошибка старта записи: $e")
                        cleanupRecorder()
                        discardVideoEntry()
                        startPreview()
                    }
                }
                override fun onConfigureFailed(s: CameraCaptureSession) {
                    log("Сессия записи не настроилась")
                    cleanupRecorder()
                    discardVideoEntry()
                    startPreview()
                }
            })
        } catch (e: Exception) {
            log("Ошибка записи: $e")
            cleanupRecorder()
            discardVideoEntry()
        }
    }

    private fun stopRecording() {
        if (recordingPersistent) { stopRecordingPersistent(); return }
        var ok = true
        var why: String? = null
        try {
            try { session?.stopRepeating() } catch (_: Exception) {}
            try { session?.abortCaptures() } catch (_: Exception) {}
            try {
                recorder?.stop()
            } catch (e: Exception) {
                ok = false
                why = "рекордер не смог завершить файл: $e"
            }
            cleanupRecorder()
            finishVideoFile(ok, why)
        } catch (e: Throwable) {
            log("Видео: ошибка при завершении записи: $e")
            discardVideoEntry()
        } finally {
            recording = false
            btnRec.text = "Видео"
            updatePauseUi()
        }
        if (!ok) markVideoSizeBad() else startPreview()
    }

    // ---------- риски на ползунках ----------

    private fun niceStep(span: Double, maxCount: Int): Double {
        var mag = 1.0
        while (true) {
            for (m in doubleArrayOf(1.0, 2.0, 5.0)) {
                val st = mag * m
                if (span / st <= maxCount) return st
            }
            mag *= 10.0
        }
    }

    // равномерная шкала: подписи на концах и на «круглых» значениях, короткие риски посередине
    private fun linearTicks(lo: Double, hi: Double, maxP: Int, maxLabels: Int, fmt: (Double) -> String): List<TickSeekBar.Tick> {
        val span = hi - lo
        if (span <= 0.0) return emptyList()
        val step = niceStep(span, maxLabels)
        fun pos(v: Double): Int = Math.round((v - lo) / span * maxP).toInt().coerceIn(0, maxP)
        val out = ArrayList<TickSeekBar.Tick>()
        out.add(TickSeekBar.Tick(0, fmt(lo), 0))
        out.add(TickSeekBar.Tick(maxP, fmt(hi), 0))
        var k = Math.floor(lo / step).toLong() + 1
        var guard = 0
        while (k * step < hi - span * 0.02 && guard++ < 50) {
            val v = k * step
            if (v > lo + span * 0.02) out.add(TickSeekBar.Tick(pos(v), fmt(v), 1))
            k++
        }
        var j = Math.floor(lo / (step / 2)).toLong() + 1
        guard = 0
        while (j * step / 2 < hi && guard++ < 100) {
            if (j % 2L != 0L) {
                val v = j * step / 2
                if (v > lo && v < hi) out.add(TickSeekBar.Tick(pos(v), null, 2))
            }
            j++
        }
        return out
    }

    private fun expLabel(sec: Double): String =
        if (sec >= 0.999) String.format(Locale.US, "%.0f с", sec) else "1/" + Math.round(1.0 / sec)

    private fun applyTicks() {
        // зум: логарифмическая шкала
        val mz = maxZoom.toDouble()
        if (mz > 1.05) {
            val majors = doubleArrayOf(1.0, 2.0, 3.0, 5.0, 10.0, 20.0, 50.0)
            val all = doubleArrayOf(1.0, 1.5, 2.0, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0, 15.0, 20.0, 30.0, 50.0)
            val l = ArrayList<TickSeekBar.Tick>()
            for (z in all) {
                if (z > mz * 1.001) continue
                val p = Math.round(1000.0 * Math.log(z) / Math.log(mz)).toInt().coerceIn(0, 1000)
                val isMajor = majors.any { it == z }
                l.add(TickSeekBar.Tick(p, if (isMajor) String.format(Locale.US, "%.0f×", z) else null, 0))
            }
            sbZoom.setTicks(l)
        } else sbZoom.setTicks(emptyList())

        // ISO: равномерная шкала
        val ir = isoRange
        if (ir != null && ir.upper > ir.lower) {
            sbIso.setTicks(linearTicks(ir.lower.toDouble(), ir.upper.toDouble(), 1000, 7) { it.toInt().toString() })
        } else sbIso.setTicks(emptyList())

        // выдержка: логарифмическая шкала, подписи примерно через 3 ступени
        val er = expRange
        if (er != null) {
            val lo = er.lower.toDouble()
            val hi = max(5_000_000_000L, er.lower + 1).toDouble()
            if (hi > lo) {
                val stops = doubleArrayOf(
                    1 / 8000.0, 1 / 4000.0, 1 / 2000.0, 1 / 1000.0, 1 / 500.0, 1 / 250.0, 1 / 125.0, 1 / 60.0,
                    1 / 30.0, 1 / 15.0, 1 / 8.0, 1 / 4.0, 1 / 2.0, 1.0, 2.0, 4.0, 8.0, 15.0, 30.0, 60.0, 120.0
                )
                val prioOrder = doubleArrayOf(
                    1 / 60.0, 1.0, 1 / 1000.0, 1 / 15.0, 1 / 250.0, 1 / 4.0, 4.0, 1 / 4000.0, 15.0, 30.0
                )
                val l = ArrayList<TickSeekBar.Tick>()
                for (s in stops) {
                    val ns = s * 1e9
                    if (ns < lo * 0.999 || ns > hi * 1.001) continue
                    val p = Math.round(1000.0 * Math.log(ns / lo) / Math.log(hi / lo)).toInt().coerceIn(0, 1000)
                    val pi = prioOrder.indexOfFirst { it == s }
                    l.add(TickSeekBar.Tick(p, if (pi >= 0) expLabel(s) else null, if (pi >= 0) pi else 99))
                }
                l.add(TickSeekBar.Tick(1000, "5 с", -1))
                sbExp.setTicks(l)
            } else sbExp.setTicks(emptyList())
        } else sbExp.setTicks(emptyList())

        // фокус: подписи в сантиметрах до предмета, справа бесконечность
        val mf = minFocus.toDouble()
        if (mf > 0.5) {
            val l = ArrayList<TickSeekBar.Tick>()
            l.add(TickSeekBar.Tick(1000, "∞", 0))
            l.add(TickSeekBar.Tick(0, String.format(Locale.US, "%.0f", 100.0 / mf), 0))
            val majors = intArrayOf(100, 50, 30, 20, 10, 5, 3)
            val minors = intArrayOf(70, 40, 15, 7, 4)
            for (dcm in majors) {
                val f = 100.0 / dcm
                if (f >= mf * 0.97) continue
                l.add(TickSeekBar.Tick(Math.round(1000.0 * (1.0 - f / mf)).toInt().coerceIn(0, 1000), "$dcm", 1))
            }
            for (dcm in minors) {
                val f = 100.0 / dcm
                if (f >= mf * 0.97) continue
                l.add(TickSeekBar.Tick(Math.round(1000.0 * (1.0 - f / mf)).toInt().coerceIn(0, 1000), null, 2))
            }
            sbFocus.setTicks(l)
        } else sbFocus.setTicks(emptyList())

        // цифровое усиление
        val br = boostRange
        if (br != null && br.upper > br.lower) {
            sbBoost.setTicks(linearTicks(br.lower.toDouble(), br.upper.toDouble(), 1000, 6) { it.toInt().toString() + "%" })
        } else sbBoost.setTicks(emptyList())

        // долгая выдержка: 2..120 с
        sbStack.setTicks(linearTicks(2.0, 120.0, 118, 6) { it.toInt().toString() })

        // интервал таймлапса: по одной риске на каждое значение списка
        val tl = ArrayList<TickSeekBar.Tick>()
        val ends = intArrayOf(tlIntervals.first(), tlIntervals.last())
        val labelled = intArrayOf(1, 5, 10, 30, 60, 120, 300, 600)
        for (i in tlIntervals.indices) {
            val v = tlIntervals[i]
            val text = if (v >= 60) (v / 60).toString() + "м" else v.toString()
            tl.add(TickSeekBar.Tick(i, if (labelled.contains(v)) text else null, if (ends.contains(v)) 0 else 1))
        }
        sbTl.setTicks(tl)
    }

    // ---------- превью вкл/выкл ----------
    // Пока превью выключено, настройки меняются мгновенно и без очереди длинных кадров;
    // при включении камера сразу работает с новыми настройками.

    private fun setPreviewEnabled(on: Boolean) {
        if (!on && (recording || stacking || tlRunning)) {
            log("Во время съёмки превью выключить нельзя")
            return
        }
        if (on == !previewOff) return
        previewOff = !on
        btnPreview.text = if (previewOff) "Превью: выкл" else "Превью: вкл"
        if (previewOff) {
            // обрываем кадр, который сейчас экспонируется, а не дожидаемся его конца;
            // делаем это в потоке камеры, чтобы не подвешивать интерфейс
            val s = session
            handler.post {
                try { s?.stopRepeating() } catch (_: Exception) {}
                try { s?.abortCaptures() } catch (_: Exception) {}
            }
            log("Превью выключено, текущий кадр прерван. Меняйте настройки, они применятся при включении")
        } else {
            // стираем старый кадр: экран чёрный, пока камера не отдаст первый новый кадр
            coverPending = true
            previewCover.visibility = View.VISIBLE
            texture.postDelayed({
                if (coverPending) {
                    coverPending = false
                    previewCover.visibility = View.GONE
                }
            }, 15_000L)
            handler.post { updateRepeating() }
            log("Превью включено: накопление начато заново с новыми настройками")
        }
    }

    // съёмка сама включает превью (камере нужен рабочий поток кадров)
    private fun clearPreviewOff() {
        if (!previewOff) return
        previewOff = false
        runOnUiThread { btnPreview.text = "Превью: вкл" }
    }

    // ---------- таймлапс ----------
    // Каждые N секунд камера снимает кадр (YUV), кадр сразу уходит в кодер (H.265/H.264) и в MP4.
    // Скорость ролика задаётся только частотой кадров: интервал × tlFps.

    private fun tlInterval(): Int = tlIntervals[sbTl.progress.coerceIn(0, tlIntervals.size - 1)]

    private fun tlLabel(): String {
        val iv = tlInterval()
        val speed = iv * tlFps
        var hours = 1
        var vid = 3600.0 * hours / speed
        if (vid < 5.0) { hours = 8; vid = 3600.0 * hours / speed }
        if (vid < 5.0) { hours = 24; vid = 3600.0 * hours / speed }
        val vs = if (vid >= 10.0) String.format(Locale.US, "%.0f", vid) else String.format(Locale.US, "%.1f", vid)
        val hs = when (hours) { 1 -> "1 час"; 8 -> "8 часов"; else -> "24 часа" }
        return "Интервал: $iv с\n×$speed, $hs → $vs с видео"
    }

    // размер кадра: YUV-размер того же формата, ближайший к выбранному разрешению видео
    private fun pickTimelapseSize(): Size? {
        val map = streamMap ?: return null
        val yuv = sizesFor(map.getOutputSizes(ImageFormat.YUV_420_888), Int.MAX_VALUE)
            .filter {
                it.width % 2 == 0 && it.height % 2 == 0 &&
                    it.width.toLong() * it.height <= 3840L * 2160L &&
                    encoderSupports(it.width, it.height)
            }
        if (yuv.isEmpty()) return null
        val t = videoSize
        return yuv.firstOrNull { it == t }
            ?: yuv.firstOrNull { it.width.toLong() * it.height <= t.width.toLong() * t.height }
            ?: yuv.last()
    }

    // причина для автоостановки: низкий заряд (если не на зарядке) или мало места
    private fun tlStopReasonIfLow(): String? {
        try {
            val i = registerReceiver(null, IntentFilter(Intent.ACTION_BATTERY_CHANGED))
            if (i != null) {
                val level = i.getIntExtra(BatteryManager.EXTRA_LEVEL, -1)
                val scale = i.getIntExtra(BatteryManager.EXTRA_SCALE, 100)
                val status = i.getIntExtra(BatteryManager.EXTRA_STATUS, -1)
                val charging = status == BatteryManager.BATTERY_STATUS_CHARGING ||
                    status == BatteryManager.BATTERY_STATUS_FULL
                if (level >= 0 && scale > 0) {
                    val pct = level * 100 / scale
                    if (!charging && pct <= tlMinBattery) return "низкий заряд ($pct%)"
                }
            }
        } catch (_: Exception) {
        }
        try {
            val free = StatFs(Environment.getExternalStorageDirectory().path).availableBytes
            if (free < tlMinFreeMb * 1024L * 1024L) return "мало места на телефоне (" + (free / 1048576L) + " МБ)"
        } catch (_: Exception) {
        }
        return null
    }

    private fun tlUiIdle() {
        btnTl.text = "Таймлапс"
        btnTl.isEnabled = true
        sbTl.isEnabled = true
        cbTlJpeg.isEnabled = true
    }

    private fun releaseTlEncoder() {
        try { tlCodec?.stop() } catch (_: Exception) {}
        try { tlCodec?.release() } catch (_: Exception) {}
        tlCodec = null
        try { tlMuxer?.release() } catch (_: Exception) {}
        tlMuxer = null
        tlMuxStarted = false
        try { tlReader?.close() } catch (_: Exception) {}
        tlReader = null
        cleanupRecorder() // закрывает и файловый дескриптор
    }

    private fun startTimelapse() {
        val cam = device
        if (cam == null) { log("Сначала откройте камеру"); return }
        if (recording || stacking) { log("Сначала остановите запись или долгую выдержку"); return }
        if (rampActive) { log("Подождите, линза встаёт на место"); return }
        val sz = pickTimelapseSize()
        if (sz == null) { log("Таймлапс: нет подходящего размера кадра"); return }
        val low = tlStopReasonIfLow()
        if (low != null) { log("Таймлапс не запущен: $low"); return }
        clearPreviewOff()

        tlW = sz.width
        tlH = sz.height
        tlIntervalMs = tlInterval() * 1000L
        tlSaveJpeg = cbTlJpeg.isChecked
        tlRotation = outputRotation()
        tlFrames = 0
        tlTrack = -1
        tlMuxStarted = false
        tlPendingSince = 0L
        tlShotIdx = 0L
        tlFailStreak = 0
        tlSkipped = 0
        tlLockEngaged = false
        tlJpegDir = "Timelapse_" + stamp()
        try {
            val uri = createVideoEntry()
            if (uri == null) { log("Не удалось создать файл видео в галерее"); return }
            tlInfo = videoInfo ?: ""
            val fd = contentResolver.openFileDescriptor(uri, "rw")
            if (fd == null) { log("Не удалось открыть файл видео"); discardVideoEntry(); return }
            pfd = fd

            val mime = if (useHevc) MediaFormat.MIMETYPE_VIDEO_HEVC else MediaFormat.MIMETYPE_VIDEO_AVC
            val fmt = MediaFormat.createVideoFormat(mime, tlW, tlH)
            fmt.setInteger(MediaFormat.KEY_COLOR_FORMAT, MediaCodecInfo.CodecCapabilities.COLOR_FormatYUV420Flexible)
            fmt.setInteger(MediaFormat.KEY_BIT_RATE, bitrates[bitrateIdx] * 1_000_000)
            fmt.setInteger(MediaFormat.KEY_FRAME_RATE, tlFps)
            fmt.setInteger(MediaFormat.KEY_I_FRAME_INTERVAL, 1)
            val codec = MediaCodec.createEncoderByType(mime)
            tlCodec = codec
            codec.configure(fmt, null, null, MediaCodec.CONFIGURE_FLAG_ENCODE)
            codec.start()
            val mux = MediaMuxer(fd.fileDescriptor, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
            mux.setOrientationHint(tlRotation)
            tlMuxer = mux

            if (tlSaveJpeg) tlJpegExec = Executors.newSingleThreadExecutor()

            val reader = ImageReader.newInstance(tlW, tlH, ImageFormat.YUV_420_888, 2)
            reader.setOnImageAvailableListener({ r -> onTlImage(r) }, handler)
            tlReader = reader
            tlRunning = true
            btnTl.text = "Стоп"
            sbTl.isEnabled = false
            cbTlJpeg.isEnabled = false

            try { session?.close() } catch (_: Exception) {}
            session = null
            val st = texture.surfaceTexture!!
            st.setDefaultBufferSize(previewSize.width, previewSize.height)
            val pSurface = Surface(st)
            previewSurface = pSurface
            sessionHasRecorder = false
            focusOverride = if (cbFocus.isChecked && minFocus > 0f) 0f else null
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
            b.addTarget(pSurface)
            applyControls(b, false, false)
            builder = b
            cam.createCaptureSession(listOf(pSurface, reader.surface), object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    try {
                        s.setRepeatingRequest(b.build(), null, handler)
                    } catch (e: Exception) {
                        log("Ошибка запроса: $e")
                    }
                    val iv = tlInterval()
                    log("ТАЙМЛАПС: " + tlW + "x" + tlH + ", интервал " + iv + " с, " + tlFps + " к/с (×" + (iv * tlFps) +
                        "), " + (if (useHevc) "H.265" else "H.264") + ", " + bitrates[bitrateIdx] + " Мбит/с" +
                        (if (tlSaveJpeg) ", + JPEG-кадры" else ""))
                    startFocusRamp { beginTimelapse() }
                }
                override fun onConfigureFailed(s: CameraCaptureSession) {
                    log("Сессия таймлапса не настроилась")
                    finishTimelapse("сессия не настроилась", true)
                }
            }, handler)
        } catch (e: Throwable) {
            log("Таймлапс: ошибка запуска: $e")
            tlRunning = false
            releaseTlEncoder()
            discardVideoEntry()
            tlUiIdle()
            startPreview()
        }
    }

    // прогрев автоэкспозиции, затем (если нужно) блокировка и первый кадр
    private fun beginTimelapse() {
        if (!tlRunning) return
        val warm = if (cbExp.isChecked) 300L else 1500L
        handler.postDelayed({
            if (!tlRunning) return@postDelayed
            tlLockEngaged = true
            updateRepeating()
            tlStartUptime = SystemClock.uptimeMillis() + 400L
            tlShotIdx = 0L
            scheduleTlTick()
        }, warm)
    }

    private fun scheduleTlTick() {
        if (!tlRunning) return
        val at = tlStartUptime + tlShotIdx * tlIntervalMs
        handler.postAtTime({ tlTick() }, tlTickToken, at)
    }

    private fun tlTick() {
        if (!tlRunning) return
        val low = tlStopReasonIfLow()
        if (low != null) { finishTimelapse(low, true); return }
        tlShotIdx++
        scheduleTlTick() // следующий кадр по абсолютному времени, без накопления сдвига
        val now = SystemClock.uptimeMillis()
        if (tlPendingSince != 0L) {
            if (now - tlPendingSince < 20_000L) {
                tlSkipped++
                if (tlSkipped == 1 || tlSkipped % 20 == 0) {
                    log("Таймлапс: предыдущий кадр ещё обрабатывается, шаг пропущен ($tlSkipped)")
                }
                return
            }
            tlPendingSince = 0L
        }
        captureTlFrame()
    }

    private val tlCb = object : CameraCaptureSession.CaptureCallback() {
        override fun onCaptureFailed(
            session: CameraCaptureSession,
            request: CaptureRequest,
            failure: CaptureFailure
        ) {
            tlPendingSince = 0L
            if (tlRunning) log("Таймлапс: кадр не снят (код " + failure.reason + ")")
        }
    }

    private fun captureTlFrame() {
        val cam = device
        val s = session
        val reader = tlReader
        if (cam == null || s == null || reader == null) {
            finishTimelapse("камера недоступна", false)
            return
        }
        try {
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_STILL_CAPTURE)
            b.addTarget(reader.surface)
            applyControls(b, false, false)
            if (Build.VERSION.SDK_INT >= 30) b.set(CaptureRequest.CONTROL_ENABLE_ZSL, false)
            tlPendingSince = SystemClock.uptimeMillis()
            s.capture(b.build(), tlCb, handler)
        } catch (e: Exception) {
            tlPendingSince = 0L
            tlFailStreak++
            log("Таймлапс: ошибка запроса кадра: $e")
            if (tlFailStreak >= 3) finishTimelapse("повторные ошибки камеры", true)
        }
    }

    private fun onTlImage(r: ImageReader) {
        val img: Image? = try { r.acquireNextImage() } catch (e: Exception) { null }
        if (img == null) return
        try {
            if (!tlRunning) return
            val n = tlFrames
            encodeTlFrame(img, n)
            if (tlSaveJpeg) queueTlJpeg(img, n)
            tlFrames = n + 1
            tlFailStreak = 0
            val cnt = n + 1
            if (cnt <= 3 || cnt % 20 == 0) {
                log("Таймлапс: кадр " + cnt + ", ролик " + String.format(Locale.US, "%.1f", cnt / tlFps.toDouble()) + " с")
            }
            runOnUiThread { btnTl.text = "Стоп\nкадров: $cnt" }
        } catch (e: Throwable) {
            tlFailStreak++
            log("Таймлапс: ошибка кадра: $e")
            if (tlFailStreak >= 3) handler.post { finishTimelapse("повторные ошибки кодера", true) }
        } finally {
            tlPendingSince = 0L
            try { img.close() } catch (_: Exception) {}
        }
    }

    private fun encodeTlFrame(img: Image, n: Int) {
        val codec = tlCodec ?: throw IllegalStateException("кодер не создан")
        if (img.width != tlW || img.height != tlH) {
            throw IllegalStateException("размер кадра " + img.width + "x" + img.height)
        }
        drainTl(false)
        var idx = codec.dequeueInputBuffer(2_000_000L)
        if (idx < 0) {
            drainTl(false)
            idx = codec.dequeueInputBuffer(2_000_000L)
        }
        if (idx < 0) throw java.io.IOException("кодер не принимает кадры")
        val dst = codec.getInputImage(idx) ?: throw IllegalStateException("кодер не отдал буфер кадра")
        copyImage(img, dst)
        codec.queueInputBuffer(idx, 0, tlW * tlH * 3 / 2, n * 1_000_000L / tlFps, 0)
        drainTl(false)
    }

    // построчное копирование кадра камеры во входной буфер кодера (учитывает шаги строк и пикселей)
    private fun copyImage(src: Image, dst: Image) {
        val w = src.width
        val h = src.height
        for (p in 0 until 3) {
            val sp = src.planes[p]
            val dp = dst.planes[p]
            val pw = if (p == 0) w else w / 2
            val ph = if (p == 0) h else h / 2
            val sb = sp.buffer
            val db = dp.buffer
            val sRow = sp.rowStride
            val dRow = dp.rowStride
            val sPix = sp.pixelStride
            val dPix = dp.pixelStride
            if (sPix == 1 && dPix == 1) {
                val line = ByteArray(pw)
                for (y in 0 until ph) {
                    sb.position(y * sRow)
                    sb.get(line, 0, pw)
                    db.position(y * dRow)
                    db.put(line, 0, pw)
                }
            } else {
                for (y in 0 until ph) {
                    val so = y * sRow
                    val d0 = y * dRow
                    for (x in 0 until pw) db.put(d0 + x * dPix, sb.get(so + x * sPix))
                }
            }
        }
    }

    // забираем готовые куски из кодера и пишем в MP4; untilEos = ждать конца потока
    private fun drainTl(untilEos: Boolean) {
        val codec = tlCodec ?: return
        val info = MediaCodec.BufferInfo()
        var guard = 0
        while (true) {
            val i = codec.dequeueOutputBuffer(info, if (untilEos) 100_000L else 0L)
            if (i == MediaCodec.INFO_TRY_AGAIN_LATER) {
                if (!untilEos) return
                if (++guard > 50) return
                continue
            }
            if (i == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED) {
                val mux = tlMuxer ?: return
                if (!tlMuxStarted) {
                    tlTrack = mux.addTrack(codec.outputFormat)
                    mux.start()
                    tlMuxStarted = true
                }
                continue
            }
            if (i < 0) continue
            guard = 0
            val buf = codec.getOutputBuffer(i)
            if ((info.flags and MediaCodec.BUFFER_FLAG_CODEC_CONFIG) != 0) info.size = 0
            val mux = tlMuxer
            if (info.size > 0 && buf != null && tlMuxStarted && mux != null) {
                buf.position(info.offset)
                buf.limit(info.offset + info.size)
                mux.writeSampleData(tlTrack, buf, info)
            }
            codec.releaseOutputBuffer(i, false)
            if ((info.flags and MediaCodec.BUFFER_FLAG_END_OF_STREAM) != 0) return
        }
    }

    // страховочный JPEG каждого кадра (если включена галочка); сжатие и запись идут в отдельном потоке
    private fun queueTlJpeg(img: Image, n: Int) {
        val exec = tlJpegExec ?: return
        if (tlJpegPending.get() >= 4) {
            log("JPEG: очередь переполнена, кадр " + (n + 1) + " пропущен")
            return
        }
        val w = img.width
        val h = img.height
        val nv = ByteArray(w * h * 3 / 2)
        val yp = img.planes[0]
        val up = img.planes[1]
        val vp = img.planes[2]
        val yb = yp.buffer
        for (y in 0 until h) {
            yb.position(y * yp.rowStride)
            yb.get(nv, y * w, w)
        }
        val ub = up.buffer
        val vb = vp.buffer
        var o = w * h
        for (y in 0 until h / 2) {
            for (x in 0 until w / 2) {
                nv[o++] = vb.get(y * vp.rowStride + x * vp.pixelStride)
                nv[o++] = ub.get(y * up.rowStride + x * up.pixelStride)
            }
        }
        val rot = tlRotation
        val info = tlInfo + "; timelapse frame " + (n + 1)
        val dir = tlJpegDir
        tlJpegPending.incrementAndGet()
        exec.execute {
            try {
                val bos = ByteArrayOutputStream(w * h / 4)
                YuvImage(nv, ImageFormat.NV21, w, h, null).compressToJpeg(Rect(0, 0, w, h), 95, bos)
                savePhoto(bos.toByteArray(), rot, info, null, null, null, String.format(Locale.US, "tl%05d", n + 1), dir, true)
            } catch (e: Throwable) {
                log("JPEG кадра " + (n + 1) + ": " + e)
            } finally {
                tlJpegPending.decrementAndGet()
            }
        }
    }

    // Завершение: дописать кодер, закрыть MP4, проверить файл. Вызывается только в потоке камеры (handler).
    private fun finishTimelapse(reason: String?, restore: Boolean) {
        if (!tlRunning) return
        tlRunning = false
        handler.removeCallbacksAndMessages(tlTickToken)
        tlLockEngaged = false
        runOnUiThread { btnTl.isEnabled = false; btnTl.text = "Сохраняю…" }
        if (reason != null) log("Таймлапс остановлен: $reason")
        try { session?.stopRepeating() } catch (_: Exception) {}
        try { session?.abortCaptures() } catch (_: Exception) {}

        val frames = tlFrames
        var ok = frames > 0
        var why: String? = if (frames > 0) null else "не снято ни одного кадра"
        val codec = tlCodec
        try {
            if (codec != null && frames > 0) {
                val idx = codec.dequeueInputBuffer(2_000_000L)
                if (idx >= 0) {
                    codec.queueInputBuffer(idx, 0, 0, frames * 1_000_000L / tlFps, MediaCodec.BUFFER_FLAG_END_OF_STREAM)
                }
                drainTl(true)
            }
        } catch (e: Throwable) {
            ok = false
            why = "кодер не завершил файл: $e"
        }
        try {
            val mux = tlMuxer
            if (mux != null && tlMuxStarted) mux.stop()
        } catch (e: Throwable) {
            ok = false
            why = "muxer не смог завершить файл: $e"
        }
        releaseTlEncoder()
        try { session?.close() } catch (_: Exception) {}
        session = null

        val ex = tlJpegExec
        tlJpegExec = null
        if (ex != null) {
            ex.shutdown()
            try { ex.awaitTermination(8, TimeUnit.SECONDS) } catch (_: Exception) {}
        }
        try {
            finishVideoFile(ok, why)
        } catch (e: Throwable) {
            log("Видео: ошибка при завершении: $e")
            discardVideoEntry()
        }
        if (frames > 0) {
            log("Таймлапс: " + frames + " кадров, ролик ≈ " + String.format(Locale.US, "%.1f", frames / tlFps.toDouble()) + " с при " + tlFps + " к/с")
            if (tlSaveJpeg) log("JPEG-кадры: Pictures/MacroCam/$tlJpegDir")
        }
        runOnUiThread { tlUiIdle() }
        if (restore) startPreview()
    }

    private fun hideSystemUi() {
        if (Build.VERSION.SDK_INT >= 30) {
            window.setDecorFitsSystemWindows(false)
            window.insetsController?.let {
                it.hide(WindowInsets.Type.systemBars())
                it.systemBarsBehavior = WindowInsetsController.BEHAVIOR_SHOW_TRANSIENT_BARS_BY_SWIPE
            }
        } else {
            window.decorView.systemUiVisibility = (View.SYSTEM_UI_FLAG_FULLSCREEN
                    or View.SYSTEM_UI_FLAG_HIDE_NAVIGATION
                    or View.SYSTEM_UI_FLAG_IMMERSIVE_STICKY
                    or View.SYSTEM_UI_FLAG_LAYOUT_STABLE
                    or View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION
                    or View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN)
        }
    }

    override fun onWindowFocusChanged(hasFocus: Boolean) {
        super.onWindowFocusChanged(hasFocus)
        if (hasFocus) hideSystemUi()
    }

    override fun onRequestPermissionsResult(
        requestCode: Int,
        permissions: Array<out String>,
        grantResults: IntArray
    ) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        tryAutoOpen()
    }

    override fun onConfigurationChanged(newConfig: android.content.res.Configuration) {
        super.onConfigurationChanged(newConfig)
        hideSystemUi()
        updateTransform()
        texture.post { updateTransform() }
        texture.postDelayed({ updateTransform() }, 300)
    }

    override fun onResume() {
        super.onResume()
        hideSystemUi()
        try {
            (getSystemService(DISPLAY_SERVICE) as DisplayManager)
                .registerDisplayListener(displayListener, Handler(Looper.getMainLooper()))
        } catch (_: Exception) {}
        appliedTransformKey = ""
        updateTransform()
        texture.post { updateTransform() }
        texture.postDelayed({ updateTransform() }, 300)
        texture.postDelayed({ updateTransform() }, 900)
        // после галереи не открываем камеру сразу: ждём, пока окно примет свой размер и поворот
        if (cameraWasOpenOnPause) {
            cameraWasOpenOnPause = false
            scheduleRestart(700)
        } else {
            tryAutoOpen()
        }
    }

    private var cameraWasOpenOnPause = false

    override fun onPause() {
        cameraWasOpenOnPause = device != null || opening
        texture.removeCallbacks(restartRunnable)
        try {
            (getSystemService(DISPLAY_SERVICE) as DisplayManager).unregisterDisplayListener(displayListener)
        } catch (_: Exception) {}
        savePrefs()
        if (saveMode) setSaveMode(false)
        if (stacking) {
            stacking = false
            cleanupStack()
        }
        if (tlRunning) {
            // дописываем и закрываем MP4, пока камера ещё жива
            val latch = CountDownLatch(1)
            handler.post {
                try { finishTimelapse("приложение свёрнуто", false) } finally { latch.countDown() }
            }
            try { latch.await(15, TimeUnit.SECONDS) } catch (_: InterruptedException) {}
        }
        if (recording) stopRecording()
        closeAll()
        super.onPause()
    }

    override fun onDestroy() {
        stopServer()
        try { torchCb?.let { cm.unregisterTorchCallback(it) } } catch (_: Exception) {}
        closeAll()
        thread.quitSafely()
        super.onDestroy()
    }
}

private const val WEB_PAGE = """<!DOCTYPE html>
<html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>MacroCam</title>
<style>
html,body{margin:0;height:100%;background:#000;color:#fff;font-family:sans-serif}
#wrap{display:flex;height:100%}
#left{flex:1;position:relative;overflow:hidden;display:flex;align-items:center;justify-content:center}
#v{max-width:100%;max-height:100%;display:block}
#pk{position:absolute;pointer-events:none}
#tog{position:absolute;top:8px;right:8px;z-index:10;width:auto;margin:0;padding:8px 14px;opacity:.6}
#loupe{display:none;position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);border:2px solid #0f0}
#right{width:360px;overflow-y:auto;background:#161616;padding:8px;box-sizing:border-box}
button{margin:3px 0;padding:12px;font-size:16px;width:100%}
.row{display:flex;gap:6px}
.row button{flex:1}
input[type=range]{width:100%;height:34px}
label{display:block;margin:8px 0 2px}
#log{font-size:11px;color:#9a9;white-space:pre-wrap;margin-top:8px}
</style></head><body>
<div id="wrap">
<div id="left"><img id="v" alt=""><canvas id="pk"></canvas><img id="loupe" alt=""><button id="tog">&#9776;</button></div>
<div id="right">
<div class="row"><button id="bPhoto">Фото</button><button id="bStack">Выдержка</button></div>
<div class="row"><button id="bRec">Видео</button><button id="bPause">Пауза</button></div>
<label><input type="checkbox" id="cPk"> Подсветка краёв (на планшете)</label>
<input type="range" id="sPk" min="10" max="150" value="45">
<div style="font-size:12px;color:#999">Нажмите на картинку: живая лупа 1:1 (нажмите на лупу, чтобы закрыть; нажмите в другом месте, чтобы сдвинуть). Кнопка в правом верхнем углу скрывает меню.</div>
<label id="lZoom">Зум</label><input type="range" id="sZoom" min="0" max="1000">
<label><input type="checkbox" id="cExp"> Ручные ISO и выдержка</label>
<label id="lIso">ISO</label><input type="range" id="sIso" min="0" max="1000">
<label id="lExp">Выдержка</label><input type="range" id="sExp" min="0" max="1000">
<div id="boostBox" style="display:none"><label id="lBoost">Усиление</label><input type="range" id="sBoost" min="0" max="1000"></div>
<label><input type="checkbox" id="cFocus"> Ручной фокус</label>
<label id="lFocus">Фокус</label><input type="range" id="sFocus" min="0" max="1000">
<label id="lStack">Долгая выдержка</label><input type="range" id="sStack" min="0" max="118">
<label><input type="checkbox" id="cFlip"> Перевернуть 180°</label>
<button id="bAspect">Формат</button>
<button id="bStab">Стабилизация</button>
<button id="bNr">Шумоподавление</button>
<button id="bEdge">Контуры</button>
<button id="bBit">Битрейт</button>
<button id="bCam">Камера</button>
<button id="bTorch">Фонарик</button>
<div id="log"></div>
</div></div>
<script>
var pin = localStorage.getItem('pin') || '';
var G = function(i){ return document.getElementById(i); };
var st = null, active = null, pend = {}, timer = null, gaveUp = false;
function q(p){ return p + (p.indexOf('?') < 0 ? '?' : '&') + 'pin=' + encodeURIComponent(pin); }
function ask(){
  if (gaveUp) return;
  var p = prompt('PIN с экрана телефона');
  if (p === null) { gaveUp = true; return; }
  pin = p; localStorage.setItem('pin', p); startStream();
}
function startStream(){ G('v').src = q('/stream?t=' + Date.now()); }
G('v').onerror = function(){ if (!gaveUp) setTimeout(startStream, 1000); };
function cmd(c, n, v){ fetch(q('/cmd?c=' + c + '&n=' + n + '&v=' + encodeURIComponent(v))).then(poll).catch(function(){}); }
function flush(){ timer = null; for (var k in pend){ cmd('set', k, pend[k]); } pend = {}; }
function slider(id, name){
  var s = G(id);
  s.addEventListener('input', function(){ active = id; pend[name] = s.value; if (!timer) timer = setTimeout(flush, 80); });
  s.addEventListener('change', function(){ active = null; });
}
function check(id, name){ G(id).addEventListener('change', function(){ cmd('check', name, G(id).checked ? 1 : 0); }); }
function bindClick(id, name){ G(id).addEventListener('click', function(){ cmd('click', name, ''); }); }
function setSl(id, val){ if (active !== id) G(id).value = val; }
function poll(){
  if (gaveUp) return;
  fetch(q('/state')).then(function(r){
    if (r.status === 403) { ask(); return null; }
    return r.json();
  }).then(function(s){
    if (!s) return;
    st = s;
    G('bPause').style.display = s.rec ? '' : 'none';
    G('bRec').textContent = s.recBtn;
    G('bPause').textContent = s.pauseBtn;
    G('bStack').textContent = s.stackBtn;
    G('lZoom').textContent = s.zoomLabel;
    G('lIso').textContent = s.isoLabel;
    G('lExp').textContent = s.expLabel;
    G('lFocus').textContent = s.focusLabel;
    G('lStack').textContent = s.stackLabel;
    G('lBoost').textContent = s.boostLabel;
    G('boostBox').style.display = s.boostOn ? '' : 'none';
    setSl('sZoom', s.zoom); setSl('sIso', s.iso); setSl('sExp', s.exp);
    setSl('sFocus', s.focus); setSl('sBoost', s.boost); setSl('sStack', s.stack);
    G('cExp').checked = s.manExp; G('cFocus').checked = s.manFocus;
    G('cFlip').checked = s.flip;
    G('bAspect').textContent = s.aspect;
    G('bStab').textContent = s.stab;
    G('bNr').textContent = s.nr;
    G('bEdge').textContent = s.edge;
    G('bBit').textContent = s.bitrate;
    G('bTorch').textContent = s.torch;
    G('bCam').textContent = s.cam;
    G('v').style.transform = s.flip ? 'rotate(180deg)' : '';
    G('loupe').style.transform = s.flip ? 'translate(-50%,-50%) rotate(180deg)' : 'translate(-50%,-50%)';
    G('log').textContent = s.log;
  }).catch(function(){});
}
slider('sZoom', 'zoom'); slider('sIso', 'iso'); slider('sExp', 'exp');
slider('sFocus', 'focus'); slider('sBoost', 'boost'); slider('sStack', 'stack');
check('cExp', 'manExp'); check('cFocus', 'manFocus'); check('cFlip', 'flip'); 
bindClick('bPhoto', 'photo'); bindClick('bStack', 'stack');
bindClick('bRec', 'rec'); bindClick('bPause', 'pause'); bindClick('bAspect', 'aspect'); bindClick('bStab', 'stab');
bindClick('bNr', 'nr'); bindClick('bEdge', 'edge'); bindClick('bBit', 'bitrate'); bindClick('bTorch', 'torch'); bindClick('bCam', 'cam');

G('v').addEventListener('click', function(e){
  var r = G('v').getBoundingClientRect();
  var x = (e.clientX - r.left) / r.width, y = (e.clientY - r.top) / r.height;
  if (st && st.flip) { x = 1 - x; y = 1 - y; }
  var L = G('loupe'); L.style.display = 'block';
  L.src = q('/loupestream?x=' + x + '&y=' + y + '&t=' + Date.now());
});
G('loupe').onload = function(){
  var L = G('loupe');
  L.style.width = (L.naturalWidth / window.devicePixelRatio) + 'px';
};
G('loupe').addEventListener('click', function(){ G('loupe').style.display = 'none'; G('loupe').removeAttribute('src'); });

var cv = document.createElement('canvas'), cx = cv.getContext('2d');
var pk = G('pk'), px = pk.getContext('2d');
function peak(){
  var v = G('v');
  if (G('cPk').checked && v.naturalWidth > 0) {
    var w = 480, h = Math.round(480 * v.naturalHeight / v.naturalWidth);
    cv.width = w; cv.height = h;
    try {
      cx.drawImage(v, 0, 0, w, h);
      var d = cx.getImageData(0, 0, w, h).data;
      pk.width = w; pk.height = h;
      var o = px.createImageData(w, h), od = o.data, th = +G('sPk').value;
      for (var y = 1; y < h - 1; y++) {
        for (var x = 1; x < w - 1; x++) {
          var i = (y * w + x) * 4;
          var gx = d[i + 5] - d[i - 3], gy = d[i + w * 4 + 1] - d[i - w * 4 + 1];
          if (Math.abs(gx) + Math.abs(gy) > th) { od[i] = 255; od[i + 3] = 255; }
        }
      }
      px.putImageData(o, 0, 0);
      pk.style.left = v.offsetLeft + 'px'; pk.style.top = v.offsetTop + 'px';
      pk.style.width = v.clientWidth + 'px'; pk.style.height = v.clientHeight + 'px';
      pk.style.transform = (st && st.flip) ? 'rotate(180deg)' : '';
    } catch (e) {}
  } else {
    px.clearRect(0, 0, pk.width, pk.height);
  }
  setTimeout(peak, 150);
}
function applyHide(){ G('right').style.display = (localStorage.getItem('hide') === '1') ? 'none' : ''; }
G('tog').addEventListener('click', function(){
  localStorage.setItem('hide', localStorage.getItem('hide') === '1' ? '0' : '1');
  applyHide();
});
applyHide();
if (!pin) ask(); else startStream();
poll(); setInterval(poll, 600); peak();
</script></body></html>
"""


// SeekBar с аккуратными рисками и подписями под дорожкой (только для ориентира, значения не «прилипают»)
class TickSeekBar(context: Context) : SeekBar(context) {
    class Tick(val progress: Int, val label: String? = null, val prio: Int = 0)

    private var ticks: List<Tick> = emptyList()
    private var labelOrder: List<Tick> = emptyList()
    private val d = context.resources.displayMetrics.density
    private val linePaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val textPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val tallLen = 7 * d
    private val shortLen = 4 * d
    private val textPx = android.util.TypedValue.applyDimension(
        android.util.TypedValue.COMPLEX_UNIT_SP, 10f, context.resources.displayMetrics
    )
    private val extra = (tallLen + textPx + 6 * d).toInt()

    init {
        linePaint.color = Color.argb(190, 255, 255, 255)
        linePaint.strokeWidth = if (d < 1f) 1f else d
        textPaint.color = Color.argb(230, 210, 210, 210)
        textPaint.textSize = textPx
        textPaint.textAlign = Paint.Align.CENTER
        setPadding(paddingLeft, paddingTop, paddingRight, paddingBottom + extra)
    }

    fun setTicks(list: List<Tick>) {
        ticks = list
        labelOrder = list.filter { it.label != null }.sortedWith(compareBy({ it.prio }, { it.progress }))
        invalidate()
    }

    // x-координата центра бегунка при значении p
    private fun xFor(p: Int): Float {
        val scale = p.toFloat() / (if (max > 0) max else 1)
        val tw = thumb?.intrinsicWidth ?: 0
        val avail = width - paddingLeft - paddingRight - tw + thumbOffset * 2
        return paddingLeft - thumbOffset + scale * avail + 0.5f + tw / 2f
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        if (ticks.isEmpty() || max <= 0) return
        val y0 = (height - extra) + d
        for (t in ticks) {
            val x = xFor(t.progress)
            canvas.drawLine(x, y0, x, y0 + (if (t.label != null) tallLen else shortLen), linePaint)
        }
        val baseline = y0 + tallLen + textPx * 0.9f + d
        val drawn = ArrayList<FloatArray>()
        for (t in labelOrder) {
            val text = t.label ?: continue
            val x = xFor(t.progress)
            val w = textPaint.measureText(text)
            var l = x - w / 2
            var r = x + w / 2
            if (l < 0f) { r -= l; l = 0f }
            if (r > width) { l -= r - width; r = width.toFloat() }
            var clash = false
            for (q in drawn) {
                if (l < q[1] + 4 * d && r > q[0] - 4 * d) { clash = true; break }
            }
            if (clash) continue
            canvas.drawText(text, (l + r) / 2f, baseline, textPaint)
            drawn.add(floatArrayOf(l, r))
        }
    }
}
