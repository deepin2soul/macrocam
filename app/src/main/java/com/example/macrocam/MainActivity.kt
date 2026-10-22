package com.example.macrocam
 
import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.content.ClipData
import android.content.ClipboardManager
import android.content.ContentValues
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.ActivityInfo
import android.content.pm.PackageManager
import android.graphics.Bitmap
import android.graphics.ImageFormat
import android.graphics.Matrix
import android.graphics.Rect
import android.graphics.YuvImage
import android.graphics.RectF
import android.graphics.SurfaceTexture
import android.hardware.camera2.*
import android.hardware.camera2.params.StreamConfigurationMap
import android.media.CamcorderProfile
import android.media.AudioAttributes
import android.media.AudioFormat
import android.media.AudioTrack
import android.media.ExifInterface
import android.media.MediaCodec
import android.media.Image
import android.media.ImageReader
import android.media.MediaRecorder
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.HandlerThread
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
import java.io.BufferedReader
import java.io.ByteArrayOutputStream
import java.io.InputStreamReader
import java.io.OutputStream
import java.net.ServerSocket
import java.net.Socket
import java.net.URLDecoder
import java.util.concurrent.CountDownLatch
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
    private val cameraId = "3"
    @Volatile private var opening = false
    private lateinit var sbIso: SeekBar
    private lateinit var sbExp: SeekBar
    private lateinit var sbFocus: SeekBar
    private lateinit var tvIso: TextView
    private lateinit var tvExp: TextView
    private lateinit var tvFocus: TextView
    private lateinit var cbExp: CheckBox
    private lateinit var cbFocus: CheckBox
    private lateinit var cbFlip: CheckBox
    private lateinit var btnRec: Button
    private lateinit var btnAspect: Button
    private lateinit var sbZoom: SeekBar
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
    private val bitrates = intArrayOf(0, 20, 40, 80)
    private var bitrateIdx = 0
    private lateinit var sbStack: SeekBar
    private lateinit var tvStack: TextView
    private lateinit var cbStackSum: CheckBox
    private lateinit var sbBoost: SeekBar
    private lateinit var tvBoost: TextView

    // долгая выдержка (наложение кадров)
    @Volatile private var stacking = false
    @Volatile private var stackCancel = false
    private var stackReader: ImageReader? = null
    private var stackSurface: Surface? = null
    private var stackCount = 0
    private var stackTarget = 0
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

    private fun mkSb(maxValue: Int, progressValue: Int): SeekBar {
        val sb = SeekBar(this)
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

        // левая колонка, всегда на экране
        btnPanel = mkBtn("Панель")
        btnMode = mkBtn("Режим: Фото")
        btnPhoto = mkBtn("Фото")
        btnStack = mkBtn("Долгая")
        btnRec = mkBtn("Запись")
        btnPause = mkBtn("Пауза")
        btnPause.visibility = View.GONE
        btnGallery = mkBtn("Галерея")
        val left = LinearLayout(this)
        left.orientation = LinearLayout.VERTICAL
        left.addView(btnPanel)
        left.addView(btnMode)
        left.addView(btnPhoto)
        left.addView(btnStack)
        left.addView(btnRec)
        left.addView(btnPause)
        left.addView(btnGallery)
        val leftLp = FrameLayout.LayoutParams(wrap, wrap, Gravity.START or Gravity.CENTER_VERTICAL)
        leftLp.leftMargin = dp(8)
        root.addView(left, leftLp)

        // правая панель настроек
        btnServer = mkBtn("Трансляция: выкл")
        btnTorch = mkBtn("Фонарик: выкл")
        btnSave = mkBtn("Экономия (чёрный экран)")
        btnAspect = mkBtn("Формат: 4:3")
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
        btnBitrate = mkBtn("Битрейт: авто")

        val col = LinearLayout(this)
        col.orientation = LinearLayout.VERTICAL
        col.addView(btnServer)
        col.addView(btnTorch)
        col.addView(btnSave)
        col.addView(btnAspect)
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
        col.addView(cbStackSum)
        col.addView(btnNr)
        col.addView(btnEdge)
        col.addView(btnBitrate)

        val panelScroll = ScrollView(this)
        panelScroll.setBackgroundColor(Color.argb(0x99, 0, 0, 0))
        panelScroll.setPadding(dp(8), dp(8), dp(8), dp(8))
        panelScroll.addView(col)
        panel = panelScroll
        root.addView(panelScroll, FrameLayout.LayoutParams(dp(320), match, Gravity.END))

        // лог внизу слева
        logView = TextView(this)
        logView.setTextColor(Color.WHITE)
        logView.textSize = 11f
        logScroll = ScrollView(this)
        logScroll.setBackgroundColor(Color.argb(0x66, 0, 0, 0))
        logScroll.addView(logView)
        val logLp = FrameLayout.LayoutParams(dp(380), dp(64), Gravity.BOTTOM or Gravity.START)
        logLp.leftMargin = dp(96)
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
        cbStackSum.isChecked = prefs.getBoolean("stackSum", true)
        sbBoost.progress = prefs.getInt("boost", 0)
        mode = prefs.getInt("mode", 0).coerceIn(0, 1)
        updateModeUi()
        nrMode = prefs.getInt("nrMode", -1)
        edgeMode = prefs.getInt("edgeMode", -1)
        updateModeButtons()
        bitrateIdx = prefs.getInt("bitrate", 0).coerceIn(0, bitrates.size - 1)
        btnBitrate.text = bitrateLabel()
        cbExp.isChecked = prefs.getBoolean("manExp", false)
        cbFocus.isChecked = prefs.getBoolean("manFocus", false)
        cbFlip.isChecked = prefs.getBoolean("flip", false)
        sbZoom.progress = prefs.getInt("zoom", 0)
        aspectMode = prefs.getInt("aspect", 0).coerceIn(0, 2)
        btnAspect.text = aspectLabel()
        texture.rotation = if (cbFlip.isChecked) 180f else 0f
        texture.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ -> updateTransform() }
        texture.surfaceTextureListener = object : TextureView.SurfaceTextureListener {
            override fun onSurfaceTextureAvailable(st: SurfaceTexture, w: Int, h: Int) {
                updateTransform()
                tryAutoOpen()
            }
            override fun onSurfaceTextureSizeChanged(st: SurfaceTexture, w: Int, h: Int) {
                updateTransform()
            }
            override fun onSurfaceTextureDestroyed(st: SurfaceTexture): Boolean = true
            override fun onSurfaceTextureUpdated(st: SurfaceTexture) {}
        }

        btnPhoto.setOnClickListener { takePhoto() }
        btnRec.setOnClickListener {
            if (recording) stopRecording() else startRecording()
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
        btnStack.setOnClickListener { startStack() }
        btnMode.setOnClickListener { toggleMode() }
        btnPause.setOnClickListener { togglePause() }
        btnGallery.setOnClickListener { openGallery() }
        btnTorch.setOnClickListener { toggleTorch() }
        btnServer.setOnClickListener { toggleServer() }
        btnSave.setOnClickListener { setSaveMode(true) }
        val tapViews = listOf<View>(
            btnPanel, btnMode, btnPhoto, btnStack, btnRec,
            btnAspect, btnNr, btnEdge, btnBitrate, cbExp, cbFocus, cbFlip, cbStackSum,
            btnPause, btnGallery, btnTorch, btnSave, btnServer
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
        btnAspect.setOnClickListener { toggleAspect() }
        btnPanel.setOnClickListener {
            panel.visibility = if (panel.visibility == View.VISIBLE) View.GONE else View.VISIBLE
        }
        cbExp.setOnCheckedChangeListener { _, _ -> savePrefs(); updateRepeating() }
        cbFocus.setOnCheckedChangeListener { _, _ -> savePrefs(); updateRepeating() }
        cbFlip.setOnCheckedChangeListener { _, checked ->
            texture.rotation = if (checked) 180f else 0f
            savePrefs()
        }
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
                if (cameraId == torchId) {
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
            .putInt("edgeMode", edgeMode)
            .putInt("bitrate", bitrateIdx)
            .putInt("aspect", aspectMode)
            .apply()
    }

    private fun log(s: String) {
        synchronized(logBuf) {
            logBuf.add(s)
            if (logBuf.size > 40) logBuf.removeAt(0)
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

    private fun shotInfo(longFrames: Int = 0, frameExpNs: Long = 0L): String {
        val sb = StringBuilder("Exposure ")
        if (longFrames > 0) {
            sb.append(String.format(Locale.US, "%.1f s total (%d frames x %s)",
                longFrames * frameExpNs / 1e9, longFrames, fmtExp(frameExpNs)))
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

    private fun fileTag(longFrames: Int = 0, frameExpNs: Long = 0L): String {
        val sb = StringBuilder()
        if (longFrames > 0) {
            sb.append("long").append(String.format(Locale.US, "%.0fs", longFrames * frameExpNs / 1e9))
                .append("_").append(longFrames).append("x").append(tagExp(frameExpNs))
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
        videoInfo = shotInfo()
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

    private fun finishVideoFile() {
        beep()
        val u = videoUri
        val info = videoInfo
        if (u != null && info != null) embedMp4Comment(u, info)
        if (u != null) rememberLast(u, "video/mp4")
        paused = false
        videoUri = null
        videoInfo = null
    }

    // ---------- значения ползунков ----------

    private fun currentIso(): Int {
        val r = isoRange ?: return 100
        return (r.lower + (r.upper - r.lower) * (sbIso.progress / 1000.0)).toInt()
    }

    private fun currentExp(): Long {
        val r = expRange ?: return 10_000_000L
        val lo = r.lower.toDouble()
        val hi = max(min(r.upper, maxFrameDuration), r.lower + 1).toDouble()
        return (lo * (hi / lo).pow(sbExp.progress / 1000.0)).toLong()
    }

    private fun currentBoost(): Int {
        val r = boostRange ?: return 100
        return (r.lower + (r.upper - r.lower) * (sbBoost.progress / 1000.0)).toInt()
    }

    private fun currentFocus(): Float {
        val f = 26f + (10f - 26f) * (sbFocus.progress / 1000f)
        return if (minFocus > 0f) min(f, minFocus) else f
    }

    private fun currentZoom(): Float =
        maxZoom.toDouble().pow(sbZoom.progress / 1000.0).toFloat()

    private fun bitrateLabel(): String {
        val v = bitrates[bitrateIdx]
        return "Битрейт: " + (if (v == 0) "авто" else "$v Мбит/с")
    }

    private fun aspectLabel(): String = "Формат: " + arrayOf("4:3", "16:9", "20:9")[aspectMode]

    private fun updateLabels() {
        tvIso.text = "ISO: " + currentIso()
        val exp = currentExp()
        tvExp.text = if (exp >= 300_000_000L) String.format("Выдержка: %.2f с", exp / 1e9)
        else "Выдержка: 1/" + (1_000_000_000.0 / exp).toInt() + " с"
        val total = sbStack.progress + 2
        val frames = min(300L, max(1L, total * 1_000_000_000L / exp))
        tvStack.text = "Долгая выдержка: " + total + " с (кадров: " + frames + ")"
        val br = boostRange
        if (br != null && br.upper > 100) {
            tvBoost.text = "Цифровое усиление: " + currentBoost() + "% (ISO ≈ " + (currentIso() * currentBoost() / 100) + ")"
        }
        val f = currentFocus()
        val dist = if (f < 0.01f) "бесконечность" else String.format("%.1f см", 100f / f)
        tvFocus.text = String.format("Фокус: %.1f дптр (%s)", f, dist)
        tvZoom.text = String.format("Зум: %.1fx", currentZoom())
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

    private fun applyControls(b: CaptureRequest.Builder, record: Boolean) {
        applyZoom(b)
        applyProcessing(b)
        if (cbExp.isChecked && isoRange != null && expRange != null) {
            val exp = currentExp()
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_OFF)
            b.set(CaptureRequest.SENSOR_SENSITIVITY, currentIso())
            b.set(CaptureRequest.SENSOR_EXPOSURE_TIME, exp)
            b.set(CaptureRequest.SENSOR_FRAME_DURATION, max(exp, 33_333_333L))
            val br = boostRange
            if (br != null && br.upper > 100) {
                b.set(CaptureRequest.CONTROL_POST_RAW_SENSITIVITY_BOOST, currentBoost())
            }
        } else {
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_ON)
        }
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
    }

    private fun updateRepeating() {
        val b = builder ?: return
        val s = session ?: return
        try {
            applyControls(b, recording)
            s.setRepeatingRequest(b.build(), null, handler)
        } catch (e: Exception) {
            log("Ошибка обновления: $e")
        }
    }

    // ---------- открытие камеры ----------

    private fun closeAll() {
        try { session?.close() } catch (_: Exception) {}
        try { device?.close() } catch (_: Exception) {}
        try { imageReader?.close() } catch (_: Exception) {}
        try { persistentSurface?.release() } catch (_: Exception) {}
        persistentSurface = null
        sessionHasRecorder = false
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

    private fun sizesFor(sizes: Array<Size>?): List<Size> {
        if (sizes == null) return emptyList()
        val target = doubleArrayOf(4.0 / 3.0, 16.0 / 9.0, 20.0 / 9.0)[aspectMode]
        return sizes
            .filter { Math.abs(it.width.toDouble() / it.height - target) < 0.02 }
            .sortedByDescending { it.width * it.height }
    }

    private fun computeSizes() {
        val map = streamMap ?: return
        previewSize = sizesFor(map.getOutputSizes(SurfaceTexture::class.java)).firstOrNull() ?: previewSize
        videoCandidates = sizesFor(map.getOutputSizes(MediaRecorder::class.java))
        videoSize = videoCandidates.firstOrNull() ?: videoSize
        photoSize = sizesFor(map.getOutputSizes(ImageFormat.JPEG)).firstOrNull() ?: photoSize
        log(aspectLabel() + ": превью $previewSize, видео $videoSize, фото $photoSize")
        updateTransform()
    }

    private fun displayDegrees(): Int {
        val rotation = windowManager.defaultDisplay.rotation
        return when (rotation) {
            Surface.ROTATION_90 -> 90
            Surface.ROTATION_180 -> 180
            Surface.ROTATION_270 -> 270
            else -> 0
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
                val rot = windowManager.defaultDisplay.rotation
                if (rot == Surface.ROTATION_90 || rot == Surface.ROTATION_270) {
                    // TextureView показывает кадр как в портрете: снимаем растяжение,
                    // вписываем в экран и поворачиваем в альбомную ориентацию
                    val viewRect = RectF(0f, 0f, vw, vh)
                    val bufRect = RectF(0f, 0f, ph, pw)
                    bufRect.offset(cx - bufRect.centerX(), cy - bufRect.centerY())
                    m.setRectToRect(viewRect, bufRect, Matrix.ScaleToFit.FILL)
                    val scale = min(vh / ph, vw / pw)
                    m.postScale(scale, scale, cx, cy)
                    m.postRotate(90f * (rot - 2), cx, cy)
                } else if (rot == Surface.ROTATION_180) {
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
        if (recording || stacking) { log("Сначала остановите запись или долгую выдержку"); return }
        aspectMode = (aspectMode + 1) % 3
        usePersistent = true
        btnAspect.text = aspectLabel()
        savePrefs()
        if (device != null) {
            try { session?.close() } catch (_: Exception) {}
            session = null
            computeSizes()
            makeReader()
            startPreview()
        } else {
            computeSizes()
        }
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

        try {
            makeReader()

            cm.openCamera(id, object : CameraDevice.StateCallback() {
                override fun onOpened(camera: CameraDevice) {
                    log("ОТКРЫЛАСЬ: ID $id")
                    opening = false
                    device = camera
                    startPreview()
                }
                override fun onDisconnected(camera: CameraDevice) {
                    log("Отключена"); opening = false; device = null; camera.close()
                }
                override fun onError(camera: CameraDevice, error: Int) {
                    log("Ошибка камеры, код $error"); opening = false; device = null; camera.close()
                }
            }, handler)
        } catch (e: Exception) {
            opening = false
            log("openCamera не удалось: $e")
        }
    }

    private fun updateModeUi() {
        btnMode.text = if (mode == 0) "Режим: Фото" else "Режим: Видео"
        val photo = mode == 0
        btnPhoto.visibility = if (photo) View.VISIBLE else View.GONE
        btnStack.visibility = if (photo) View.VISIBLE else View.GONE
        btnRec.visibility = if (photo) View.GONE else View.VISIBLE
        updatePauseUi()
    }

    private fun updatePauseUi() {
        runOnUiThread {
            btnPause.visibility = if (mode == 1 && recording) View.VISIBLE else View.GONE
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
        s("nr", btnNr.text.toString())
        s("edge", btnEdge.text.toString())
        s("bitrate", btnBitrate.text.toString())
        s("torch", btnTorch.text.toString())
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
                            "nr" -> btnNr.performClick()
                            "edge" -> btnEdge.performClick()
                            "bitrate" -> btnBitrate.performClick()
                            "torch" -> btnTorch.performClick()
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

    private fun openGallery() {
        if (recording || stacking) { log("Сначала остановите запись или долгую выдержку"); return }
        val u = lastMediaUri ?: prefs.getString("lastUri", null)?.let { Uri.parse(it) }
        val mime = lastMediaMime ?: prefs.getString("lastMime", null)
        try {
            if (u != null) {
                val i = Intent(Intent.ACTION_VIEW)
                i.setDataAndType(u, mime ?: "*/*")
                i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                startActivity(i)
            } else {
                startActivity(Intent.makeMainSelectorActivity(Intent.ACTION_MAIN, Intent.CATEGORY_APP_GALLERY))
            }
        } catch (e: Exception) {
            log("Не удалось открыть галерею: $e")
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

    private fun toggleTorch() {
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
        if (recording || stacking) { log("Сначала остановите запись или долгую выдержку"); return }
        if (rampActive) { log("Подождите, линза встаёт на место"); return }
        mode = 1 - mode
        savePrefs()
        updateModeUi()
        if (device != null) startPreview()
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
                t.setVideoEncoder(MediaRecorder.VideoEncoder.H264)
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
            val st = texture.surfaceTexture!!
            st.setDefaultBufferSize(previewSize.width, previewSize.height)
            val surface = Surface(st)
            previewSurface = surface
            focusOverride = if (cbFocus.isChecked && minFocus > 0f) 0f else null
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
            b.addTarget(surface)
            applyControls(b, false)
            builder = b
            previewBuilder = b
            val targets = ArrayList<Surface>()
            targets.add(surface)
            var ps: Surface? = null
            if (mode == 1) {
                if (usePersistent) ps = createPersistentSurface()
                if (ps != null) targets.add(ps)
            } else {
                imageReader?.let { targets.add(it.surface) }
            }
            val hasRec = ps != null
            cam.createCaptureSession(targets, object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    sessionHasRecorder = hasRec
                    try {
                        s.setRepeatingRequest(b.build(), null, handler)
                        log("Режим " + (if (mode == 0) "«Фото»" else "«Видео»") + ": превью запущено")
                    } catch (e: Exception) {
                        log("Ошибка запроса: $e")
                    }
                    startFocusRamp { log("Линза на месте, можно снимать") }
                }
                override fun onConfigureFailed(s: CameraCaptureSession) {
                    if (hasRec) {
                        log("Сессия с видео не настроилась, запись будет с перенастройкой камеры")
                        usePersistent = false
                        try { persistentSurface?.release() } catch (_: Exception) {}
                        persistentSurface = null
                        startPreview()
                    } else {
                        log("Сессия не настроилась")
                    }
                }
            }, handler)
        } catch (e: Exception) {
            log("Ошибка превью: $e")
        }
    }

    // ---------- фото ----------

    private fun takePhoto() {
        val cam = device
        val s = session
        val reader = imageReader
        if (cam == null || s == null || reader == null) { log("Сначала откройте камеру"); return }
        if (recording) { log("Во время записи фото недоступно"); return }
        if (stacking) { log("Идёт долгая выдержка"); return }
        if (mode != 0) { log("Переключите режим на «Фото»"); return }
        if (rampActive) { log("Подождите, линза встаёт на место"); return }
        try {
            pendingInfo = shotInfo()
            pendingTag = fileTag()
            pendingExpSec = if (cbExp.isChecked) currentExp() / 1e9 else null
            pendingIso = if (cbExp.isChecked) currentIso() else null
            val fNow = currentFocus()
            pendingDist = if (cbFocus.isChecked && fNow > 0.01f) 1.0 / fNow else null
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_STILL_CAPTURE)
            b.addTarget(reader.surface)
            applyControls(b, false)
            b.set(CaptureRequest.JPEG_ORIENTATION, outputRotation())
            s.capture(b.build(), object : CameraCaptureSession.CaptureCallback() {
                override fun onCaptureCompleted(
                    session: CameraCaptureSession,
                    request: CaptureRequest,
                    result: TotalCaptureResult
                ) {
                    log("Снимок сделан")
                }
                override fun onCaptureFailed(
                    session: CameraCaptureSession,
                    request: CaptureRequest,
                    failure: CaptureFailure
                ) {
                    log("Снимок не удался")
                }
            }, handler)
        } catch (e: Exception) {
            log("Ошибка фото: $e")
        }
    }

    private fun savePhoto(
        bytes: ByteArray,
        rotation: Int = -1,
        info: String? = null,
        expSec: Double? = null,
        iso: Int? = null,
        distM: Double? = null,
        tag: String? = null
    ) {
        try {
            val name = "macro_" + stamp() + (if (tag != null) "_$tag" else "")
            val values = ContentValues().apply {
                put(MediaStore.Images.Media.DISPLAY_NAME, "$name.jpg")
                put(MediaStore.Images.Media.MIME_TYPE, "image/jpeg")
                put(MediaStore.Images.Media.RELATIVE_PATH, "Pictures/MacroCam")
            }
            val uri = contentResolver.insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, values)
            if (uri == null) { log("Не удалось создать файл фото"); return }
            contentResolver.openOutputStream(uri)?.use { it.write(bytes) }
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
            rememberLast(uri, "image/jpeg")
            log("Фото сохранено: Pictures/MacroCam")
        } catch (e: Exception) {
            log("Ошибка сохранения фото: $e")
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
        runOnUiThread { btnStack.text = "Долгая" }
    }

    private fun startStack() {
        if (stacking) {
            stackCancel = true
            log("Останавливаю, обработаю уже снятые кадры...")
            return
        }
        val cam = device
        if (cam == null) { log("Сначала откройте камеру"); return }
        if (recording) { log("Остановите запись"); return }
        if (mode != 0) { log("Переключите режим на «Фото»"); return }
        if (rampActive) { log("Подождите, линза встаёт на место"); return }
        if (!cbExp.isChecked || isoRange == null || expRange == null) {
            log("Включите «Ручные ISO и выдержка» и задайте выдержку одного кадра")
            return
        }
        val exp = currentExp()
        val totalNs = (sbStack.progress + 2) * 1_000_000_000L
        var n = (totalNs / exp).toInt()
        if (n < 1) n = 1
        if (n > 300) { n = 300; log("Кадров слишком много, ограничено до 300") }
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
        stackCancel = false
        stackSum = cbStackSum.isChecked
        try {
            val reader = ImageReader.newInstance(stackW, stackH, ImageFormat.YUV_420_888, 3)
            reader.setOnImageAvailableListener({ r -> onStackImage(r) }, handler)
            stackReader = reader
            stacking = true
            runOnUiThread { btnStack.text = "Стоп 0/$n" }

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
            applyControls(b, false)
            builder = b
            cam.createCaptureSession(listOf(pSurface, reader.surface), object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    log("Долгая выдержка: $n кадров, режим " + (if (stackSum) "сумма" else "среднее"))
                    startFocusRamp { captureStackFrame() }
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

    private fun captureStackFrame() {
        val cam = device
        val s = session
        val reader = stackReader
        val ps = stackSurface
        if (cam == null || s == null || reader == null || ps == null) return
        try {
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_STILL_CAPTURE)
            b.addTarget(reader.surface)
            b.addTarget(ps)
            applyControls(b, false)
            s.capture(b.build(), null, handler)
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
        runOnUiThread { btnStack.text = "Стоп $cnt/$tgt" }
        if (stackCancel || cnt >= tgt) finishStack() else captureStackFrame()
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
        yuv.compressToJpeg(Rect(0, 0, w, h), 95, out)
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
                    savePhoto(
                        jpeg, outputRotation(),
                        shotInfo(n, stackFrameExpNs),
                        n * stackFrameExpNs / 1e9,
                        if (cbExp.isChecked) currentIso() else null,
                        if (cbFocus.isChecked && fNow > 0.01f) 1.0 / fNow else null,
                        fileTag(n, stackFrameExpNs)
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
        if (stacking) { log("Идёт долгая выдержка"); return }
        if (device == null) { log("Камера ещё не открыта"); return }
        if (mode != 1) { log("Переключите режим на «Видео»"); return }
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
            sess.setRepeatingRequest(pb.build(), null, handler)
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
            val values = ContentValues().apply {
                put(MediaStore.Video.Media.DISPLAY_NAME, videoName() + ".mp4")
                put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                put(MediaStore.Video.Media.RELATIVE_PATH, "Movies/MacroCam")
            }
            val uri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
            if (uri == null) { log("Не удалось создать файл видео"); return }
            videoUri = uri
            val fd = contentResolver.openFileDescriptor(uri, "w")
            if (fd == null) { log("Не удалось открыть файл видео"); return }
            pfd = fd

            val fixed = bitrates[bitrateIdx]
            val br = if (fixed > 0) fixed * 1_000_000
            else (videoSize.width.toLong() * videoSize.height * 30 * 0.15).toLong()
                .coerceIn(8_000_000L, 50_000_000L).toInt()
            val r = MediaRecorder()
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
            r.setVideoEncoder(MediaRecorder.VideoEncoder.H264)
            r.setVideoEncodingBitRate(br)
            r.setVideoFrameRate(30)
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
            sess.setRepeatingRequest(rb.build(), null, handler)
            r.start()
            recording = true
            recordingPersistent = true
            btnRec.text = "Стоп"
            updatePauseUi()
            log("ЗАПИСЬ ИДЁТ: " + videoSize.width + "x" + videoSize.height + ", " + (br / 1_000_000) + " Мбит/с")
        } catch (e: Exception) {
            log("Ошибка записи: $e")
            cleanupRecorder()
            recording = false
            recordingPersistent = false
            btnRec.text = "Запись"
            updatePauseUi()
            restorePreview()
        }
    }

    private fun stopRecordingPersistent() {
        restorePreview()
        try { recorder?.stop() } catch (e: Exception) { log("stop: $e") }
        cleanupRecorder()
        finishVideoFile()
        recording = false
        recordingPersistent = false
        btnRec.text = "Запись"
        updatePauseUi()
        log("Видео сохранено: Movies/MacroCam")
    }

    private fun startRecordingLegacy() {
        val cam = device
        if (cam == null) { log("Сначала откройте камеру"); return }
        if (stacking) { log("Идёт долгая выдержка"); return }
        try {
            val values = ContentValues().apply {
                put(MediaStore.Video.Media.DISPLAY_NAME, videoName() + ".mp4")
                put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                put(MediaStore.Video.Media.RELATIVE_PATH, "Movies/MacroCam")
            }
            val uri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
            if (uri == null) { log("Не удалось создать файл видео"); return }
            videoUri = uri
            val fd = contentResolver.openFileDescriptor(uri, "w")
            if (fd == null) { log("Не удалось открыть файл видео"); return }
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
                    t.setVideoEncoder(MediaRecorder.VideoEncoder.H264)
                    val fixed = bitrates[bitrateIdx]
                    val br = if (fixed > 0) fixed * 1_000_000
                    else (sz.width.toLong() * sz.height * 30 * 0.15).toLong()
                        .coerceIn(8_000_000L, 50_000_000L).toInt()
                    t.setVideoEncodingBitRate(br)
                    t.setVideoFrameRate(30)
                    t.setVideoSize(sz.width, sz.height)
                    t.setOrientationHint(outputRotation())
                    t.prepare()
                    made = t
                    videoSize = sz
                    log("Видео: " + sz.width + "x" + sz.height + ", " + (br / 1_000_000) + " Мбит/с")
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
                return
            }
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
            cam.createCaptureSession(listOf(pSurface, rSurface), object : CameraCaptureSession.StateCallback() {
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
                    }
                }
                override fun onConfigureFailed(s: CameraCaptureSession) {
                    log("Сессия записи не настроилась")
                    cleanupRecorder()
                }
            }, handler)
        } catch (e: Exception) {
            log("Ошибка записи: $e")
            cleanupRecorder()
        }
    }

    private fun stopRecording() {
        if (recordingPersistent) { stopRecordingPersistent(); return }
        try { session?.stopRepeating() } catch (_: Exception) {}
        try { session?.abortCaptures() } catch (_: Exception) {}
        try { recorder?.stop() } catch (e: Exception) { log("stop: $e") }
        cleanupRecorder()
        finishVideoFile()
        recording = false
        btnRec.text = "Запись"
        updatePauseUi()
        log("Видео сохранено: Movies/MacroCam")
        startPreview()
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

    override fun onResume() {
        super.onResume()
        hideSystemUi()
        updateTransform()
        tryAutoOpen()
    }

    override fun onPause() {
        savePrefs()
        if (saveMode) setSaveMode(false)
        if (stacking) {
            stacking = false
            cleanupStack()
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
<div class="row"><button id="bMode">Режим</button></div>
<div class="row"><button id="bPhoto">Фото</button><button id="bStack">Долгая</button></div>
<div class="row"><button id="bRec">Запись</button><button id="bPause">Пауза</button></div>
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
<label><input type="checkbox" id="cSum"> Суммировать (ярче)</label>
<label><input type="checkbox" id="cFlip"> Перевернуть 180°</label>
<button id="bAspect">Формат</button>
<button id="bNr">Шумоподавление</button>
<button id="bEdge">Контуры</button>
<button id="bBit">Битрейт</button>
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
    G('bMode').textContent = s.modeBtn;
    G('bPhoto').style.display = s.mode === 0 ? '' : 'none';
    G('bStack').style.display = s.mode === 0 ? '' : 'none';
    G('bRec').style.display = s.mode === 1 ? '' : 'none';
    G('bPause').style.display = (s.mode === 1 && s.rec) ? '' : 'none';
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
    G('cFlip').checked = s.flip; G('cSum').checked = s.stackSum;
    G('bAspect').textContent = s.aspect;
    G('bNr').textContent = s.nr;
    G('bEdge').textContent = s.edge;
    G('bBit').textContent = s.bitrate;
    G('bTorch').textContent = s.torch;
    G('v').style.transform = s.flip ? 'rotate(180deg)' : '';
    G('loupe').style.transform = s.flip ? 'translate(-50%,-50%) rotate(180deg)' : 'translate(-50%,-50%)';
    G('log').textContent = s.log;
  }).catch(function(){});
}
slider('sZoom', 'zoom'); slider('sIso', 'iso'); slider('sExp', 'exp');
slider('sFocus', 'focus'); slider('sBoost', 'boost'); slider('sStack', 'stack');
check('cExp', 'manExp'); check('cFocus', 'manFocus'); check('cFlip', 'flip'); check('cSum', 'stackSum');
bindClick('bMode', 'mode'); bindClick('bPhoto', 'photo'); bindClick('bStack', 'stack');
bindClick('bRec', 'rec'); bindClick('bPause', 'pause'); bindClick('bAspect', 'aspect');
bindClick('bNr', 'nr'); bindClick('bEdge', 'edge'); bindClick('bBit', 'bitrate'); bindClick('bTorch', 'torch');

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
