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
