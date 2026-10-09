package com.example.macrocam

import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.content.ClipData
import android.content.ClipboardManager
import android.content.ContentValues
import android.content.SharedPreferences
import android.content.pm.ActivityInfo
import android.content.pm.PackageManager
import android.graphics.ImageFormat
import android.graphics.Matrix
import android.graphics.Rect
import android.graphics.YuvImage
import android.graphics.RectF
import android.graphics.SurfaceTexture
import android.hardware.camera2.*
import android.hardware.camera2.params.StreamConfigurationMap
import android.media.CamcorderProfile
import android.media.ExifInterface
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
import android.view.TextureView
import android.view.View
import android.view.WindowInsets
import android.view.WindowInsetsController
import android.view.WindowManager
import android.widget.Button
import android.widget.CheckBox
import android.widget.EditText
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import java.io.ByteArrayOutputStream
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
    private var boostRange: Range<Int>? = null
    private var maxFrameDuration: Long = Long.MAX_VALUE
    private lateinit var btnStack: Button
    private lateinit var cbNoNr: CheckBox
    private lateinit var cbNoProc: CheckBox
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

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        requestedOrientation = ActivityInfo.SCREEN_ORIENTATION_LANDSCAPE
        if (Build.VERSION.SDK_INT >= 28) {
            val lp = window.attributes
            lp.layoutInDisplayCutoutMode =
                WindowManager.LayoutParams.LAYOUT_IN_DISPLAY_CUTOUT_MODE_SHORT_EDGES
            window.attributes = lp
        }
        setContentView(R.layout.activity_main)
        hideSystemUi()

        prefs = getSharedPreferences("macro", MODE_PRIVATE)
        cm = getSystemService(CAMERA_SERVICE) as CameraManager
        texture = findViewById(R.id.texture)
        logView = findViewById(R.id.log)
        logScroll = findViewById(R.id.logScroll)
        sbIso = findViewById(R.id.sbIso)
        sbExp = findViewById(R.id.sbExp)
        sbFocus = findViewById(R.id.sbFocus)
        tvIso = findViewById(R.id.tvIso)
        tvExp = findViewById(R.id.tvExp)
        tvFocus = findViewById(R.id.tvFocus)
        cbExp = findViewById(R.id.cbExp)
        cbFocus = findViewById(R.id.cbFocus)
        cbFlip = findViewById(R.id.cbFlip)
        btnRec = findViewById(R.id.btnRec)
        btnAspect = findViewById(R.id.btnAspect)
        panel = findViewById(R.id.panel)
        btnPanel = findViewById(R.id.btnPanel)
        sbZoom = findViewById(R.id.sbZoom)
        btnStack = findViewById(R.id.btnStack)
        cbNoNr = findViewById(R.id.cbNoNr)
        cbNoProc = findViewById(R.id.cbNoProc)
        btnBitrate = findViewById(R.id.btnBitrate)
        sbStack = findViewById(R.id.sbStack)
        tvStack = findViewById(R.id.tvStack)
        cbStackSum = findViewById(R.id.cbStackSum)
        sbBoost = findViewById(R.id.sbBoost)
        tvBoost = findViewById(R.id.tvBoost)
        tvZoom = findViewById(R.id.tvZoom)
        thread = HandlerThread("cam").also { it.start() }
        handler = Handler(thread.looper)

        // восстановить сохранённые настройки
        sbIso.progress = prefs.getInt("iso", 200)
        sbExp.progress = prefs.getInt("exp", 500)
        sbFocus.progress = prefs.getInt("focus", 200)
        sbStack.progress = prefs.getInt("stack", 28)
        cbStackSum.isChecked = prefs.getBoolean("stackSum", true)
        sbBoost.progress = prefs.getInt("boost", 0)
        cbNoNr.isChecked = prefs.getBoolean("noNr", false)
        cbNoProc.isChecked = prefs.getBoolean("noProc", false)
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

        findViewById<Button>(R.id.btnPhoto).setOnClickListener { takePhoto() }
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
        cbNoNr.setOnCheckedChangeListener { _, _ -> savePrefs(); updateRepeating() }
        cbNoProc.setOnCheckedChangeListener { _, _ -> savePrefs(); updateRepeating() }
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

        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(arrayOf(Manifest.permission.CAMERA), 1)
        }
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
            .putBoolean("noNr", cbNoNr.isChecked)
            .putBoolean("noProc", cbNoProc.isChecked)
            .putInt("bitrate", bitrateIdx)
            .putInt("aspect", aspectMode)
            .apply()
    }

    private fun log(s: String) {
        runOnUiThread {
            logView.append(s + "\n")
            logScroll.post { logScroll.fullScroll(ScrollView.FOCUS_DOWN) }
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
        val hi = max(min(r.upper, maxFrameDuration), r.lower + 1).toDouble()
        return (lo * (hi / lo).pow(sbExp.progress / 1000.0)).toLong()
    }

    private fun currentBoost(): Int {
        val r = boostRange ?: return 100
        return (r.lower + (r.upper - r.lower) * (sbBoost.progress / 1000.0)).toInt()
    }

    private fun currentFocus(): Float = (1f - sbFocus.progress / 1000f) * minFocus

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

    private fun applyProcessing(b: CaptureRequest.Builder) {
        val c = chars ?: return
        if (cbNoNr.isChecked) {
            val m = c.get(CameraCharacteristics.NOISE_REDUCTION_AVAILABLE_NOISE_REDUCTION_MODES)
            if (m != null && m.contains(CameraMetadata.NOISE_REDUCTION_MODE_OFF)) {
                b.set(CaptureRequest.NOISE_REDUCTION_MODE, CameraMetadata.NOISE_REDUCTION_MODE_OFF)
            }
        }
        if (cbNoProc.isChecked) {
            val e = c.get(CameraCharacteristics.EDGE_AVAILABLE_EDGE_MODES)
            if (e != null && e.contains(CameraMetadata.EDGE_MODE_OFF)) {
                b.set(CaptureRequest.EDGE_MODE, CameraMetadata.EDGE_MODE_OFF)
            }
            val v = c.get(CameraCharacteristics.CONTROL_AVAILABLE_VIDEO_STABILIZATION_MODES)
            if (v != null && v.contains(CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_OFF)) {
                b.set(CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE,
                    CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_OFF)
            }
            val o = c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_OPTICAL_STABILIZATION)
            if (o != null && o.contains(CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_OFF)) {
                b.set(CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE,
                    CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_OFF)
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
            b.set(CaptureRequest.LENS_FOCUS_DISTANCE, currentFocus())
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
                    savePhoto(bytes)
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

    private fun startPreview() {
        val cam = device ?: return
        try {
            try { session?.close() } catch (_: Exception) {}
            session = null
            val st = texture.surfaceTexture!!
            st.setDefaultBufferSize(previewSize.width, previewSize.height)
            val surface = Surface(st)
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
            b.addTarget(surface)
            applyControls(b, false)
            builder = b
            val targets = ArrayList<Surface>()
            targets.add(surface)
            imageReader?.let { targets.add(it.surface) }
            cam.createCaptureSession(targets, object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    try {
                        s.setRepeatingRequest(b.build(), null, handler)
                        log("ПРЕВЬЮ ЗАПУЩЕНО")
                    } catch (e: Exception) {
                        log("Ошибка запроса: $e")
                    }
                }
                override fun onConfigureFailed(s: CameraCaptureSession) {
                    log("Сессия не настроилась")
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
        try {
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

    private fun savePhoto(bytes: ByteArray, rotation: Int = -1) {
        try {
            val values = ContentValues().apply {
                put(MediaStore.Images.Media.DISPLAY_NAME, "macro_" + System.currentTimeMillis() + ".jpg")
                put(MediaStore.Images.Media.MIME_TYPE, "image/jpeg")
                put(MediaStore.Images.Media.RELATIVE_PATH, "Pictures/MacroCam")
            }
            val uri = contentResolver.insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, values)
            if (uri == null) { log("Не удалось создать файл фото"); return }
            contentResolver.openOutputStream(uri)?.use { it.write(bytes) }
            if (rotation >= 0) {
                val rw = contentResolver.openFileDescriptor(uri, "rw")
                if (rw != null) {
                    rw.use {
                        val exif = ExifInterface(it.fileDescriptor)
                        val o = when (rotation) {
                            90 -> ExifInterface.ORIENTATION_ROTATE_90
                            180 -> ExifInterface.ORIENTATION_ROTATE_180
                            270 -> ExifInterface.ORIENTATION_ROTATE_270
                            else -> ExifInterface.ORIENTATION_NORMAL
                        }
                        exif.setAttribute(ExifInterface.TAG_ORIENTATION, o.toString())
                        exif.saveAttributes()
                    }
                }
            }
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
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
            b.addTarget(pSurface)
            applyControls(b, false)
            builder = b
            cam.createCaptureSession(listOf(pSurface, reader.surface), object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    log("Долгая выдержка: $n кадров, режим " + (if (stackSum) "сумма" else "среднее"))
                    captureStackFrame()
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
        try {
            if (n == 0) {
                log("Кадров нет")
            } else {
                log("Обработка $n кадров...")
                val jpeg = buildStackJpeg(n)
                if (jpeg != null) savePhoto(jpeg, outputRotation()) else log("Нет данных")
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
        val cam = device
        if (cam == null) { log("Сначала откройте камеру"); return }
        if (stacking) { log("Идёт долгая выдержка"); return }
        try {
            val values = ContentValues().apply {
                put(MediaStore.Video.Media.DISPLAY_NAME, "macro_" + System.currentTimeMillis() + ".mp4")
                put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                put(MediaStore.Video.Media.RELATIVE_PATH, "Movies/MacroCam")
            }
            val uri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
            if (uri == null) { log("Не удалось создать файл видео"); return }
            val fd = contentResolver.openFileDescriptor(uri, "w")
            if (fd == null) { log("Не удалось открыть файл видео"); return }
            pfd = fd

            val cands = if (videoCandidates.isEmpty()) listOf(videoSize) else videoCandidates.take(4)
            var made: MediaRecorder? = null
            for (sz in cands) {
                val t = MediaRecorder()
                try {
                    t.setVideoSource(MediaRecorder.VideoSource.SURFACE)
                    t.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
                    t.setOutputFile(fd.fileDescriptor)
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
            cam.createCaptureSession(listOf(pSurface, rSurface), object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    try {
                        s.setRepeatingRequest(b.build(), null, handler)
                        rec.start()
                        recording = true
                        runOnUiThread { btnRec.text = "Стоп" }
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
        try { session?.stopRepeating() } catch (_: Exception) {}
        try { session?.abortCaptures() } catch (_: Exception) {}
        try { recorder?.stop() } catch (e: Exception) { log("stop: $e") }
        cleanupRecorder()
        recording = false
        btnRec.text = "Запись"
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
        if (stacking) {
            stacking = false
            cleanupStack()
        }
        if (recording) stopRecording()
        closeAll()
        super.onPause()
    }

    override fun onDestroy() {
        closeAll()
        thread.quitSafely()
        super.onDestroy()
    }
}
