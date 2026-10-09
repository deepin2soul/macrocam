package com.example.macrocam

import android.Manifest
import android.app.Activity
import android.app.AlertDialog
import android.content.ClipData
import android.content.ClipboardManager
import android.content.ContentValues
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.graphics.ImageFormat
import android.graphics.Matrix
import android.graphics.Rect
import android.graphics.SurfaceTexture
import android.hardware.camera2.*
import android.hardware.camera2.params.StreamConfigurationMap
import android.media.CamcorderProfile
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
import android.widget.Button
import android.widget.CheckBox
import android.widget.EditText
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import kotlin.math.max
import kotlin.math.min
import kotlin.math.pow

class MainActivity : Activity() {

    private lateinit var prefs: SharedPreferences
    private lateinit var cm: CameraManager
    private lateinit var texture: TextureView
    private lateinit var logView: TextView
    private lateinit var logScroll: ScrollView
    private lateinit var idInput: EditText
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
    private var wide = false
    private var previewSize = Size(640, 480)
    private var videoSize = Size(1280, 720)
    private var photoSize = Size(1280, 960)

    private var recorder: MediaRecorder? = null
    private var pfd: ParcelFileDescriptor? = null
    @Volatile private var recording = false

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)

        prefs = getSharedPreferences("macro", MODE_PRIVATE)
        cm = getSystemService(CAMERA_SERVICE) as CameraManager
        texture = findViewById(R.id.texture)
        logView = findViewById(R.id.log)
        logScroll = findViewById(R.id.logScroll)
        idInput = findViewById(R.id.idInput)
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
        sbZoom = findViewById(R.id.sbZoom)
        tvZoom = findViewById(R.id.tvZoom)
        thread = HandlerThread("cam").also { it.start() }
        handler = Handler(thread.looper)

        // восстановить сохранённые настройки
        idInput.setText(prefs.getString("id", "3"))
        sbIso.progress = prefs.getInt("iso", 200)
        sbExp.progress = prefs.getInt("exp", 500)
        sbFocus.progress = prefs.getInt("focus", 800)
        cbExp.isChecked = prefs.getBoolean("manExp", false)
        cbFocus.isChecked = prefs.getBoolean("manFocus", false)
        cbFlip.isChecked = prefs.getBoolean("flip", false)
        sbZoom.progress = prefs.getInt("zoom", 0)
        wide = prefs.getBoolean("wide", false)
        btnAspect.text = aspectLabel()
        texture.rotation = if (cbFlip.isChecked) 180f else 0f
        texture.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ -> updateTransform() }

        findViewById<Button>(R.id.btnList).setOnClickListener { showList() }
        findViewById<Button>(R.id.btnData).setOnClickListener { showData(idInput.text.toString().trim()) }
        findViewById<Button>(R.id.btnOpen).setOnClickListener {
            openById(idInput.text.toString().trim())
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
        btnAspect.setOnClickListener { toggleAspect() }
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
            .putString("id", idInput.text.toString().trim())
            .putInt("iso", sbIso.progress)
            .putInt("exp", sbExp.progress)
            .putInt("focus", sbFocus.progress)
            .putBoolean("manExp", cbExp.isChecked)
            .putBoolean("manFocus", cbFocus.isChecked)
            .putBoolean("flip", cbFlip.isChecked)
            .putInt("zoom", sbZoom.progress)
            .putBoolean("wide", wide)
            .apply()
    }

    private fun log(s: String) {
        runOnUiThread {
            logView.append(s + "\n")
            logScroll.post { logScroll.fullScroll(ScrollView.FOCUS_DOWN) }
        }
    }

    private fun showList() {
        try {
            log("getCameraIdList: " + cm.cameraIdList.joinToString(", "))
        } catch (e: Exception) {
            log("Ошибка списка: $e")
        }
    }

    // ---------- отчёт о камере ----------

    private fun ratioLabel(s: Size): String {
        val r = s.width.toDouble() / s.height
        return when {
            Math.abs(r - 4.0 / 3.0) < 0.01 -> "4:3"
            Math.abs(r - 16.0 / 9.0) < 0.01 -> "16:9"
            Math.abs(r - 3.0 / 2.0) < 0.01 -> "3:2"
            Math.abs(r - 1.0) < 0.01 -> "1:1"
            Math.abs(r - 2.0) < 0.01 -> "2:1"
            Math.abs(r - 20.0 / 9.0) < 0.01 -> "20:9"
            else -> String.format("%.3f", r)
        }
    }

    private fun fmtSizes(sizes: Array<Size>?): String {
        if (sizes == null || sizes.isEmpty()) return "  нет"
        return sizes.sortedByDescending { it.width * it.height }
            .joinToString("\n") { "  " + it.width + "x" + it.height + " (" + ratioLabel(it) + ")" }
    }

    private fun buildReport(id: String): String {
        val sb = StringBuilder()
        sb.append("Camera ID: ").append(id).append("\n")
        sb.append("Android API: ").append(Build.VERSION.SDK_INT).append(", ")
            .append(Build.MANUFACTURER).append(" ").append(Build.MODEL).append("\n")
        try {
            val c = cm.getCameraCharacteristics(id)
            fun line(name: String, v: Any?) {
                sb.append(name).append(": ").append(v).append("\n")
            }
            line("HARDWARE_LEVEL", c.get(CameraCharacteristics.INFO_SUPPORTED_HARDWARE_LEVEL))
            line("SENSOR_ORIENTATION", c.get(CameraCharacteristics.SENSOR_ORIENTATION))
            line("LENS_FACING", c.get(CameraCharacteristics.LENS_FACING))
            line("ACTIVE_ARRAY_SIZE", c.get(CameraCharacteristics.SENSOR_INFO_ACTIVE_ARRAY_SIZE))
            line("PIXEL_ARRAY_SIZE", c.get(CameraCharacteristics.SENSOR_INFO_PIXEL_ARRAY_SIZE))
            line("PHYSICAL_SIZE (мм)", c.get(CameraCharacteristics.SENSOR_INFO_PHYSICAL_SIZE))
            line("FOCAL_LENGTHS", c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_FOCAL_LENGTHS)?.joinToString())
            line("APERTURES", c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_APERTURES)?.joinToString())
            line("MIN_FOCUS_DISTANCE (дптр)", c.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE))
            line("AF режимы", c.get(CameraCharacteristics.CONTROL_AF_AVAILABLE_MODES)?.joinToString())
            line("FPS диапазоны", c.get(CameraCharacteristics.CONTROL_AE_AVAILABLE_TARGET_FPS_RANGES)?.joinToString())
            line("Макс. цифровой зум", c.get(CameraCharacteristics.SCALER_AVAILABLE_MAX_DIGITAL_ZOOM))
            if (Build.VERSION.SDK_INT >= 30) {
                line("ZOOM_RATIO_RANGE", c.get(CameraCharacteristics.CONTROL_ZOOM_RATIO_RANGE))
            }
            line("CROPPING_TYPE", c.get(CameraCharacteristics.SCALER_CROPPING_TYPE))
            line("Возможности", c.get(CameraCharacteristics.REQUEST_AVAILABLE_CAPABILITIES)?.joinToString())
            line("ISO", c.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE))
            line("Выдержка (нс)", c.get(CameraCharacteristics.SENSOR_INFO_EXPOSURE_TIME_RANGE))

            val map = c.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)
            if (map != null) {
                sb.append("\nФорматы вывода: ").append(map.outputFormats.joinToString()).append("\n")
                sb.append("\nПревью (SurfaceTexture):\n").append(fmtSizes(map.getOutputSizes(SurfaceTexture::class.java)))
                sb.append("\n\nВидео (MediaRecorder):\n").append(fmtSizes(map.getOutputSizes(MediaRecorder::class.java)))
                sb.append("\n\nФото (JPEG):\n").append(fmtSizes(map.getOutputSizes(ImageFormat.JPEG)))
                sb.append("\n\nYUV_420_888:\n").append(fmtSizes(map.getOutputSizes(ImageFormat.YUV_420_888)))
                sb.append("\n")
            }
        } catch (e: Exception) {
            sb.append("Характеристики недоступны: ").append(e).append("\n")
        }
        try {
            val n = id.toInt()
            sb.append("\nCamcorderProfile (старый API):\n")
            val q = listOf(
                "HIGH" to CamcorderProfile.QUALITY_HIGH,
                "2160P" to CamcorderProfile.QUALITY_2160P,
                "1080P" to CamcorderProfile.QUALITY_1080P,
                "720P" to CamcorderProfile.QUALITY_720P
            )
            for ((name, quality) in q) {
                if (CamcorderProfile.hasProfile(n, quality)) {
                    val p = CamcorderProfile.get(n, quality)
                    if (p != null) {
                        sb.append("  ").append(name).append(": ")
                            .append(p.videoFrameWidth).append("x").append(p.videoFrameHeight)
                            .append(", ").append(p.videoFrameRate).append(" fps, ")
                            .append(p.videoBitRate).append(" bps\n")
                    }
                } else {
                    sb.append("  ").append(name).append(": нет\n")
                }
            }
        } catch (e: Exception) {
            sb.append("CamcorderProfile недоступен: ").append(e).append("\n")
        }
        return sb.toString()
    }

    private fun showData(id: String) {
        if (id.isEmpty()) { log("Введите ID"); return }
        val report = buildReport(id)
        val tv = TextView(this)
        tv.text = report
        tv.textSize = 12f
        tv.setTextIsSelectable(true)
        tv.setPadding(24, 24, 24, 24)
        val sv = ScrollView(this)
        sv.addView(tv)
        AlertDialog.Builder(this)
            .setTitle("Данные камеры $id")
            .setView(sv)
            .setPositiveButton("Копировать") { _, _ ->
                val cmgr = getSystemService(CLIPBOARD_SERVICE) as ClipboardManager
                cmgr.setPrimaryClip(ClipData.newPlainText("camera", report))
                log("Скопировано в буфер обмена")
            }
            .setNegativeButton("Закрыть", null)
            .show()
    }

    // ---------- значения ползунков ----------

    private fun currentIso(): Int {
        val r = isoRange ?: return 100
        return (r.lower + (r.upper - r.lower) * (sbIso.progress / 1000.0)).toInt()
    }

    private fun currentExp(): Long {
        val r = expRange ?: return 10_000_000L
        val lo = r.lower.toDouble()
        val hi = min(r.upper, 66_666_666L).toDouble()
        return (lo * (hi / lo).pow(sbExp.progress / 1000.0)).toLong()
    }

    private fun currentFocus(): Float = sbFocus.progress / 1000f * minFocus

    private fun currentZoom(): Float =
        maxZoom.toDouble().pow(sbZoom.progress / 1000.0).toFloat()

    private fun aspectLabel(): String = "Формат: " + (if (wide) "9:16" else "3:4")

    private fun updateLabels() {
        tvIso.text = "ISO: " + currentIso()
        val exp = currentExp()
        tvExp.text = "Выдержка: 1/" + (1_000_000_000.0 / exp).toInt() + " с"
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

    private fun applyControls(b: CaptureRequest.Builder, record: Boolean) {
        applyZoom(b)
        if (cbExp.isChecked && isoRange != null && expRange != null) {
            val exp = currentExp()
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_OFF)
            b.set(CaptureRequest.SENSOR_SENSITIVITY, currentIso())
            b.set(CaptureRequest.SENSOR_EXPOSURE_TIME, exp)
            b.set(CaptureRequest.SENSOR_FRAME_DURATION, max(exp, 33_333_333L))
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
        try {
            val c = cm.getCameraCharacteristics(id)
            chars = c
            isoRange = c.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE)
            expRange = c.get(CameraCharacteristics.SENSOR_INFO_EXPOSURE_TIME_RANGE)
            minFocus = c.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE) ?: 0f
            log("ISO $isoRange, выдержка $expRange нс, мин. фокус $minFocus дптр")

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
        runOnUiThread { updateLabels() }
    }

    private fun pick(sizes: Array<Size>?, maxW: Int, maxH: Int, fallback: Size): Size {
        if (sizes == null) return fallback
        val target = if (wide) 16.0 / 9.0 else 4.0 / 3.0
        val fit = sizes.filter { it.width <= maxW && it.height <= maxH }
        val inRatio = fit.filter { Math.abs(it.width.toDouble() / it.height - target) < 0.03 }
        val best = inRatio.maxByOrNull { it.width * it.height }
            ?: fit.maxByOrNull { it.width * it.height }
        return best ?: fallback
    }

    private fun computeSizes() {
        val map = streamMap ?: return
        previewSize = pick(map.getOutputSizes(SurfaceTexture::class.java), 1280, 960, previewSize)
        videoSize = pick(map.getOutputSizes(MediaRecorder::class.java), 1920, 1080, videoSize)
        photoSize = pick(map.getOutputSizes(ImageFormat.JPEG), Int.MAX_VALUE, Int.MAX_VALUE, photoSize)
        log(aspectLabel() + ": превью $previewSize, видео $videoSize, фото $photoSize")
        updateTransform()
    }

    private fun updateTransform() {
        runOnUiThread {
            val vw = texture.width.toFloat()
            val vh = texture.height.toFloat()
            if (vw > 0f && vh > 0f) {
                val ca = previewSize.width.toFloat() / previewSize.height
                val va = vw / vh
                val m = Matrix()
                if (va > ca) m.setScale((vh * ca) / vw, 1f, vw / 2f, vh / 2f)
                else m.setScale(1f, (vw / ca) / vh, vw / 2f, vh / 2f)
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
        if (recording) { log("Сначала остановите запись"); return }
        wide = !wide
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

    private fun openById(id: String) {
        if (id.isEmpty()) { log("Введите ID"); return }
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
            log("Нет разрешения на камеру"); return
        }
        if (!texture.isAvailable) { log("Превью не готово, повторите"); return }
        if (recording) { log("Сначала остановите запись"); return }

        savePrefs()
        closeAll()
        log("--- Открываю ID $id ---")
        readCharacteristics(id)

        try {
            makeReader()

            cm.openCamera(id, object : CameraDevice.StateCallback() {
                override fun onOpened(camera: CameraDevice) {
                    log("ОТКРЫЛАСЬ: ID $id")
                    device = camera
                    startPreview()
                }
                override fun onDisconnected(camera: CameraDevice) {
                    log("Отключена"); camera.close()
                }
                override fun onError(camera: CameraDevice, error: Int) {
                    log("Ошибка камеры, код $error"); camera.close()
                }
            }, handler)
        } catch (e: Exception) {
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
        try {
            val b = cam.createCaptureRequest(CameraDevice.TEMPLATE_STILL_CAPTURE)
            b.addTarget(reader.surface)
            applyControls(b, false)
            b.set(CaptureRequest.JPEG_ORIENTATION, if (cbFlip.isChecked) 180 else 0)
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

    private fun savePhoto(bytes: ByteArray) {
        try {
            val values = ContentValues().apply {
                put(MediaStore.Images.Media.DISPLAY_NAME, "macro_" + System.currentTimeMillis() + ".jpg")
                put(MediaStore.Images.Media.MIME_TYPE, "image/jpeg")
                put(MediaStore.Images.Media.RELATIVE_PATH, "Pictures/MacroCam")
            }
            val uri = contentResolver.insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, values)
            if (uri == null) { log("Не удалось создать файл фото"); return }
            contentResolver.openOutputStream(uri)?.use { it.write(bytes) }
            log("Фото сохранено: Pictures/MacroCam")
        } catch (e: Exception) {
            log("Ошибка сохранения фото: $e")
        }
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

            val r = MediaRecorder()
            r.setVideoSource(MediaRecorder.VideoSource.SURFACE)
            r.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
            r.setOutputFile(fd.fileDescriptor)
            r.setVideoEncoder(MediaRecorder.VideoEncoder.H264)
            r.setVideoEncodingBitRate(12_000_000)
            r.setVideoFrameRate(30)
            r.setVideoSize(videoSize.width, videoSize.height)
            r.setOrientationHint(if (cbFlip.isChecked) 180 else 0)
            r.prepare()
            recorder = r

            val st = texture.surfaceTexture!!
            st.setDefaultBufferSize(previewSize.width, previewSize.height)
            val pSurface = Surface(st)
            val rSurface = r.surface
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
                        r.start()
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

    override fun onPause() {
        savePrefs()
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
