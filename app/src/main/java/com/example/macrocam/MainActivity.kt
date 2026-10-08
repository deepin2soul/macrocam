package com.example.macrocam

import android.Manifest
import android.app.Activity
import android.content.pm.PackageManager
import android.graphics.SurfaceTexture
import android.hardware.camera2.*
import android.os.Bundle
import android.os.Handler
import android.os.HandlerThread
import android.util.Size
import android.view.Surface
import android.view.TextureView
import android.widget.Button
import android.widget.EditText
import android.widget.TextView


class MainActivity : Activity() {

    private lateinit var cm: CameraManager
    private lateinit var texture: TextureView
    private lateinit var logView: TextView
    private lateinit var idInput: EditText
    private lateinit var thread: HandlerThread
    private lateinit var handler: Handler
    private var device: CameraDevice? = null
    private var session: CameraCaptureSession? = null

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)

        cm = getSystemService(CAMERA_SERVICE) as CameraManager
        texture = findViewById(R.id.texture)
        logView = findViewById(R.id.log)
        idInput = findViewById(R.id.idInput)
        thread = HandlerThread("cam").also { it.start() }
        handler = Handler(thread.looper)

        findViewById<Button>(R.id.btnList).setOnClickListener { showList() }
        findViewById<Button>(R.id.btnOpen).setOnClickListener {
            openById(idInput.text.toString().trim())
        }

        if (checkSelfPermission(Manifest.permission.CAMERA)
            != PackageManager.PERMISSION_GRANTED
        ) {
            requestPermissions(arrayOf(Manifest.permission.CAMERA), 1)
        }
    }

    private fun log(s: String) {
        runOnUiThread { logView.append(s + "\n") }
    }

    private fun showList() {
        try {
            log("getCameraIdList: " + cm.cameraIdList.joinToString(", "))
        } catch (e: Exception) {
            log("Ошибка списка: $e")
        }
    }

    private fun closeAll() {
        try { session?.close() } catch (_: Exception) {}
        try { device?.close() } catch (_: Exception) {}
        session = null
        device = null
    }

    private fun logCharacteristics(id: String): Size {
        var size = Size(640, 480)
        try {
            val c = cm.getCameraCharacteristics(id)
            log("Характеристики ID $id доступны")
            log("MIN_FOCUS_DISTANCE: " + c.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE))
            log("ISO: " + c.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE))
            log("Выдержка (нс): " + c.get(CameraCharacteristics.SENSOR_INFO_EXPOSURE_TIME_RANGE))
            log("Уровень: " + c.get(CameraCharacteristics.INFO_SUPPORTED_HARDWARE_LEVEL))
            val map = c.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)
            val sizes = map?.getOutputSizes(SurfaceTexture::class.java)
            val best = sizes?.filter { it.width <= 1280 && it.height <= 960 }
                ?.maxByOrNull { it.width * it.height }
            if (best != null) size = best
        } catch (e: Exception) {
            log("Характеристики ID $id недоступны: $e")
        }
        log("Размер превью: $size")
        return size
    }

    private fun openById(id: String) {
        if (id.isEmpty()) { log("Введите ID"); return }
        if (checkSelfPermission(Manifest.permission.CAMERA)
            != PackageManager.PERMISSION_GRANTED
        ) { log("Нет разрешения на камеру"); return }
        if (!texture.isAvailable) { log("Экран превью ещё не готов, повторите"); return }

        closeAll()
        log("--- Открываю ID $id ---")
        val size = logCharacteristics(id)

        try {
            cm.openCamera(id, object : CameraDevice.StateCallback() {
                override fun onOpened(camera: CameraDevice) {
                    log("ОТКРЫЛАСЬ: ID $id")
                    device = camera
                    startPreview(camera, size)
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

    private fun startPreview(camera: CameraDevice, size: Size) {
        try {
            val st = texture.surfaceTexture!!
            st.setDefaultBufferSize(size.width, size.height)
            val surface = Surface(st)
            val req = camera.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
            req.addTarget(surface)
            camera.createCaptureSession(listOf(surface), object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(s: CameraCaptureSession) {
                    session = s
                    try {
                        s.setRepeatingRequest(req.build(), null, handler)
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

    override fun onDestroy() {
        closeAll()
        thread.quitSafely()
        super.onDestroy()
    }
}
