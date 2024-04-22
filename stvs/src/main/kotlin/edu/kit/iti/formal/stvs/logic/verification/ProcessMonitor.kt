package edu.kit.iti.formal.stvs.logic.verification

import javafx.beans.property.*
import tornadofx.getValue
import tornadofx.setValue
import java.io.IOException
import java.util.*
import java.util.concurrent.TimeUnit

/**
 * Detects when a process is finished and invokes the associated listeners. Adapted from
 * https://beradrian.wordpress.com/2008/11/03/detecting-process-exit-in-java/.
 *
 * @author Benjamin Alt
 */
class ProcessMonitor(process: Process?, timeout: Int) : Thread() {
    /**
     * The process for which we have to detect the end.
     */
    var process: Process? = null

    val processFinishedProperty: BooleanProperty = SimpleBooleanProperty(false)
    var finished by processFinishedProperty

    private var timeout = 0
    var isAborted: Boolean = false
        private set
    var error: Exception? = null

    /**
     * Starts the detection for the given process.
     *
     * @param process the process for which one would like to detect when it is finished
     * @param timeout Timeout after which the process is killed automatically
     */
    init {
        try {
            /* Test if the process is finished */
            process!!.exitValue()
            throw IllegalArgumentException("The process has already finished.")
        } catch (exc: IllegalThreadStateException) {
            this.process = process
            this.timeout = timeout
        }
    }

    /**
     * runs an external process and wait until `timeout` or until it is interrupted.
     */
    override fun run() {
        isAborted = false
        val process = this.process!!
        try {
            // wait for the process to finish
            if (!process.waitFor(timeout.toLong(), TimeUnit.SECONDS)) {
                process.destroy()
                isAborted = true
            }
            if (process.exitValue() != 0) {
                val errorOut = process.errorStream.reader().readText()
                error = IOException("Process ended with error ${process.exitValue()} and error output: $errorOut")
            }
            processFinishedProperty.set(true)
        } catch (e: InterruptedException) {
            // intentionally left empty. Process is destroyed somewhere else
        } catch (e: IOException) {
            error = e
            e.printStackTrace()
            processFinishedProperty.set(true)
        }
    }
}
