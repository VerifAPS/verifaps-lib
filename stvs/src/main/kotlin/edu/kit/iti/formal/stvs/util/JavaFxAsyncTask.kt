package edu.kit.iti.formal.stvs.util

import javafx.application.Platform
import java.util.*

/**
 * A Thread that executes an [AsyncRunner] and calls a [AsyncTaskCompletedHandler] after
 * completion. The handler is always called within the JavaFX main thread.
 *
 * @author Leon Kaucher
 */
class JavaFxAsyncTask<T>(
    timeout: Int, runner: AsyncRunner<T>,
    resultHandler: AsyncTaskCompletedHandler<T>
) : Thread() {
    private val runner: AsyncRunner<T>
    private val resultHandler: AsyncTaskCompletedHandler<T>
    private val processTerminatorTask: Timer

    /**
     * Constructor for an asynchronous task.
     *
     * @param timeout time before the runner will be terminated
     * @param runner The portion of action to be run asynchronously (a functional interface).
     * @param resultHandler The portion of the action to be run synchronously (in javafx's EDT) with
     * any other AsyncTasks.
     */
    init {
        isDaemon = true
        this.runner = runner
        this.resultHandler = resultHandler
        this.processTerminatorTask = Timer()
        processTerminatorTask.schedule(object : TimerTask() {
            override fun run() {
                terminate()
            }
        }, (timeout * 1000).toLong())
    }

    /**
     * Interrupts this thread and terminates the process that the runner is depending on.
     */
    fun terminate() {
        processTerminatorTask.cancel()
        this.interrupt()
        runner.terminate()
    }

    override fun run() {
        try {
            val result = runner.run()
            Platform.runLater { resultHandler.onSuccess(result) }
        } catch (exception: Exception) {
            Platform.runLater { resultHandler.onException(exception) }
        } finally {
            processTerminatorTask.cancel()
        }
    }
}
