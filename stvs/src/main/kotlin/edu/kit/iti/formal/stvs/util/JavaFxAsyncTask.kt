/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.util

import javafx.application.Platform
import java.util.*

/**
 * A Thread that executes an [AsyncRunner] and calls a [AsyncTaskCompletedHandler] after
 * completion. The handler is always called within the JavaFX main thread.
 *
 * @author Leon Kaucher
 */
class JavaFxAsyncTask<T>(timeout: Int, runner: AsyncRunner<T>, resultHandler: AsyncTaskCompletedHandler<T>) : Thread() {
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
        processTerminatorTask.schedule(
            object : TimerTask() {
                override fun run() {
                    terminate()
                }
            },
            (timeout * 1000).toLong(),
        )
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