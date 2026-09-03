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
package edu.kit.iti.formal.lsp

import org.eclipse.lsp4j.services.LanguageClient
import org.eclipse.lsp4j.services.LanguageServer
import org.slf4j.LoggerFactory
import java.util.concurrent.CompletableFuture
import java.util.concurrent.ForkJoinPool
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

abstract class MyLanguageServer : LanguageServer {
    internal val LOGGER = LoggerFactory.getLogger("key-lsp")

    val executorService: ForkJoinPool = ForkJoinPool.commonPool()
    
    abstract var client: LanguageClient

    override fun shutdown(): CompletableFuture<Any> {
        executorService.shutdown()
        val c = executorService.awaitTermination(5, TimeUnit.SECONDS)
        val i = executorService.shutdownNow()
        return CompletableFuture.completedFuture("Finish: Waited 5 seconds. $c, ${i.size} jobs killed.")
    }

    override fun exit() {
        shutdown()
        exitProcess(0)
    }
}