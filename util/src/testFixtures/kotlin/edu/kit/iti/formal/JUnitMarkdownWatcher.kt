package edu.kit.iti.formal

import org.junit.jupiter.api.extension.AfterAllCallback
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.api.extension.TestWatcher
import java.io.FileWriter
import java.io.PrintWriter
import java.util.*
import kotlin.jvm.optionals.getOrNull

/**
 * A Task reading JUnit XML reports and generating a simple Markdown report for GitHub workflows.
 *
 * @author Alexander Weigl
 * @version 1 (2025-12-26)
 */
class JUnitMarkdownWatcher :
    TestWatcher,
    AfterAllCallback {
    private val markdownFile: PrintWriter

    init {
        val file = System.getenv("GITHUB_STEP_SUMMARY") ?: "junit.md"
        markdownFile = PrintWriter(FileWriter(file), true)
    }

    override fun testAborted(context: ExtensionContext, cause: Throwable?) {
        markdownFile.println("* **aborted** ${context.displayName}: ${cause?.javaClass} '${cause?.message}'")
    }

    override fun testDisabled(context: ExtensionContext, reason: Optional<String>) {
        markdownFile.println("* **disabled** ${context.displayName}: reason: ${reason.getOrNull() ?: ""}")
    }

    override fun testFailed(context: ExtensionContext, cause: Throwable?) {
        markdownFile.println("* **failed** ${context.displayName}: ${cause?.javaClass} '${cause?.message}'")
    }

    override fun testSuccessful(context: ExtensionContext) {
    }

    override fun afterAll(context: ExtensionContext) {
        markdownFile.close()
    }
}