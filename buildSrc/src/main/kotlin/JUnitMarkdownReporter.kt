import org.gradle.api.DefaultTask
import org.gradle.api.file.ConfigurableFileTree
import org.gradle.api.file.RegularFileProperty
import org.gradle.api.provider.Property
import org.gradle.api.tasks.*
import org.w3c.dom.NodeList
import java.io.File
import javax.xml.parsers.DocumentBuilderFactory
import javax.xml.xpath.XPathConstants
import javax.xml.xpath.XPathFactory

/**
 * A Task reading JUnit XML reports and generating a simple Markdown report for GitHub workflows.
 *
 * @author Alexander Weigl
 * @version 1 (2025-12-26)
 */
abstract class JUnitMarkdownReporter : DefaultTask() {
    @get:InputFiles
    @get:PathSensitive(PathSensitivity.RELATIVE)
    abstract val testReports: Property<ConfigurableFileTree>

    @get:OutputFile
    abstract val outputFile: RegularFileProperty

    private val builderFactory = DocumentBuilderFactory.newInstance()
    private val builder = builderFactory.newDocumentBuilder()
    private val xPath = XPathFactory.newInstance().newXPath()

    private val xpathFailingTestcases = "/testsuite/testcase[./error|./failure]"
    private val xpathCFailingTestcases = xPath.compile(xpathFailingTestcases)

    private val xpathNumberTests = "/testsuite/@tests"
    private val xpathCNumberTests = xPath.compile(xpathNumberTests)

    init {
        val pathname = System.getenv("GITHUB_STEP_SUMMARY") ?: "build/reports/junit.md"
        outputFile.set(File(pathname))
    }

    @TaskAction
    fun run() {
        val errors = arrayListOf<String>()
        outputFile.get().asFile.bufferedWriter().use { writer ->
            var cntFiles = 0
            var testCases = 0
            testReports.get().forEach { file ->
                testCases += process(file, errors)
                cntFiles++
            }

            if (errors.isNotEmpty()) {
                writer.write(errors.joinToString("\n") { "* $it" })
            } else {
                writer.write("No errors in $cntFiles JUnit files. Found $testCases tests.")
            }
        }
    }

    private fun process(file: File, errors: MutableList<String>): Int {
        val xmlDocument = builder.parse(file)
        val testCount = xpathCNumberTests.evaluate(xmlDocument, XPathConstants.NUMBER) as Number

        val nodeList = xpathCFailingTestcases.evaluate(xmlDocument, XPathConstants.NODESET) as NodeList?
        if (nodeList != null && errors.isNotEmpty()) {
            for (i in 0 until nodeList.length) {
                val node = nodeList.item(i)
                val name = node.attributes.getNamedItem("name").nodeValue
                val classname = node.attributes.getNamedItem("classname").nodeValue
                val time = node.attributes.getNamedItem("time").nodeValue
                val error = node.firstChild
                errors.add("Error: $classname#$name in $time")
            }
        }
        return testCount.toInt()
    }
}