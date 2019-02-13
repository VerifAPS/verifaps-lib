import edu.kit.iti.formal.util.findProgram
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (22.11.18)
 */
class RunExamples {
    @TestFactory
    fun runExamples() =
            createExample("Scenario3v1_Final.xml", "Scenario5v1_Final.xml", "Crane", "Magazin", "Stamp") +
                    createExample("Scenario5v1_Final.xml", "Scenario7v1_Final.xml", "Crane", "Magazin", "Stamp") +
                    createExample("Scenario7_Final.xml", "Scenario8_Final.xml", "Crane", "Magazin", "Stamp") +
                    createExample("Scenario8_Final.xml", "Scenario9_Final.xml", "Crane", "Magazin", "Stamp") +
                    createExample("E3.A.st", "E3.B.st", "A") +
                    createExample("E1.A.st", "E1.B.st", "A") +
                    createExample("Scenario9_Final.xml", "Scenario10_Final.xml", "Crane", "Magazin", "Stamp")

    fun createExample(left: String, right: String, vararg pou: String) =
            pou.map { p ->
                DynamicTest.dynamicTest("$p/$left/$right") {
                    val a = AbstractIntEqSfc(p,
                            File("examples/$left"),
                            File("examples/$right"),
                            File("examples/$left.$right.$p.dot"))
                    Assumptions.assumeTrue(a.leftFile.exists() && a.rightFile.exists())
                    a.run()
                    val dot = findProgram("dot")
                    if (dot != null) {
                        ProcessBuilder(dot.absolutePath, "-Tsvg", "-o", "$left.$right.$p.svg", "$left.$right.$p.dot")
                                .inheritIO()
                                .directory(File("examples"))
                                .start()
                    }
                }
            }
}