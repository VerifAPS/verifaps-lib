package edu.kit.iti.formal

import edu.kit.iti.formal.automation.rvt.*
import edu.kit.iti.formal.smv.SMVFacade
import org.junit.Test
import java.io.File

class SimpleTest {
    @Test fun testSimple(): Unit {
        main(arrayOf(
                "--old", "src/test/resources/simple1_old.st",
                "--new", "src/test/resources/simple1_new.st",
                "-o", "target/test-output"
        ))
    }

    @Test fun testUntilMiter(): Unit {
        var pipe: TransformationPipeline = TransformationPipeline(false)
        val om = pipe.run("src/test/resources/simple1_old.st")
        val nm = pipe.run("src/test/resources/simple1_new.st")
        val gm = GloballyMiter(om, nm)
        val um = UntilMiter(om, nm, gm)
        um.event(SMVFacade.expr("n_i<0sd16_2"))
        val rv = ReVeWithMiter(om, nm, um)
        rv.run()
        val writer = File("target/test-output/miter.smv").bufferedWriter()
        rv.writeTo(writer)
        writer.close()
    }
}
