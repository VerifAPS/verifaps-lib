/*-
 * #%L
 * aps-rvt
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */
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
