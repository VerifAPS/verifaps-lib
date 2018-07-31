/**
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl></weigl>@kit.edu>
 *
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
 * <http:></http:>//www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io.xmv


import edu.kit.iti.formal.automation.testtables.io.Report
import edu.kit.iti.formal.automation.testtables.model.VerificationTechnique
import org.junit.Assert
import org.junit.Assume
import org.junit.Test

import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
class NuXmvTest {
    @Test
    fun simpleSuccessRun() {
        val p = NuXMVProcess(
                VerificationTechnique.IC3.commands,
                File("src/test/resources/success.smv").absoluteFile,
                File("target/test"),
                File("success.log"))

        Assume.assumeTrue(p.executablePath.startsWith("/"))

        p.run()
        Report.close()
        Assert.assertTrue(p.isVerified)
    }

    @Test
    fun simpleSuccessCE() {
        val p = NuXMVProcess(
                VerificationTechnique.IC3.commands,
                File("src/test/resources/counterexample.smv").absoluteFile,
                File("target/test").absoluteFile,
                File("error.log"))

        Assume.assumeTrue(p.executablePath.startsWith("/"))
        p.run()
        Report.XML_MODE = true
        Report.close()
        Assert.assertFalse(p.isVerified)
    }
}
