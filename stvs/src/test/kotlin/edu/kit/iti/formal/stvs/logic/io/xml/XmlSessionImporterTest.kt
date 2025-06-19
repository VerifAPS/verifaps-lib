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
package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class XmlSessionImporterTest {
    @Test
    fun testDoImportValid1() {
        val importedSession: StvsRootModel = ImporterFacade.importSession(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/session_valid_with_concrete_instance_1.xml")!!,
            GlobalConfig(),
            History(),
        )
        val hybridSpec: HybridSpecification = ImporterFacade.importHybridSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml")!!,
        )

        val typeContext = listOf(TypeInt, TypeBool, enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml")!!,
            typeContext,
        )
        hybridSpec.concreteInstance = concreteSpec
        Assertions.assertEquals(hybridSpec, importedSession.hybridSpecifications[0])
        val code =
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/code_valid_1.st")!!
                .reader().readText()

        Assertions.assertEquals(
            code.replace("\\s+".toRegex(), " ").trim(),
            importedSession.scenario.code.sourcecode.replace("\\s+".toRegex(), " ").trim(),
        )
    }
}