/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
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
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.monitor

/*-
 * #%L
 * geteta
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

import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import java.util.concurrent.Callable

/**
 * @author Alexander Weigl
 * @version 1 (23.03.17)
 */
class MonitorGeneration(internal val gtt: GeneralizedTestTable) : Callable<PouElements> {
    internal val fb = FunctionBlockDeclaration()

    @Throws(Exception::class)
    override fun call(): PouElements {
        val vars = fb.scope.builder()
        vars.push(VariableDeclaration.INPUT)

        // IOVariables -> VAR_INPUT
        gtt.ioVariables.forEach { v ->
            //vars.identifiers(v.name)
            //        .baseType(v.dataType).create()
        }

        // VAR_OUTPUT WARNING : BOOL; END_VAR
        vars.clear().push(VariableDeclaration.OUTPUT).identifiers("WARNING")
                .baseType("BOOL").close()

        for (i in 0 until gtt.region!!.count()) {
            vars.identifiers(String.format("ROW_%2d", i)).baseType("BOOL").close()
        }

        return PouElements(mutableListOf(fb))
    }
}
