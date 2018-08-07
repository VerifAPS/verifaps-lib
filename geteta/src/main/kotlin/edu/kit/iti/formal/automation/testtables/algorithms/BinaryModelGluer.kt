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
package edu.kit.iti.formal.automation.testtables.algorithms

import edu.kit.iti.formal.automation.testtables.model.options.TableOptions
import edu.kit.iti.formal.smv.ModuleType
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
class BinaryModelGluer(private val options: TableOptions,
                       private val tableModule: SMVModule,
                       private val tableType: ModuleType,
                       private val code: List<SMVModule>,
                       private val programRunNames: List<String>) : Runnable {
    val product = SMVModule("main")

    override fun run() {
        product.name = MAIN_MODULE
        product.inputVars.addAll(code.flatMap { it.moduleParameters })

        programRunNames.zip(code).forEach { (name, code) ->
            product.stateVars.add(
                    SVariable(name,
                            ModuleType(code.name, code.moduleParameters)))
        }

        product.stateVars.add(SVariable(TABLE_MODULE,tableType))
    }

    companion object {
        val TABLE_MODULE = "tableModule"
        val MAIN_MODULE = "main"
    }
}
