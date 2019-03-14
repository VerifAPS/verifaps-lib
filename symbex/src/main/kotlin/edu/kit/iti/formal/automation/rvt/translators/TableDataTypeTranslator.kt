package edu.kit.iti.formal.automation.rvt.translators

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*

/**
 * @author Alexander Weigl
 */
class TableDataTypeTranslator : TypeTranslator {
    /**
     */
    private val map = HashMap<AnyDt, SMVType>()

    /**
     *
     */
    val integerMap: Map<String, Int> = HashMap()

    private val dttFallback = DefaultTypeTranslator()

    /**
     *
     *
     */
    override fun translate(datatype: AnyDt): SMVType {
        return map.computeIfAbsent(datatype, { dttFallback.translate(it)!! })
    }

    /**
     * {@inheritDoc}
     *
     * @param vdecl
     * @return
     */
    override fun translate(vdecl: VariableDeclaration): SVariable {
        val i = integerMap[vdecl.name]
        if (i != null) {
            return if (i == 0) SVariable.create(vdecl.name).asBool() else SVariable.create(vdecl.name)
                    .with(if (i < 0) SMVTypes.unsigned(-i)
                    else SMVTypes.signed(i))
        } else {
            return SVariable.create(vdecl.name).with(translate(vdecl.dataType!!))
        }
    }
}
