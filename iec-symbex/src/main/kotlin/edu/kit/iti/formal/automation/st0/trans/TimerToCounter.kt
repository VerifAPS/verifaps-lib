package edu.kit.iti.formal.automation.st0.trans

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.TimeType
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.datatypes.values.TimeData
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.STSimplifier
import edu.kit.iti.formal.automation.visitors.Visitable
import java.math.BigInteger

/**
 * @author Alexander Weigl (06.07.2014), Augusto Modanese
 * @version 1
 */
class TimerToCounter(private val cycleTime: Long) : AstMutableVisitor() {

    fun defaultVisit(visitable: Visitable): Any {
        return visitable
    }

    override fun visit(vd: VariableDeclaration): VariableDeclaration {
        if (vd.dataType === TimeType.TIME_TYPE) {

            val newVariable = VariableDeclaration(vd.name, vd.type, UINT)
            var cycles = if (vd.init != null) {
                val value = (vd.init as Literal).asValue()
                val data = value!!.value as TimeData
                BigInteger.valueOf((data.milliseconds / cycleTime).toLong())
            } else {
                BigInteger.ZERO
            }

            val newVal = IntegerLit(UINT, cycles)
            val sd = SimpleTypeDeclaration()
            sd.initialization = newVal
            sd.baseType.obj = UINT
            //setPositions(vd.getInit(), sd);
            newVariable.typeDeclaration = sd
            return newVariable
        }
        return super.visit(vd)
    }

    override fun visit(literal: Literal) =
            when (literal) {
                is TimeLit -> {
                    val value = literal.asValue()
                    val data = value.value
                    val cycles = (data.milliseconds / this.cycleTime).toInt()
                    IntegerLit(UINT, cycles.toBigInteger())
                }
                else -> super.visit(literal)
            }


    companion object {
        var DEFAULT_CYCLE_TIME: Long = 4

        val INSTANCE = object : ST0Transformation {
            override fun transform(state: STSimplifier.State) {
                val ttc = TimerToCounter(DEFAULT_CYCLE_TIME)
                state.theProgram = ttc.visit(state.theProgram!!) as ProgramDeclaration?
                for (function in state.functions.values)
                    state.functions.replace(function.name, ttc.visit(function) as FunctionDeclaration)
            }
        }
    }

}
