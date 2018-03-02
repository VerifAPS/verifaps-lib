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
package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionLexer
import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionParser
import edu.kit.iti.formal.automation.testtables.io.IOFacade.getSMVDataType
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.schema.DataType
import edu.kit.iti.formal.automation.testtables.schema.Variable
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SMVType
import edu.kit.iti.formal.smv.ast.SVariable
import org.antlr.v4.runtime.ANTLRInputStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

/**
 * Created by weigl on 10.12.16.
 */
object IOFacade {
    fun createParser(input: String?): CellExpressionParser {
        assert(input != null)
        val lexer = CellExpressionLexer(CharStreams.fromString(input!!))
        lexer.removeErrorListeners()
        lexer.addErrorListener(ThrowingErrorListener.INSTANCE)

        val parser = CellExpressionParser(CommonTokenStream(lexer))

        parser.removeErrorListeners()
        parser.addErrorListener(ThrowingErrorListener.INSTANCE)

        return parser
    }

    /**
     * @param cell
     * @param column
     * @param vars
     * @return
     */
    fun parseCellExpression(cell: String?, column: SVariable,
                            vars: GeneralizedTestTable): SMVExpr {
        assert(cell != null)
        val p = createParser(cell).cell()
        val ev = ExprVisitor(column, vars)
        val expr = p.accept(ev)
        Report.debug("parsed: %s to %s", cell, expr)
        return expr
    }

    fun parseDuration(duration: String): Duration {
        if (duration.equals("omega", ignoreCase = true)) {
            return Duration.OMEGA
        }

        if (duration.equals("wait", ignoreCase = true)) {
            return Duration.DET_WAIT
        }


        val parser = createParser(duration)
        val p = parser.fixed_interval()
        val d = Duration()
        if (p.c != null) {
            val i = Integer.parseInt(p.c.text)
            d.lower = i
            d.upper = i
        } else if (p.dc != null) {
            d.lower = 0
            d.upper = -1
        } else {
            d.lower = Integer.parseInt(p.a.text)
            if (p.inf != null)
                d.upper = -1
            else
                d.upper = Integer.parseInt(p.b.text)
        }
        assert(parser.numberOfSyntaxErrors == 0)
        assert(d.invariant())
        return d
    }

    fun asSMVVariable(column: Variable?): SVariable? {
        return if (column == null) null else SVariable(column.name,
                getSMVDataType(column.dataType))
    }

    private fun getSMVDataType(dataType: DataType): SMVType {
        return DataTypeTranslator.INSTANCE.apply(dataType)
    }
}
