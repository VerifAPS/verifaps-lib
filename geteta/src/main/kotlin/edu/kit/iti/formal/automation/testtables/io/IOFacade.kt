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


import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.smv.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.File

/**
 * Created by weigl on 10.12.16.
 */
object IOFacade {
    fun createParser(input: CharStream): TestTableLanguageParser {
        val lexer = TestTableLanguageLexer(input)
        lexer.removeErrorListeners()
        lexer.addErrorListener(ThrowingErrorListener.INSTANCE)

        val parser = TestTableLanguageParser(CommonTokenStream(lexer))

        parser.removeErrorListeners()
        parser.addErrorListener(ThrowingErrorListener.INSTANCE)

        return parser
    }

    fun createParser(input: String) = createParser(CharStreams.fromString(input))

    /**
     * @param cell
     * @param column
     * @param vars
     * @return
     */
    fun parseCellExpression(cell: String, column: SVariable,
                            vars: GeneralizedTestTable): SMVExpr {
        val p = createParser(cell).cell()
        val ev = ExprVisitor(column, vars)
        val expr = p.accept(ev)
        Report.debug("parsed: %s to %s", cell, expr)
        return expr
    }


    fun parseCellExpression(cell: TestTableLanguageParser.CellContext, column: SVariable,
                            vars: GeneralizedTestTable): SMVExpr {
        val ev = ExprVisitor(column, vars)
        val expr = cell.accept(ev)
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

    fun asSMVVariable(column: edu.kit.iti.formal.automation.testtables.model.Variable): SVariable {
        return SVariable(column.name, getSMVDataType(column.dataType))
    }

    private fun getSMVDataType(dataType: AnyDt): SMVType {
        return DefaultTypeTranslator.INSTANCE.translate(dataType)
                ?: error("Data type $dataType is not supported by DataTypeTranslator")
    }


    @JvmStatic
    fun parseTable(input: String) = parseTable(CharStreams.fromString(input))

    @JvmStatic
    fun parseTable(input: File) = parseTable(CharStreams.fromFileName(input.absolutePath))

    @JvmStatic
    fun parseTable(input: CharStream): GeneralizedTestTable {
        val parser = createParser(input)
        val ctx = parser.file()
        val ttlb = TestTableLanguageBuilder()
        ctx.accept(ttlb)
        return ttlb.testTables.get(0)
    }
}
