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
package edu.kit.iti.formal.automation.testtables

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2017 - 2018 Alexander Weigl
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

import com.google.common.base.Strings
import com.google.common.collect.ImmutableList
import edu.kit.iti.formal.automation.st.util.Tuple
import edu.kit.iti.formal.automation.testtables.algorithms.LatexPrinter
import edu.kit.iti.formal.automation.testtables.io.IOFacade
import edu.kit.iti.formal.automation.testtables.io.TableReader
import edu.kit.iti.formal.automation.testtables.model.*
import org.antlr.v4.runtime.misc.ParseCancellationException
import org.apache.commons.cli.CommandLine
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.ParseException
import org.w3c.dom.Element
import java.util.*
import javax.xml.bind.JAXBException

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
object PrintTable {
    private const val DONT_CARE = "\\DONTCARE"
    private val durations = Stack<Tuple<Duration, Int>>()
    private var table: GeneralizedTestTable? = null
    private var currentRow = 0
    private var input: List<IoVariable>? = null
    private var output: List<IoVariable>? = null
    private val cache = HashMap<String, String>()
    private val drawLines = LinkedHashMap<String, String>()
    private val markCounter = Counter()
    private val lastTikzMarkColumn = HashMap<String, Int>()
    private val specialChars = ImmutableList.of("_", "^", "~", "$", "%", "#", "&", "{", "}")
    private var totalNumSteps: Int = 0
    private val columns = LinkedHashMap<String, ArrayList<String>>()

    @Throws(ParseException::class, JAXBException::class)
    @JvmStatic
    fun main(args: Array<String>) {
        val cli = parse(args)
        for (s in cli.argList) {
            print(s)
        }
    }

    private var customStyFile: String = ""

    @Throws(JAXBException::class)
    private fun print(s: String) {
        table = GetetaFacade.readTable(s)
        totalNumSteps = table!!.region!!.count()
        fillColumns()

        input = table!!.ioVariables.filter { it.isInput }
        output = table!!.ioVariables.filter { it.isOutput }

        val depth = table!!.region!!.depth()

        println("\\documentclass{standalone}")
        println("\\usepackage{gtt}\n")
        if (customStyFile.isNotEmpty())
            println("\\usepackage{$customStyFile}\n")

        println("\\begin{document}\n")

        System.out.format("\\begin{tabular}{c|%s|%s|%s}%n",
                "c".repeat(input!!.size),
                "c".repeat(output!!.size),
                "c".repeat(depth + 1))

        System.out.printf("\\# & \\multicolumn{%d}{c}{\\categoryheader{Input}} & " +
                "\\multicolumn{%d}{c}{\\categoryheader{Output}} & \\coltime \\\\%n",
                input!!.size, output!!.size)

        val wrapColumnHeader = { hdr: String -> "\\variableheader{$hdr}" }

        System.out.printf("  & %s &%s \\\\%n",
                input!!.stream().map { it.name }
                        .map { escape(it) }
                        .map(wrapColumnHeader)
                        .reduce { a, b -> "$a & $b" }.orElse(""),
                output!!.stream().map { it.name }
                        .map { escape(it) }
                        .map(wrapColumnHeader)
                        .reduce { a, b -> "$a & $b" }.orElse(""))

        println("\\toprule")

        printRegionLatex(table!!.region!!.children)

        System.out.format("\\bottomrule\n\\end{tabular}%n")

        println("\\begin{tikzpicture}[remember picture, overlay]")
        drawLines.forEach { from, to -> System.out.printf("\\drawrepetition{%s}{%s}%n", from, to) }
        println("\\end{tikzpicture}")
        println("\\end{document}")
    }

    private fun fillColumns() {
        table!!.ioVariables.forEach { columns[it.name] = ArrayList() }

        //prefill
        table!!.region!!.flat()
                .forEach { s ->
                    s.entryForColumn.forEach { k, v ->
                        columns[k]?.add(parseAndSafePrint(Strings.nullToEmpty(v)))
                    }
                }

        //simplify
        columns.forEach { k, v ->
            if (v[0].isEmpty())
                v[0] = "-"

            var i = 0
            while (i < v.size - 1) {
                var j = i + 1
                // delete any cell contents, that is same as i
                while (j < v.size && (v[i] == v[j] || v[j].isEmpty())) {
                    v[j] = ""
                    j++
                }

                if (j == i + 2) {//one empty cell
                    v[i + 1] = "\\singlecopy{" + v[i] + "}"
                } else if (j > i + 2) {//more than one empty
                    v[i + 1] = tikzMark(k)
                    v[j - 1] = tikzMarkAndDraw(k)
                }
                i = j
            }
        }
    }

    private fun parseAndSafePrint(expr: String): String {
        if (expr.isEmpty()) return ""
        val cep = IOFacade.createParser(expr)
        val latexPrinter = LatexPrinter()
        try {
            val ctx = cep.cell()
            return ctx.accept(latexPrinter)
        } catch (e: ParseCancellationException) {
            System.err.println("Input: '$expr'")
            e.printStackTrace()
            throw e
        }
    }

    internal fun escape(s: String): String {
        var t = s
        for (sc in specialChars) {
            t = t.replace(sc, '\\' + sc)
        }
        return t
    }

    private fun printRegionLatex(region: List<TableNode>) {
        for (o in region) {
            if (o is State) {
                printStep(o)
            }
            if (o is Region) {
                println("\\midrule")
                printRegionLatex(o)
                println("\\midrule")
            }
        }
    }

    private fun printRegionLatex(b: Region) {
        durations.push(Tuple.make(b.duration, b.count()))
        printRegionLatex(b.children)
    }

    /*
    private static int countSteps(Block b) {
        int count = 0;
        for (Object o : b.getStepOrBlock()) {
            if (o instanceof Step) {
                count += 1;
            }
            if (o instanceof Block) {
                count += countSteps((Block) o);
            }
        }
        return count;
    }
    */

    private fun printStep(s: State) {
        System.out.printf("%2d", currentRow++)
        //List<Element> any = s.getAny().stream().map(Element.class::cast).collect(Collectors.toList());

        input!!.forEach { v -> System.out.printf(" & %15s", columns[v.name]?.get(currentRow - 1)) }

        output!!.forEach { v -> System.out.printf(" & %15s", columns[v.name]?.get(currentRow - 1)) }

        System.out.printf(" & %15s", beautifyDuration(s.duration))
        while (!durations.empty()) {
            val d = durations.pop()
            System.out.printf(" & \\rowgroupduration{%d}{%s}", d.b, beautifyDuration(d.a))
        }
        System.out.printf("\\\\%n")
    }

    private fun beautifyDuration(d: Duration): String {
        if (d.isDeterministicWait)
            return "\\textsc{dwait}"

        if (d.isOmega)
            return "$\\omega$"

        if (d.isOneStep)
            return "$1$"

        return if (d.isUnbounded) String.format("$\\geq%s$", d.lower) else String.format("$[%d,%d]$", d.lower, d.upper)

    }

    private operator fun get(s: List<Element>, varName: String, lastRow: Boolean): String {
        val value = TableReader.get(s, varName)
        val cacheValue = cache[varName]
        if (value != null) { //value defined
            cache[varName] = value //save into cache
            return if (value == cacheValue) if (lastRow) tikzMarkAndDraw(varName) else "" else tikzMarkAndDraw(varName) + escape(value)
            //else return new value.
        }
        if (cacheValue == null) {
            cache[varName] = "-"
            return DONT_CARE + tikzMark(varName) //first row
        } else {
            return if (lastRow) tikzMarkAndDraw(varName) else ""
        }
    }

    private fun tikzMark(varName: String): String {
        val c = markCounter.getAndIncrement(varName)
        lastTikzMarkColumn[varName] = c
        return String.format("\\tikzmark{%s%s}", varName, c)
    }


    private fun tikzMarkAndDraw(varName: String): String {
        val c = markCounter.getAndIncrement(varName)
        if (lastTikzMarkColumn.containsKey(varName)) {
            val b = lastTikzMarkColumn[varName]
            drawLines[varName + b] = varName + c
        }
        lastTikzMarkColumn[varName] = c
        return String.format("\\tikzmark{%s%s}", varName, c)
    }

    @Throws(ParseException::class)
    fun parse(args: Array<String>): CommandLine {
        val clp = DefaultParser()
        val options = org.apache.commons.cli.Options()
        options.addOption("f", "format", true, "output format")
        return clp.parse(options, args, true)
    }


    class Counter {
        private val counter = LinkedHashMap<String, Int>()

        fun peek(s: String): Int =
                counter.computeIfAbsent(s) { _ -> 0 }

        fun getAndIncrement(s: String): Int {
            val peek = peek(s)
            counter[s] = peek + 1
            return peek
        }
    }
}
