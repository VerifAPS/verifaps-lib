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
package edu.kit.iti.formal.stvs.model.table

import com.google.gson.GsonBuilder
import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.model.common.*
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.problems.InvalidIoVarProblem
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblemException
import edu.kit.iti.formal.stvs.util.MapUtil
import java.io.InputStreamReader
import java.io.Reader
import java.util.function.Consumer
import java.util.function.Function
import java.util.stream.Collectors

/**
 * Created by Philipp on 04.02.2017.
 */
object JsonTableParser {
    val GSON = GsonBuilder().create()

    inline fun <reified T> fromJson(resource: Reader) = GSON.fromJson(resource, T::class.java)
    inline fun <reified T> fromJson(resource: String) = GSON.fromJson(resource, T::class.java)
    inline fun <reified T> fromJson(resource: JsonElement) = GSON.fromJson(resource, T::class.java)

    inline fun <reified T> jsonFromResource(resource: String) = jsonFromResource(resource, T::class.java)

    fun jsonFromResource(resource: String, clazz: Class<*>): JsonElement =
        GSON.fromJson(readResource(resource, clazz), JsonElement::class.java)

    private fun readResource(resource: String, clazz: Class<*>): String =
        InputStreamReader(clazz.getResourceAsStream(resource)!!).readText()

    fun expectedSpecProblemsFromJson(elem: JsonElement): List<Class<*>> {
        val expectedProblems: JsonExpectedProblems = fromJson<JsonExpectedProblems>(elem)
        return expectedProblems.expected_problems
            .map { s: String ->
                Class.forName("edu.kit.iti.formal.stvs.model.table.problems.$s")
            }
    }

    fun codeIoVariablesFromJson(elem: JsonElement): List<CodeIoVariable> {
        val ioVars: JsonCodeIoVars = fromJson<JsonCodeIoVars>(elem)
        return ioVars.codeiovars.map { CodeIoVariable(VariableCategory.valueOf(it.kind), it.type, it.name) }
    }

    fun concreteTableFromJson(
        types: List<Type>?,
        isCounterExample: Boolean,
        element: JsonElement,
    ): ConcreteSpecification {
        val parsedTable: SpecificationTable<SpecIoVariable, String, String> = specificationTableFromJson(element)

        val concreteSpec = ConcreteSpecification(isCounterExample)

        val typeContext: MutableList<Type> = ArrayList()
        typeContext.add(TypeInt)
        typeContext.add(TypeBool)
        typeContext.addAll(types!!)
        val typesByName = typeContext.stream()
            .collect(Collectors.toMap(Type::typeName, Function.identity()))

        for (specIoVariable in parsedTable.columnHeaders) {
            try {
                val validIoVariable: ValidIoVariable = InvalidIoVarProblem.tryGetValidIoVariable(
                    specIoVariable,
                    emptyList(),
                    typesByName,
                ) { problem -> } // ignore insignificant problems

                concreteSpec.columnHeaders.add(validIoVariable)
            } catch (problem: SpecProblemException) {
                throw RuntimeException(problem)
            }
        }

        for (rowIndex in parsedTable.rows.indices) {
            val row = parsedTable.rows[rowIndex]
            val cells = MapUtil.mapValuesWithKey(row.cells) { columnId: String, cellString: String ->
                ConcreteCell(
                    concreteSpec.getColumnHeaderByName(columnId).validType.parseLiteral(cellString.trim { it <= ' ' })
                        ?: error(
                            "Couldnt parse: $cellString of type ${concreteSpec.getColumnHeaderByName(
                                columnId,
                            ).validType.typeName} in column $columnId",
                        ),
                )
            }
            concreteSpec.rows.add(SpecificationRow.createUnobservableRow(cells))
        }

        var beginCycle = 0
        for (durString in parsedTable.durations) {
            val duration = durString.toInt()
            concreteSpec.durations.add(ConcreteDuration(beginCycle, duration))
            beginCycle += duration
        }

        return concreteSpec
    }

    fun constraintTableFromJson(element: JsonElement): ConstraintSpecification {
        val freeVarSet: FreeVariableList = freeVariableSetFromJson(element)
        val parsedTable: SpecificationTable<SpecIoVariable, String, String> = specificationTableFromJson(element)

        val spec = ConstraintSpecification(freeVarSet)

        spec.columnHeaders.addAll(parsedTable.columnHeaders)

        for (row in parsedTable.rows) {
            val cells = hashMapOf<String, ConstraintCell>()

            row.cells.forEach { (columnId, cellString) ->
                cells[columnId] = ConstraintCell(cellString)
            }

            spec.rows.add(ConstraintSpecification.createRow(cells))
        }

        spec.durations.addAll(
            parsedTable.durations.stream()
                .map { stringRepresentation: String? -> ConstraintDuration(stringRepresentation) }
                .collect(Collectors.toList()),
        )

        return spec
    }

    fun freeVariableSetFromJson(element: JsonElement): FreeVariableList = FreeVariableList(
        fromJson<JsonFreeVarSet>(element).freevariables.map { toFreeVariable(it) }.toMutableList(),
    )

    private fun toFreeVariable(jsonFreeVar: JsonFreeVar): FreeVariable =
        FreeVariable(jsonFreeVar.name, jsonFreeVar.type)

    fun specificationTableFromJson(element: JsonElement): SpecificationTable<SpecIoVariable, String, String> =
        specificationTableFromJsonTable(fromJson<JsonTable>(element))

    private fun specificationTableFromJsonTable(table: JsonTable): SpecificationTable<SpecIoVariable, String, String> {
        val spec: SpecificationTable<SpecIoVariable, String, String> =
            SpecificationTable({ arrayOf() }, { arrayOf() })
        table.variables
            .map { obj -> toSpecIoVariable(obj) }
            .forEach { r -> spec.columnHeaders.add(r) }

        table.rows.forEach(Consumer { row: String -> spec.rows.add(toSpecificationRow(row, spec.columnHeaders)) })

        spec.durations.addAll(table.durations)
        return spec
    }

    private fun toSpecificationRow(s: String, ioVars: List<SpecIoVariable>): SpecificationRow<String> {
        val split = s.split("\\s*\\|\\s*".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
        val elems = hashMapOf<String, String>()
        for (i in split.indices) {
            elems[ioVars[i].name] = split[i].trim { it <= ' ' }
        }
        return SpecificationRow.createUnobservableRow(elems)
    }

    private fun toSpecIoVariable(iovar: JsonIoVariable): SpecIoVariable =
        SpecIoVariable(iovar.iotype, iovar.iotype.defaultRole, iovar.type, iovar.name)

    private fun typeFromString(input: String): Type = when (input) {
        "INT" -> TypeInt
        "BOOL" -> TypeBool
        else -> TypeEnum(input, emptyList())
    }

    class JsonExpectedProblems(var expected_problems: List<String>)

    data class JsonFreeVarSet(var freevariables: List<JsonFreeVar>)

    data class JsonCodeIoVar(var name: String, var type: String, var kind: String)

    class JsonCodeIoVars(var codeiovars: List<JsonCodeIoVar>)

    class JsonFreeVar(var name: String, var type: String)

    data class JsonTable(var variables: List<JsonIoVariable>, var rows: List<String>, var durations: List<String>)

    data class JsonIoVariable(var iotype: VariableCategory, var name: String, var type: String)
}