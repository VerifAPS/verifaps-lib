package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.logic.io.jsonFormat
import edu.kit.iti.formal.stvs.model.common.*
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.problems.InvalidIoVarProblem
import edu.kit.iti.formal.stvs.util.MapUtil
import kotlinx.serialization.Serializable
import org.apache.commons.io.IOUtils
import java.util.function.Consumer
import java.util.function.Function
import java.util.stream.Collectors

/**
 * Created by Philipp on 04.02.2017.
 */
object JsonTableParser {
    inline fun <reified T> jsonFromResource(resource: String, clazz: Class<*>) =
        jsonFormat.decodeFromString<T>(stringFromResource(resource, clazz))

    fun stringFromResource(resource: String, clazz: Class<*>): String =
        IOUtils.toString(clazz.getResourceAsStream(resource)!!, "UTF-8")

    fun expectedSpecProblemsFromJson(elem: JsonElement?): List<Class<*>> {
        val expectedProblems: JsonExpectedProblems = GSON.fromJson(elem, JsonExpectedProblems::class.java)
        return expectedProblems.expected_problems!!.stream()
            .map { s: String ->
                try {
                    return@map Class.forName("edu.kit.iti.formal.stvs.model.table.problems.$s")
                } catch (e: ClassNotFoundException) {
                    throw RuntimeException(e)
                }
            }
            .collect(Collectors.toList())
    }

    fun codeIoVariablesFromJson(elem: JsonElement?): List<CodeIoVariable> {
        val ioVars: JsonCodeIoVars = GSON.fromJson(elem, JsonCodeIoVars::class.java)
        return ioVars.codeiovars!!.stream()
            .map { ioVar: JsonCodeIoVar ->
                CodeIoVariable(
                    VariableCategory.valueOf(ioVar.kind),
                    ioVar.type,
                    ioVar.name
                )
            }
            .collect(Collectors.toList())
    }

    fun concreteTableFromJson(types: List<Type>?, isCounterExample: Boolean, element: JsonElement)
            : ConcreteSpecification {
        val parsedTable: SpecificationTable<SpecIoVariable, String, String> = specificationTableFromJson(element)

        val concreteSpec = ConcreteSpecification(isCounterExample)

        val typeContext: MutableList<Type> = ArrayList()
        typeContext.add(TypeInt.INT)
        typeContext.add(TypeBool.BOOL)
        typeContext.addAll(types!!)
        val typesByName = typeContext.stream()
            .collect(Collectors.toMap(Type::typeName, Function.identity()))

        for (specIoVariable in parsedTable.columnHeaders) {
            try {
                val validIoVariable: ValidIoVariable = InvalidIoVarProblem.tryGetValidIoVariable(
                    specIoVariable,
                    emptyList(),
                    typesByName
                ) { problem -> } // ignore insignificant problems

                concreteSpec.columnHeaders.add(validIoVariable)
            } catch (problem: InvalidIoVarProblem) {
                throw RuntimeException(problem)
            }
        }

        for (rowIndex in parsedTable.rows.indices) {
            val row = parsedTable.rows[rowIndex]
            val cells = MapUtil.mapValuesWithKey(row.cells) { columnId: String?, cellString: String ->
                ConcreteCell(
                    concreteSpec.getColumnHeaderByName(columnId).validType.parseLiteral(cellString.trim { it <= ' ' })
                        .orElseThrow {
                            RuntimeException(
                                ("Couldnt parse: "
                                        + cellString + " of type "
                                        + concreteSpec.getColumnHeaderByName(columnId).validType.typeName
                                        ).toString() + " in column " + columnId
                            )
                        })
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

    fun constraintTableFromJson(element: JsonElement?): ConstraintSpecification {
        val freeVarSet: FreeVariableList = freeVariableSetFromJson(element)
        val parsedTable: SpecificationTable<SpecIoVariable, String, String> = specificationTableFromJson(element)

        val spec: ConstraintSpecification = ConstraintSpecification(freeVarSet)

        spec.columnHeaders.addAll(parsedTable.columnHeaders)

        for (row in parsedTable.rows) {
            val cells: MutableMap<String?, ConstraintCell> = HashMap()

            row.cells.forEach { columnId: String?, cellString: String? ->
                cells[columnId] = ConstraintCell(cellString)
            }

            spec.rows.add(ConstraintSpecification.createRow(cells))
        }

        spec.durations.addAll(
            parsedTable.durations.stream()
                .map { stringRepresentation: String? -> ConstraintDuration(stringRepresentation) }
                .collect(Collectors.toList()))

        return spec
    }

    fun freeVariableSetFromJson(element: JsonElement?): FreeVariableList {
        val freeVariableList: FreeVariableList = FreeVariableList(ArrayList<FreeVariable>())
        GSON.fromJson(element, JsonFreeVarSet::class.java).freevariables
            .map { _: JsonTableParser?, jsonFreeVar: JsonFreeVar -> toFreeVariable(jsonFreeVar) }
            .forEach { freeVar -> freeVariableList.variables.add(freeVar) }

        return freeVariableList
    }

    private fun toFreeVariable(jsonFreeVar: JsonFreeVar): FreeVariable {
        return FreeVariable(jsonFreeVar.name, jsonFreeVar.type)
    }

    fun specificationTableFromJson(element: JsonElement?): SpecificationTable<SpecIoVariable, String, String> {
        return specificationTableFromJsonTable(GSON.fromJson(element, JsonTable::class.java))
    }

    private fun specificationTableFromJsonTable(table: JsonTable): SpecificationTable<SpecIoVariable, String, String> {
        val spec: SpecificationTable<SpecIoVariable, String, String> =
            SpecificationTable({ arrayOf() }, { arrayOf() })
        table.variables!!
            .map { obj -> toSpecIoVariable(obj) }
            .forEach { r -> spec.columnHeaders.add(r) }

        table.rows!!.forEach(Consumer { row: String -> spec.rows.add(toSpecificationRow(row, spec.columnHeaders)) })

        spec.durations.addAll(table.durations!!)
        return spec
    }

    private fun toSpecificationRow(s: String, ioVars: List<SpecIoVariable>): SpecificationRow<String> {
        val split = s.split("\\s*\\|\\s*".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
        val elems: MutableMap<String?, String> = HashMap()
        for (i in split.indices) {
            elems[ioVars[i].name] = split[i].trim { it <= ' ' }
        }
        return SpecificationRow.createUnobservableRow(elems)
    }

    private fun toSpecIoVariable(iovar: JsonIoVariable): SpecIoVariable {
        return SpecIoVariable(iovar.iotype, iovar.iotype.defaultRole, iovar.type, iovar.name)
    }

    private fun typeFromString(input: String): Type {
        return when (input) {
            "INT" -> TypeInt.INT
            "BOOL" -> TypeBool.BOOL
            else -> TypeEnum(input, emptyList())
        }
    }

    @Serializable
    class JsonExpectedProblems(var expected_problems: List<String>)

    @Serializable
    data class JsonFreeVarSet(var freevariables: List<JsonFreeVar>)

    @Serializable
    data class JsonCodeIoVar(var name: String, var type: String, var kind: String)

    @Serializable
    class JsonCodeIoVars(var codeiovars: List<JsonCodeIoVar>)

    @Serializable
    class JsonFreeVar(var name: String, var type: String)

    @Serializable
    data class JsonTable(var variables: List<JsonIoVariable>, var rows: List<String>, var durations: List<String>)

    @Serializable
    data class JsonIoVariable(var iotype: VariableCategory, var name: String, var type: String) {}
}
