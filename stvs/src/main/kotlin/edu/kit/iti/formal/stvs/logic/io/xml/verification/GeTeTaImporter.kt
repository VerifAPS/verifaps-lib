package edu.kit.iti.formal.stvs.logic.io.xml.verification

import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.*
import edu.kit.iti.formal.stvs.model.*
import edu.kit.iti.formal.stvs.logic.*
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.xml.*
import edu.kit.iti.formal.stvs.model.verification.*
import org.jdom2.Element
import java.io.File
import java.io.IOException
import java.net.URL
import java.util.regex.Pattern
import javax.xml.transform.TransformerException
import javax.xml.transform.TransformerFactory
import javax.xml.transform.dom.DOMSource
import javax.xml.transform.stream.StreamResult

/**
 * Provides functionality to import the output of the GeTeTa verification engine.
 *
 * @author Benjamin Alt
 */
class GeTeTaImporter(private val typeContext: List<Type>, constraintSpec: ConstraintSpecification) :
    XmlImporter<VerificationResult>() {
    //    private val constraintSpecification: ConstraintSpecification = constraintSpec
//
//    /**
//     * Imports a [VerificationResult] from an XML [Node].
//     *
//     * @param source the Node from which the result should be imported
//     * @return the imported result
//     * @throws ImportException if an error occurs while importing
//     */
//    @Throws(ImportException::class)
//    override fun doImportFromXmlNode(source: Element): VerificationResult {
//        try {
//            val jaxbContext: JAXBContext = JAXBContext.newInstance(ObjectFactory::class.java)
//            val jaxbUnmarshaller: Unmarshaller = jaxbContext.createUnmarshaller()
//            val importedMessage: Message = jaxbUnmarshaller.unmarshal(source) as Message
//            return makeVerificationResult(source, importedMessage)
//        } catch (exception: JAXBException) {
//            throw ImportException(exception)
//        }
//    }
//
//    /**
//     * Builds a [VerificationResult] from a GeTeTa [Message].
//     *
//     * @param source the original top-level XML node of the verification result
//     * @param importedMessage the JAXB-converted GeTeTa [Message] object
//     * @return the imported result
//     * @throws ImportException if an error occurs while importing
//     */
//    @Throws(ImportException::class)
//    private fun makeVerificationResult(source: Element, importedMessage: String): VerificationResult {
//        try {
//            /* Write log to file */
//            val logFile: File = File.createTempFile("log-verification-", ".xml")
//            val transformerFactory = TransformerFactory.newInstance()
//            val transformer = transformerFactory.newTransformer()
//            val domSource = DOMSource(source)
//            val result: StreamResult = StreamResult(logFile)
//            transformer.transform(domSource, result)
//
//            return when (importedMessage.getReturncode()) {
//                RETURN_CODE_SUCCESS -> VerificationSuccess(logFile)
//                RETURN_CODE_NOT_VERIFIED -> Counterexample(
//                    parseCounterexample(importedMessage), logFile
//                )
//
//                else -> VerificationError(VerificationError.Reason.ERROR, logFile)
//            }
//        } catch (exception: TransformerException) {
//            throw ImportException(exception)
//        } catch (exception: IOException) {
//            throw ImportException(exception)
//        }
//    }
//
//    /**
//     * Generates a counterexample from a given [Message] from the GeTeTa verification engine.
//     *
//     * @param message Message from the GeTeTa verification engine
//     * @return concrete specification that represents the counterexample
//     * @throws ImportException exception while importing
//     */
//    @Throws(ImportException::class)
//    private fun parseCounterexample(message: String): ConcreteSpecification {
//        // Parse variables from counterexample
//
//        val varTypes: MutableMap<String, Type> = HashMap()
//        val varNames: MutableList<String> = ArrayList()
//        val varCategories: MutableMap<String, VariableCategory> = HashMap<String, VariableCategory>()
//
//        for (specIoVariable in constraintSpecification.columnHeaders) {
//            val name: String = specIoVariable.name
//            varNames.add(name)
//            varCategories[name] = specIoVariable.category
//            varTypes[name] = getType(specIoVariable)
//        }
//
//        val rowMap: List<String> = message.getCounterexample().getRowMappings().getRowMap()
//        // It does not matter which of the rowMaps to use, so always use the zeroeth
//        //take the last counterexample
//        val rowNums = parseRowMap(rowMap[rowMap.size - 1])
//        val currentValues = makeInitialValues(varTypes)
//
//        // Parse concrete rows
//        val steps: List<Counterexample.Step> = message.getCounterexample().getTrace().getStep()
//        val concreteRows: List<SpecificationRow<ConcreteCell>> =
//            makeConcreteRows(steps, rowNums, varNames, varTypes, currentValues, varCategories)
//
//        // Parse durations
//        val concreteDurations: List<ConcreteDuration> = makeConcreteDurations(rowNums)
//
//        val concreteSpec: ConcreteSpecification = ConcreteSpecification(true)
//        for (varName in varNames) {
//            concreteSpec.columnHeaders
//                .add(ValidIoVariable(varCategories[varName], varName, varTypes[varName]))
//        }
//        concreteSpec.rows.addAll(concreteRows)
//        concreteSpec.durations.addAll(concreteDurations)
//        return concreteSpec
//    }
//
//    private fun makeInitialValues(variableTypes: Map<String, Type>): MutableMap<String, Value> {
//        val initialValues: MutableMap<String, Value> = HashMap()
//        for ((key, value) in variableTypes) {
//            initialValues[key] = value.generateDefaultValue()
//        }
//        return initialValues
//    }
//
//    @Throws(ImportException::class)
//    private fun getType(variable: SpecIoVariable): Type {
//        for (type in typeContext) {
//            if (type.typeName == variable.type) {
//                return type
//            }
//        }
//        throw ImportException("Cannot find type for variable " + variable.name)
//    }
//
//    /**
//     * Generates a list of concrete specification rows for a given list of
//     * [edu.kit.iti.formal.exteta_1_0.report.Counterexample.Step]s.
//     *
//     * @param steps the GeTeTa output {
//     * @link edu.kit.iti.formal.exteta_1_0.report.Counterexample.Step}s to import the rows from
//     * @param rowNums the row mapping (map from cycle number to row number)
//     * @param varNames the names of all declared free and i/o variables
//     * @param varTypes the types of the variables
//     * @param currentValues the current values of the variables
//     * @param varCategories the categories (input/output) of the i/o variables
//     * @return a list containing the rows of the counterexample
//     * @throws ImportException if an error occurs during importing
//     */
//    @Throws(ImportException::class)
//    private fun makeConcreteRows(
//        steps: List<Counterexample.Step>,
//        rowNums: List<Int>, varNames: List<String>, varTypes: MutableMap<String, Type>,
//        currentValues: MutableMap<String, Value>, varCategories: MutableMap<String, VariableCategory>
//    ): List<SpecificationRow<ConcreteCell>> {
//        val concreteRows: MutableList<SpecificationRow<ConcreteCell>> = ArrayList<SpecificationRow<ConcreteCell>>()
//        var cycleNum = -1
//        // iterate over steps to create specification rows
//        for (i in steps.indices) {
//            if (i - 1 > rowNums.size) {
//                break // Make sure I terminate after right # of cycles
//            }
//            val step: Counterexample.Step = steps[i]
//            processOutputVariables(varTypes, currentValues, varCategories, step)
//
//            // Now can make and add the row
//            if (cycleNum > -1) {
//                val row: SpecificationRow<ConcreteCell> =
//                    makeSpecificationRowFromValues(varNames, currentValues)
//                concreteRows.add(row)
//            }
//
//            processInputVariables(varTypes, currentValues, varCategories, step)
//            cycleNum++
//        }
//        return concreteRows
//    }
//
//    /**
//     * Converts a list of beginning cycles of durations into a List of [ConcreteDuration]s.
//     *
//     * @param rowNums list of beginning cycles of durations
//     * @return list of durations
//     */
//    private fun makeConcreteDurations(rowNums: List<Int>): List<ConcreteDuration> {
//        val concreteDurations: MutableList<ConcreteDuration> = ArrayList<ConcreteDuration>()
//        var currentDuration = 0
//        var oldRowNum = 1
//        var cycle = 0
//        while (cycle < rowNums.size) {
//            val rowNum = rowNums[cycle]
//            if (rowNum != oldRowNum) {
//                concreteDurations.add(ConcreteDuration(cycle - currentDuration, currentDuration))
//                oldRowNum = rowNum
//                currentDuration = 0
//            }
//            currentDuration++
//            cycle++
//        }
//        concreteDurations.add(ConcreteDuration(cycle - currentDuration, currentDuration))
//        return concreteDurations
//    }
//
//    /**
//     * Parses the input variables of one [Counterexample.Step] and adds found types, values and
//     * categories to the corresponding map.
//     *
//     * @param varTypes map of types
//     * @param currentValues map of values for one step
//     * @param varCategories map of categories
//     * @param step current step
//     * @throws ImportException exception while importing
//     */
//    @Throws(ImportException::class)
//    private fun processInputVariables(
//        varTypes: MutableMap<String, Type>, currentValues: MutableMap<String, Value>,
//        varCategories: MutableMap<String, VariableCategory>, step: Counterexample.Step
//    ) {
//        for (input in step.getInput()) { // Input vars are initialized here FOR THE NEXT
//            // CYCLE
//            val varName: String = VariableEscaper.unescapeIdentifier(input.getName())
//            if (INPUT_VARIABLE_PATTERN.matcher(varName).matches()) {
//                varCategories[varName] = VariableCategory.INPUT
//                processVarAssignment(
//                    currentValues, varTypes, varName,
//                    VariableEscaper.unescapeIdentifier(input.getValue())
//                )
//            }
//        }
//    }
//
//    /**
//     * Parses the output variables of one [Counterexample.Step] and adds found types, values and
//     * categories to the corresponding map.
//     *
//     * @param varTypes map of types
//     * @param currentValues map of values for one step
//     * @param varCategories map of categories
//     * @param step current step
//     * @throws ImportException exception while importing
//     */
//    @Throws(ImportException::class)
//    private fun processOutputVariables(
//        varTypes: MutableMap<String, Type>, currentValues: MutableMap<String, Value>,
//        varCategories: MutableMap<String, VariableCategory>, step: Counterexample.Step
//    ) {
//        for (state in step.getState()) { // Output vars are initialized here
//            val stateString: String = state.getName().trim()
//            if (CODE_VARIABLE_PATTERN.matcher(stateString).matches()) {
//                val periodIndex = stateString.indexOf(".")
//                val varName: String =
//                    VariableEscaper.unescapeIdentifier(stateString.substring(periodIndex + 1, stateString.length))
//                varCategories[varName] = VariableCategory.OUTPUT
//                val varValue: String = VariableEscaper.unescapeIdentifier(state.getValue())
//                processVarAssignment(currentValues, varTypes, varName, varValue)
//            }
//        }
//    }
//
//    /**
//     * Creates a [SpecificationRow] for one step.
//     *
//     * @param varNames variable names
//     * @param currentValues values for one step
//     * @return specification row representing one step
//     */
//    private fun makeSpecificationRowFromValues(
//        varNames: List<String>,
//        currentValues: Map<String, Value>
//    ): SpecificationRow<ConcreteCell> {
//        val row: SpecificationRow<ConcreteCell> = SpecificationRow.createUnobservableRow(HashMap<K, V>())
//        for (varName in varNames) {
//            row.cells.put(varName, ConcreteCell(currentValues[varName]))
//        }
//        return row
//    }
//
//    /**
//     * Parses a list of integers separated by a comma and space.
//     *
//     * @param rowMapString string to be parsed
//     * @return list of integers
//     */
//    private fun parseRowMap(rowMapString: String): List<Int> {
//        val tokens = rowMapString.trim { it <= ' ' }.split(", ".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
//        val res: MutableList<Int> = ArrayList()
//        for (token in tokens) {
//            res.add(token.toInt())
//        }
//        return res
//    }
//
//    @get:Throws(IOException::class)
//    protected val xsdResource: URL?
//        get() = this.javaClass.getResource("/fileFormats/report.xsd")
//
//    /**
//     * Processes an assignment of a single value represented by `varValue` to a variable
//     * specified by `varName` for one step in the counterexample. The type of the value is
//     * determined by matching `varValue` against several regular expressions and, in case of an
//     * enum type, further information is taken from `typeContext`. The value is then added to
//     * the `currentValues`-Map as a [Value]. Found types are added to `varTypes`.
//     *
//     * @param currentValues Represents the values of variables for a step
//     * @param varTypes Map of types
//     * @param varName Name of the variable
//     * @param varValue String representation of this variable for one step
//     * @throws ImportException when an enum literal is assigned to a variable of incompatible enum
//     * type
//     */
//    @Throws(ImportException::class)
//    private fun processVarAssignment(
//        currentValues: MutableMap<String, Value>, varTypes: MutableMap<String, Type>,
//        varName: String, varValue: String
//    ) {
//        if (INT_VALUE_PATTERN.matcher(varValue).matches()) {
//            val underlineIndex = varValue.indexOf("_")
//            var intVal = varValue.substring(underlineIndex + 1, varValue.length).toInt()
//            if (varValue[0] == '-') {
//                intVal = -intVal
//            }
//            currentValues[varName] = ValueInt(intVal)
//            if (!varTypes.containsKey(varName)) {
//                varTypes[varName] = TypeInt.INT
//            }
//        } else if (BOOL_VALUE_PATTERN.matcher(varValue).matches()) {
//            if (!varTypes.containsKey(varName)) {
//                varTypes[varName] = TypeBool.BOOL
//            }
//            if (varValue == "TRUE") {
//                currentValues[varName] = ValueBool.TRUE
//            } else {
//                currentValues[varName] = ValueBool.FALSE
//            }
//        } else {
//            if (!varTypes.containsKey(varName)) {
//                // Find the enum type for this variable
//                var enumTypeFound = false
//                for (type in typeContext) {
//                    val `val` = type.parseLiteral(varValue)
//                    if (`val`.isPresent) {
//                        enumTypeFound = true
//                        varTypes[varName] = type
//                    }
//                }
//                if (!enumTypeFound) {
//                    throw ImportException("No enum type found for literal $varValue")
//                }
//            }
//            val enumVal = varTypes[varName]!!.parseLiteral(varValue)
//            if (!enumVal.isPresent) {
//                throw ImportException(
//                    "Illegal literal " + varValue + " for enum type "
//                            + varTypes[varName]!!.typeName
//                )
//            }
//            currentValues[varName] = enumVal.get()
//        }
//    }
//
//    companion object {
//        /* GeTeTa return codes */
//        private const val RETURN_CODE_SUCCESS = "verified"
//        private const val RETURN_CODE_NOT_VERIFIED = "not-verified"
//
//        /* Regular expressions */
//        private const val IDENTIFIER_RE = "[\$a-zA-Z0-9_]+"
//        private val VARIABLES_FOUND_PATTERN: Pattern = Pattern.compile("[0-9]+ variables " + "found")
//        private val VARIABLE_DECL_PATTERN: Pattern = Pattern.compile("\\s*" + IDENTIFIER_RE + " : " + IDENTIFIER_RE)
//        private val CODE_VARIABLE_PATTERN: Pattern = Pattern.compile("code\\." + IDENTIFIER_RE)
//        private val INPUT_VARIABLE_PATTERN: Pattern = Pattern.compile(IDENTIFIER_RE)
//        private val INT_VALUE_PATTERN: Pattern = Pattern.compile("-?0sd16_-?[0-9]+")
//        private val BOOL_VALUE_PATTERN: Pattern = Pattern.compile("(TRUE)|(FALSE)")
//    }
    override fun doImportFromXmlNode(source: Element): VerificationResult {
        TODO("Not yet implemented")
    }

    override val xsdResource: URL?
        get() = TODO("Not yet implemented")
}
