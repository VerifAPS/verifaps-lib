package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.monitor.SmvToCTranslator
import edu.kit.iti.formal.smv.SMVAstDefaultVisitorNN
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.SMVWordType
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.debug
import edu.kit.iti.formal.util.error
import edu.kit.iti.formal.util.info
import java.io.File
import java.nio.file.Paths
import kotlin.math.max

/**
 * @author Moritz Baumann
 * @version 1 (2/23/20)
 */

object Synthesis {
    @JvmStatic
    fun main(args: Array<String>) {
        SynthesisApp().main(args)
    }
}

class SynthesisApp : CliktCommand(
        help = "Synthesizes a program for each for each given file",
        epilog = "ttsynth -- Program Synthesis from Test Tables.",
        name = "ttsynth") {

    private val tableFiles by argument("FILE", help = "Test table DSL file")
            .file(exists = true, folderOkay = false, readable = true)
            .multiple(required = true)

    private val outputFolder by option("-o", "--output", help = "Output directory")
            .file(exists = true, fileOkay = false, writable = true)
            .default(Paths.get("").toAbsolutePath().toFile())

    private val omegaVenv by option("--omega-venv", help = "Path to virtualenv with omega", envvar = "OMEGA_VENV")
            .file(exists = true, fileOkay = false)

    override fun run() {
        val expressionSynthesizer = ExpressionSynthesizer(omegaVenv)

        tableFiles.forEach { tableFile ->
            val programName = tableFile.name.split('.')[0]
            val headerFile = File(outputFolder, "${programName}.h")
            val moduleFile = File(outputFolder, "${programName}.cpp")

            info("Parsing DSL file: ${tableFile.absolutePath}")
            val synthesizer = ProgramSynthesizer(programName, tableFile, expressionSynthesizer)

            info("Generating header file: ${headerFile.absolutePath}")
            headerFile.writeText(synthesizer.generateHeader())

            info("Generating module file: ${moduleFile.absolutePath}")
            moduleFile.writeText(synthesizer.generateModule())
        }
    }
}

class ProgramSynthesizer(val name: String, tables: List<GeneralizedTestTable>,
                         private val synthesizer: ExpressionSynthesizer) {
    constructor(name: String, tableDslFile: File, synthesizer: ExpressionSynthesizer) :
            this(name, GetetaFacade.readTables(tableDslFile), synthesizer)

    @Suppress("Unused") // meant for unit tests
    constructor(name: String, tableDsl: String, synthesizer: ExpressionSynthesizer) :
            this(name, GetetaFacade.parseTableDSL(tableDsl), synthesizer)

    companion object {
        private val HISTORY_VAR_REGEX = Regex("""^code\$(.+)__history._\$([0-9]+)$""")
    }

    // accumulated over all tables (SVariable::name -> type)
    private val inputs = mutableMapOf<String, SMVType>()
    private val outputs = mutableMapOf<String, SMVType>()
    private val referenceVariables = mutableMapOf<String, SMVType>() // inputs and outputs referenced in references
    private val references = mutableMapOf<String, SMVType>() // the concrete references to historical values
    private var maxLookBack = 0
    // maps SVariable names to names for temporary variables
    private val variableNames = mutableMapOf<String, String>()
    private val translator = SmvToCTranslator()
    // indexed by table
    private val automata = mutableListOf<TestTableAutomaton>()
    private val states = mutableListOf<List<RowState>>()
    private val unrolledRowOffsets = mutableListOf<Int>()

    init {
        // preprocessing
        tables.map { gtt ->
            gtt.ensureProgramRuns()
            gtt.generateSmvExpression()
            gtt.simplify()
        }

        // check a few preconditions (not everything is checked here, exceptions might be thrown later during synthesis)
        if (tables.any { it.constraintVariables.isNotEmpty() }) {
            //TODO weigl: Hint; you can use error(...) {...}, or require(...) {...}
            throw IllegalArgumentException("Global variables are currently unsupported")
        }
        if (tables.any { it.functions.isNotEmpty() }) {
            throw IllegalArgumentException("Functions are currently unsupported")
        }

        // extract context information
        var unrolledRowCount = 0
        tables.forEach { table ->
            val inputVariables = table.programVariables.filter { it.isAssumption }.toSet()
            val variables = table.programVariables.map { it.name to it }.toMap()

            table.parseContext.let { context ->
                val historyVariables = mutableSetOf<SVariable>()
                context.refs.forEach { (sVariable, lookBack) ->
                    historyVariables += sVariable
                    maxLookBack = max(maxLookBack, -lookBack)
                }
                context.vars.forEach { (variable, sVariable) ->
                    val sVariableName = sVariable.name

                    if (inputVariables.contains(variable)) {
                        inputs[sVariableName] = variable.logicType
                        translator.variableReplacement[sVariableName] = "input.${variable.name}"
                    } else {
                        outputs[sVariableName] = variable.logicType
                        translator.variableReplacement[sVariableName] = "output.${variable.name}"
                    }

                    variableNames[sVariableName] = variable.name

                    if (historyVariables.contains(sVariable)) {
                        referenceVariables[sVariableName] = variable.logicType
                    }
                }
            }

            // find all SVariables with historical references
            val referenceExtractor = SVariableCollector(HISTORY_VAR_REGEX)
            table.region.flat().fold(setOf<Pair<String, MatchResult>>()) { acc, row ->
                val expressions = row.inputExpr.values + row.outputExpr.values
                acc + expressions.fold(setOf<Pair<String, MatchResult>>()) { innerAcc, expr ->
                    innerAcc + expr.accept(referenceExtractor)
                }
            }.forEach { (sVariableName, match) ->
                val (variableName, lookBehind) = match.destructured
                references[sVariableName] = variables.getValue(variableName).logicType
                translator.variableReplacement[sVariableName] =
                        "var_history.get_value(${lookBehind}).${variableName}"
                variableNames[sVariableName] = "__history_${variableName}_${lookBehind}"
            }

            val automaton = GetetaFacade.constructTable(table).automaton
            automata.add(automaton)
            states.add(table.region.flat().fold(listOf()) { acc, row -> acc + automaton.rowStates.getValue(row) })
            unrolledRowOffsets += unrolledRowCount
            unrolledRowCount += automaton.rowStates.size
        }
    }

    fun generateHeader(): String {
        val initialState = states.foldIndexed(listOf<Boolean>()) { index, acc, rowStates ->
            val automaton = automata[index]
            acc + rowStates.map { automaton.initialStates.contains(it) }
        }
        // initial state as string, bits reversed to match bitset constructor order
        val stateDescription = initialState.asReversed().joinToString("") { if (it) "1" else "0" }

        return """
            #pragma once

            #include <array>
            #include <bitset>
            #include <cassert>
            #include <cstddef>
            #include <cstdint>
            #include <string_view>
            
            namespace $name {
                template <typename T, std::size_t N>
                class history {
                public:
                    using size_type = typename std::array<T, N>::size_type;
                    using value_type = typename std::array<T, N>::value_type;

                    void add_value(const T& value) {
                        array[front_pos] = value;
                        front_pos = (front_pos + 1) % N;
                    }

                    value_type get_value(size_type look_behind_steps) {
                        assert (look_behind_steps != 0 and look_behind_steps <= N);
                        return array[(front_pos + N - look_behind_steps) % N];
                    }

                private:
                    std::array<T, N> array;
                    size_type front_pos = 0;
                };
            
                class synthesized {
                public:
                    struct input_type {
                        ${indentLines(generateStructMembers(inputs), 24)}
                    };
    
                    struct output_type {
                        ${indentLines(generateStructMembers(outputs), 24)}
                        
                        // for testing purposes - in C++20, we'll be able to simply use a defaulted spaceship operator
                        bool operator==(const output_type& other) const {
                            return ${generateOutputEqualityComparison()};
                        }
                    };
    
                    struct result {
                        bool in_spec;
                        output_type output;
                        
                        // for testing purposes - in C++20, we'll be able to simply use a defaulted spaceship operator
                        bool operator==(const result& other) const {
                            return in_spec == other.in_spec && output == other.output;
                        }
                    };
    
                    result next(const input_type& input);
    
                private:
                    struct memory_type {
                        ${indentLines(generateStructMembers(referenceVariables), 24)}
                    };
                    
                    static constexpr std::size_t MAX_LOOKBACK = $maxLookBack;
                    static constexpr std::string_view INITIAL_STATE = "$stateDescription";
    
                    std::bitset<INITIAL_STATE.size()> state{INITIAL_STATE.data()};
                    history<memory_type, MAX_LOOKBACK> var_history;
    
                    void update_state_prediction(const input_type& input);
                    output_type calculate_output(const input_type& input);
                    void state_transition(const input_type& input, const output_type& output);
                    void update_history(const input_type& input, const output_type& output);
                };
            }
        """.trimIndent()
    }

    fun generateModule(): String {
        return """
            #include "${name}.h"
            
            #include <limits>
            #include <type_traits>
            
            #define ite(cond, then, else) (cond) ? (then) : (else)
            
            namespace {
                template<typename T, typename = std::enable_if_t<std::is_integral_v<T>>>
                struct bit_size {
                    static constexpr std::size_t value = std::numeric_limits<T>::digits
                            + std::numeric_limits<T>::is_signed;
                };
            
                template<typename T, typename = std::enable_if_t<std::is_integral_v<T>>>
                constexpr std::size_t bit_size_v = bit_size<T>::value;
            
                template<typename T, std::size_t size = bit_size<T>::value,
                        typename = std::enable_if_t<std::is_integral_v<T> && sizeof(T) <= sizeof(unsigned long long)>>
                constexpr std::bitset<size> to_bitset(T value) {
                    // cast to unsigned long long is well-defined for negative signed integers
                    return {static_cast<unsigned long long>(value)};
                }
            
                template<typename T, std::size_t size = bit_size<T>::value,
                        typename = std::enable_if_t<std::is_integral_v<T> && sizeof(T) <= sizeof(unsigned long long)>>
                void from_bitset(std::bitset<size>& bs, T& value) {
                    // verify that implementation-defined behavior matches expectations
                    static_assert(static_cast<T>(static_cast<unsigned long long>(std::numeric_limits<T>::min()))
                            == std::numeric_limits<T>::min());
                    // the reverse cast is implementation-defined for negative signed integers before C++20
                    value = static_cast<T>(bs.to_ullong());
                }
            }
            
            namespace $name {

                using input_t = synthesized::input_type;
                using output_t = synthesized::output_type;

                synthesized::result synthesized::next(const input_t& input) {
                    update_state_prediction(input);
                    if (state.none()) {
                        return {false, {}};
                    }
                    auto output = calculate_output(input);
                    state_transition(input, output);
                    update_history(input, output);
                    return {true, output};
                }
                
                void synthesized::update_state_prediction(const input_t& input) {
                    // check negation of input constraints for each state
                    ${indentLines(generateStateChecks(), 20)}
                }
            
                output_t synthesized::calculate_output(const input_t &input) {
                    auto output = output_type{};

                    ${indentLines(generateOutputFunctions(), 20)}
                    
                    return output;
                }

                void synthesized::state_transition(const input_t &input, const output_t &output) {
                    // check which states were actually fulfilled by the output and progress accordingly
                    std::bitset<INITIAL_STATE.size()> new_state{};
                    ${indentLines(generateStateProgression(), 20)}
                    state = new_state;
                }
                                
                void synthesized::update_history(const input_t &input, const output_t &output) {
                    var_history.add_value({
                        ${indentLines(generateHistoryValues(), 24)}
                    });
                }
            }
        """.trimIndent()
    }

    private fun generateStructMembers(vars: Map<String, SMVType>): Iterable<String> =
            vars.map { (name, type) ->
                "${generateCppDataType(type)} ${variableNames.getValue(name)};"
            }

    private fun generateOutputEqualityComparison() =
            if (outputs.keys.isEmpty()) "true" else {
                outputs.keys.map { variableNames.getValue(it) }.joinToString(" && ") { "$it == other.$it" }
            }

    private fun generateStateChecks(): Iterable<String> =
            states.foldIndexed(listOf()) { tableIndex, lines, rowStates ->
                lines + rowStates.foldIndexed(listOf<String>()) { rowIndex, acc, rowState ->
                    val index = unrolledRowOffsets[tableIndex] + rowIndex
                    val inputCheckExpr = generateCheckExpression(rowState.row.inputExpr)
                    if (inputCheckExpr.contains("output.")) {
                        throw IllegalArgumentException("Referring to output variables in assumptions is unsupported")
                    }
                    acc + "if (state[${index}] and not (${inputCheckExpr})) {" +
                            "    state[${index}] = false;" +
                            "}"
                }
            }

    private fun generateOutputFunctions(): Iterable<String> =
            states.foldIndexed(listOf()) { tableIndex, lines, rowStates ->
                val memoizedOutputFunctions = mutableMapOf<TableRow, List<String>>()

                lines + rowStates.foldIndexed(listOf<String>()) { rowIndex, acc, rowState ->
                    val index = unrolledRowOffsets[tableIndex] + rowIndex
                    val inputCheckExpr = generateCheckExpression(rowState.row.inputExpr)
                    val outputFunctions = memoizedOutputFunctions.getOrPut(rowState.row,
                            { generateOutputFunctions(rowState.row.outputExpr) })

                    acc + "if (state[${index}] and (${inputCheckExpr})) {" +
                            outputFunctions.map { line -> "    $line" } +
                            "}"
                }
            }

    // TODO: special case simple expressions (?)
    // TODO: support "one BDD per whole row", "one BDD per state combination" and "big BDD" modes
    //       prerequisite for the second one: we need a way to signal unsatisfiability and a fallback mechanism
    //                                        based on row priority
    //       third one: encode automaton state into formula, generate 1 huge ITE cascade for all GTTs and variables
    private fun generateOutputFunctions(outputExpr: Map<String, SMVExpr>): List<String> {
        // figure out all other variables we need for each output variable
        val variableDependencies = outputExpr.mapValues { (name, expr) ->
            expr.accept(OutputExpressionDependencyVisitor(outputs.keys, name))
        }

        // convert all input/history variables we need for any expression to bitmaps
        val conversions = variableDependencies.values.flatten().filter { (_, isOutput) -> !isOutput }.map { (v, _) ->
            "auto ${variableNames.getValue(v)} = to_bitset(${translator.variableReplacement.getValue(v)});"
        }

        // figure out dependencies between the different outputs and sort topologically
        val outputDependencies = variableDependencies.values.foldIndexed(listOf<Pair<Int, Int>>()) { i, acc, deps ->
            acc + deps.filter { (_, isOutput) -> isOutput }
                    .map { (outputVariable, _) -> Pair(variableDependencies.keys.indexOf(outputVariable), i) }
        }
        val sortedOutputs = topologicalSort(variableDependencies.keys.toList(), outputDependencies)
                ?: throw IllegalArgumentException("Circular output dependencies are unsupported")

        // generate bitset declarations for each output variable
        val outputDeclarations = sortedOutputs.map { variableName ->
            val name = variableNames.getValue(variableName)
            "auto $name = std::bitset<bit_size_v<decltype(output.${name})>>();"
        }

        // generate ITE expression for each output variable in the right order
        val outputCalculations = sortedOutputs.fold(listOf<String>()) { acc, resultVariable ->
            acc + synthesizer.synthesize(
                    outputExpr.getValue(resultVariable),
                    listOf(resultVariable),
                    (variableDependencies.getValue(resultVariable) + Pair(resultVariable, false)).map { (v, _) ->
                        v to generateCppDataType(
                                inputs[v] ?: outputs[v] ?: references.getValue(v)
                        )
                    }.toMap(),
                    variableNames
            )
        }

        // convert output variable bitsets to results
        val outputAssignments = sortedOutputs.map { varName ->
            "from_bitset(${variableNames.getValue(varName)}, ${translator.variableReplacement.getValue(varName)});"
        }

        return conversions + outputDeclarations + outputCalculations + outputAssignments
    }

    private fun generateStateProgression(): Iterable<String> =
            states.foldIndexed(listOf()) { tableIndex, lines, rowStates ->
                lines + rowStates.foldIndexed(listOf<String>()) { rowIndex, acc, rowState ->
                    val index = unrolledRowOffsets[tableIndex] + rowIndex
                    val outputCheckExpr = generateCheckExpression(rowState.row.outputExpr)
                    val outgoingTransitions = automata[tableIndex].getOutgoingTransition(rowState)
                    val successors = states.foldIndexed(listOf<Int>()) { successorTableIndex, successors, rowStates ->
                        successors + rowStates.mapIndexed { successorRowIndex, successorCandidate ->
                            val successorIndex = unrolledRowOffsets[successorTableIndex] + successorRowIndex
                            Pair(successorIndex, outgoingTransitions.any { it.to == successorCandidate })
                        }.filter { (_, isSuccessor) -> isSuccessor }.map { (i, _) -> i }
                    }
                    acc + "if (state[${index}] and (${outputCheckExpr})) {" +
                            successors.map { "    new_state[${it}] = true;" } +
                            "}"
                }
            }

    private fun generateHistoryValues(): Iterable<String> =
            referenceVariables.keys.map { "${translator.variableReplacement.getValue(it)}," }

    private fun generateCheckExpression(expressions: Map<String, SMVExpr>) =
            if (expressions.isEmpty()) "true" else expressions.values.joinToString(" and ") { it.accept(translator) }

    private fun generateCppDataType(type: SMVType): CppType = when (type) {
        is SMVTypes.BOOLEAN -> CppType.BOOL
        is SMVWordType -> when (type.width) {
            8 -> if (type.signed) CppType.INT8 else CppType.UINT8
            16 -> if (type.signed) CppType.INT16 else CppType.UINT16
            32 -> if (type.signed) CppType.INT32 else CppType.UINT32
            64 -> if (type.signed) CppType.INT64 else CppType.UINT64
            else -> throw IllegalStateException("Unexpected integer width") //TODO weigl: error(...)
        }
        else -> throw IllegalArgumentException("Data types other than bool and int are currently unsupported")
    }

    private fun indentLines(iter: Iterable<String>, indent: Int): String =
            iter.joinToString(separator = "\n" + " ".repeat(indent))


    /**
     * Accumulates values from all SVariables in the expression
     */
    abstract class SVariableVisitor<T> : SMVAstDefaultVisitorNN<Set<T>>() {
        final override fun defaultVisit(top: SMVAst): Set<T> = setOf()

        abstract override fun visit(v: SVariable): Set<T>

        final override fun visit(be: SBinaryExpression): Set<T> =
                be.left.accept(this) + be.right.accept(this)

        final override fun visit(ue: SUnaryExpression): Set<T> = ue.expr.accept(this)

        final override fun visit(a: SAssignment): Set<T> = a.target.accept(this) + a.expr.accept(this)

        final override fun visit(ce: SCaseExpression): Set<T> =
                ce.cases.fold(setOf()) { set, case ->
                    set + case.condition.accept(this) + case.then.accept(this) }
    }


    /**
     * Extracts SVariables matching the given pattern from an expression
     */
    class SVariableCollector(private val pattern: Regex) : SVariableVisitor<Pair<String, MatchResult>>() {
        override fun visit(v: SVariable): Set<Pair<String, MatchResult>> =
                pattern.find(v.name)?.let { match -> setOf(Pair(v.name, match)) } ?: setOf()
    }


    /**
     * Extracts the dependencies to output variables (other than self) and other variables from an expression
     */
    class OutputExpressionDependencyVisitor(private val outputVariables: Set<String>, private val self: String) :
            SVariableVisitor<Pair<String, Boolean>>() {
        override fun visit(v: SVariable): Set<Pair<String, Boolean>> =
                if (v.name == self) setOf() else setOf(Pair(v.name, outputVariables.contains(v.name)))
    }
}


class ExpressionSynthesizer(omegaVenv: File? = null) {
    private val pythonExecutable: String = omegaVenv?.let { virtualEnv ->
        if (virtualEnv.resolve("bin/python").exists()) {
            // UNIX-like OS
            virtualEnv.resolve("bin/python").absolutePath
        } else {
            // Windows
            virtualEnv.resolve("Scripts/python.exe").absolutePath
        }
    } ?: "python"

    fun synthesize(formula: SMVExpr, resultVariables: Iterable<String>, variables: Map<String, CppType>,
                   variableNameMap: Map<String, String>): List<String> =
            // TODO: detect and handle common sub-expressions
            callOmega(
                    formula.accept(SmvToOmegaTranslator(variableNameMap)),
                    resultVariables.map { variableNameMap.getValue(it) },
                    variables.map { (variable, type) ->
                        "${variableNameMap.getValue(variable)}${cppToOmegaType(type)}"
                    }
            ).let { expressions ->
                omegaExpressionsToCpp(expressions, variables.keys.map { variableNameMap.getValue(it) })
            }.dropLastWhile { it.isWhitespace() }.lines().map { "$it;" }

    //TODO weigl: Why not as a member function for CppType?
    private fun cppToOmegaType(cppType: CppType): String {
        return when (cppType) {
            CppType.BOOL -> ":bool"
            CppType.INT8 -> "[${Byte.MIN_VALUE},${Byte.MAX_VALUE}]"
            CppType.INT16 -> "[${Short.MIN_VALUE},${Short.MAX_VALUE}]"
            CppType.INT32 -> "[${Int.MIN_VALUE},${Int.MAX_VALUE}]"
            CppType.INT64 -> "[${Long.MIN_VALUE},${Long.MAX_VALUE}]"
            // Kotlin's unsigned types are currently experimental, so avoid using their constants here
            CppType.UINT8 -> "[0,${Byte.MAX_VALUE.toShort() * 2 + 1}]"
            CppType.UINT16 -> "[0,${Short.MAX_VALUE.toInt() * 2 + 1}]"
            CppType.UINT32 -> "[0,${Int.MAX_VALUE.toLong() * 2 + 1}]"
            CppType.UINT64 -> "[0,${Long.MAX_VALUE.toBigInteger() * 2.toBigInteger() + 1.toBigInteger()}]"
        }
    }

    companion object { // see also formula_to_ite.py (prefix/suffix expression are also defined there)
        //language=regexp
        private const val TOKEN_PREFIX = """([(,\s]|^)""" // space, start of line, comma or opening parens
        //language=regexp
        private const val TOKEN_SUFFIX = """([),\s]|$)""" // space, end of line, comma or closing parens
        private val ITE_BOOL_LITERAL_REGEX =
                // capturing groups: possible prefixes, literal, possible suffixes
                Regex("""$TOKEN_PREFIX(TRUE|FALSE)$TOKEN_SUFFIX""")

        private fun iteVariableRegex(variableNames: Iterable<String>): Regex =
                // capturing groups: possible prefixes, variable name, accessed bit, possible suffixes
                Regex("""$TOKEN_PREFIX(${variableNames.joinToString("|")})(?:_([0-9]+))?$TOKEN_SUFFIX""")
    }

    private fun omegaExpressionsToCpp(omegaExpression: String, variableNames: Iterable<String>): String =
            omegaExpression
                    .replace("~", "not")
                    .replace(ITE_BOOL_LITERAL_REGEX) { match ->
                        val (prefix, literal, suffix) = match.destructured
                        "${prefix}${literal.toLowerCase()}${suffix}"
                    }
                    .replace(iteVariableRegex(variableNames)) { match ->
                        val (prefix, variable, bit, suffix) = match.destructured
                        // if no bit was specified, it's a bool -> access bit 0 of the bitset
                        "${prefix}${variable}[${if (bit.isNotEmpty()) bit else "0"}]${suffix}"
                    }

    private fun callOmega(formula: String, resultVariables: List<String>, variableDefinitions: List<String>): String {
        val arguments = listOf(pythonExecutable, "-") + resultVariables.fold(listOf<String>()) { acc, resultVariable ->
            acc + "--result" + resultVariable
        } + formula + variableDefinitions
        val process = ProcessBuilder(arguments)
                .redirectInput(ProcessBuilder.Redirect.PIPE)
                .redirectOutput(ProcessBuilder.Redirect.PIPE)
                .redirectError(ProcessBuilder.Redirect.PIPE)
                .start()

        process.outputStream.use { stdin ->
            javaClass.getResourceAsStream("/synthesis/formula_to_ite.py").use { script ->
                script.transferTo(stdin)
            }
        }

        val exitCode = process.waitFor()

        process.errorStream.use { stderr ->
            stderr.bufferedReader().use { reader ->
                for (line in reader.readLines()) {
                    // silence warnings about omega using its Python backend
                    if (line == "`omega.symbolic.symbolic` failed to import `dd.cudd`." ||
                            line == "Will use `dd.autoref`.") {
                        debug("Expression synthesis script wrote to stderr: $line")
                    } else {
                        error("Expression synthesis script wrote to stderr: $line")
                    }
                }
            }
        }

        if (exitCode != 0) {
            throw IllegalStateException("Synthesis via omega failed (formula: ${formula})")
        }

        process.inputStream.use { stdout ->
            return stdout.bufferedReader().use { reader ->
                reader.readText()
            }
        }
    }


    /**
     * Translates SMV expressions to expressions the omega library understands
     */
    class SmvToOmegaTranslator(private val variableNameMap: Map<String, String>) : SMVAstDefaultVisitorNN<String>() {
        override fun defaultVisit(top: SMVAst): String = throw IllegalArgumentException("unsupported expression $top")

        override fun visit(v: SVariable): String = variableNameMap.getValue(v.name)

        override fun visit(be: SBinaryExpression): String =
                "(${be.left.accept(this)} ${opToOmega(be.operator, be.left.dataType)} ${be.right.accept(this)})"

        private fun opToOmega(op: SBinaryOperator, type: SMVType?): String = when (type) {
            SMVTypes.BOOLEAN -> when (op) {
                SBinaryOperator.AND -> """/\"""
                SBinaryOperator.EQUAL, SBinaryOperator.EQUIV, SBinaryOperator.XNOR -> "<=>"
                SBinaryOperator.IMPL -> "=>"
                SBinaryOperator.NOT_EQUAL, SBinaryOperator.XOR -> "^"
                SBinaryOperator.OR -> """\/"""
                else -> throw IllegalArgumentException("unsupported binary boolean operator $op")
            }
            SMVTypes.INT, is SMVWordType -> when (op) {
                SBinaryOperator.PLUS -> "+"
                SBinaryOperator.MINUS -> "-"
                SBinaryOperator.MUL -> "*"
                SBinaryOperator.DIV -> "/"
                SBinaryOperator.MOD -> "%"
                SBinaryOperator.EQUAL, SBinaryOperator.EQUIV -> "="
                SBinaryOperator.NOT_EQUAL -> "!="
                SBinaryOperator.GREATER_THAN -> ">"
                SBinaryOperator.GREATER_EQUAL -> ">="
                SBinaryOperator.LESS_THAN -> "<"
                SBinaryOperator.LESS_EQUAL -> "<="
                else -> throw IllegalArgumentException("unsupported binary integer operator $op")
            }
            else -> throw IllegalArgumentException("unsupported expression type $type")
        }

        override fun visit(ue: SUnaryExpression): String =
                "(${opToOmega(ue.operator, ue.expr.dataType)} ${ue.expr.accept(this)})"

        private fun opToOmega(op: SUnaryOperator, type: SMVType?): String = when (type) {
            SMVTypes.BOOLEAN -> when (op) {
                SUnaryOperator.NEGATE -> "~"
                else -> throw IllegalArgumentException("unsupported unary boolean operator $op")
            }
            SMVTypes.INT, is SMVWordType -> when (op) {
                SUnaryOperator.MINUS -> "0 -" // omega doesn't seem to understand unary minus
                else -> throw IllegalArgumentException("unsupported unary integer operator $op")
            }
            else -> throw IllegalArgumentException("unsupported expression type $type")
        }

        override fun visit(l: SLiteral): String = when (l) {
            SLiteral.FALSE -> "FALSE"
            SLiteral.TRUE -> "TRUE"
            else -> l.value.toString()
        }

        override fun visit(a: SAssignment): String = when (a.target.dataType) {
            SMVTypes.BOOLEAN -> "(${a.target.accept(this)} <=> ${a.expr.accept(this)})"
            SMVTypes.INT -> "(${a.target.accept(this)} = ${a.expr.accept(this)})"
            else -> throw IllegalArgumentException("unsupported expression type ${a.target.dataType}")
        }

        override fun visit(ce: SCaseExpression): String = ce.cases.fold(StringBuilder()) { sb, case ->
            sb.append("ite(${case.condition.accept(this)},${case.then.accept(this)},")
        }.append(")".repeat(ce.cases.size)).toString()
    }
}


/**
 * Supported C++ variable types
 */
enum class CppType(private val cppName: String) {
    BOOL("bool"),
    UINT8("std::uint8_t"),
    UINT16("std::uint16_t"),
    UINT32("std::uint32_t"),
    UINT64("std::uint64_t"),
    INT8("std::int8_t"),
    INT16("std::int16_t"),
    INT32("std::int32_t"),
    INT64("std::int64_t");

    override fun toString(): String = cppName
}


/**
 * Returns a new, topologically sorted vertex list or null if the graph is not acyclic
 */
fun <T> topologicalSort(vertices: List<T>, edges: Iterable<Pair<Int, Int>>): List<T>? {
    val inEdges = HashMap<Int, MutableSet<Int>>(vertices.size)
    val outEdges = HashMap<Int, MutableSet<Int>>(vertices.size)

    edges.forEach { (u, v) ->
        if (outEdges.containsKey(u)) {
            outEdges.getValue(u).add(v)
        } else {
            outEdges[u] = mutableSetOf(v)
        }
        if (inEdges.containsKey(v)) {
            inEdges.getValue(v).add(u)
        } else {
            inEdges[v] = mutableSetOf(u)
        }
    }

    val result = mutableListOf<T>()
    val todo = vertices.mapIndexed { i, v -> Pair(i, v) }.filter { !inEdges.containsKey(it.first) }.toMutableList()

    while (todo.isNotEmpty()) {
        val indexedVertex = todo.first()
        todo.removeAt(0)
        result.add(indexedVertex.second)
        outEdges[indexedVertex.first]?.forEach { target ->
            inEdges.getValue(target).remove(indexedVertex.first)
            if (inEdges.getValue(target).isEmpty()) {
                todo.add(Pair(target, vertices[target]))
            }
        }
    }

    if (inEdges.any { it.value.isNotEmpty() }) {
        return null
    }

    return result
}
