package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.defaultLazy
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.choice
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.IteLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.IteLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.IteLanguageParser
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
import edu.kit.iti.formal.util.fail
import edu.kit.iti.formal.util.info
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
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

    private val outputFolder by option("-o", "--output-dir", help = "Output directory")
            .file(exists = true, fileOkay = false, writable = true)
            .defaultLazy { Paths.get("").toAbsolutePath().toFile() }

    private val pythonExecutable by option("--python", help = "Path to python with omega",
            envvar = "PYTHON").default("python")

    private val optimizations by option("-O", "--optimization-level", help = "Optimization level")
            .choice(enumValues<OptimizationLevel>().associateBy { it.ordinal.toString() })
            .default(OptimizationLevel.SIMPLE)

    private val outputFunctionStrategy by option("--row-selection-strategy",
            help = "Strategy for choosing output function when multiple rows are active")
            .choice(enumValues<OutputFunctionStrategy>().associateBy { it.name.toLowerCase() })
            .default(OutputFunctionStrategy.ASSUME_ORTHOGONAL)

    override fun run() {
        // TODO: implement rest, set default to CHOOSE_FIRST
        require(outputFunctionStrategy == OutputFunctionStrategy.ASSUME_ORTHOGONAL) {
            "Only the strategy --assume-orthogonal is currently implemented"
        }

        val expressionSynthesizer = ExpressionSynthesizer(pythonExecutable)

        tableFiles.forEach { tableFile ->
            val programName = tableFile.name.split('.')[0]
            val headerFile = File(outputFolder, "${programName}.h")
            val moduleFile = File(outputFolder, "${programName}.cpp")

            info("Parsing DSL file: ${tableFile.absolutePath}")
            val synthesizer = ProgramSynthesizer(
                    programName, tableFile, outputFunctionStrategy, optimizations, expressionSynthesizer
            )

            info("Generating header file: ${headerFile.absolutePath}")
            headerFile.writeText(synthesizer.generateHeader())

            info("Generating module file: ${moduleFile.absolutePath}")
            moduleFile.writeText(synthesizer.generateModule())
        }
    }
}


enum class OptimizationLevel(val optimizeAssignments: Boolean) {
    NONE(false),
    SIMPLE(true);
}


/**
 * Strategy for computing the output function in nondeterministic cases.
 */
enum class OutputFunctionStrategy {
    /**
     * Always choose the output function of the first active row of each table.
     */
    CHOOSE_FIRST,
    /**
     * Always choose the output function of the last active row of each table.
     */
    CHOOSE_LAST,
    /**
     * Always choose the output function of a random active row of each table.
     */
    CHOOSE_RANDOM,
    /**
     * Assume all output functions of all rows in all tables that can be active at the same time are orthogonal (set
     * different outputs) and execute them all in order.
     */
    ASSUME_ORTHOGONAL,
    /**
     * Combine as many output functions as possible. When conflicts are detected, prefer satisfying earlier rows.
     */
    COMBINE_PREFER_FIRST,
    /**
     * Combine as many output functions as possible. When conflicts are detected, prefer satisfying later rows.
     */
    COMBINE_PREFER_LAST;
}


class ProgramSynthesizer(val name: String, tables: List<GeneralizedTestTable>,
                         private val strategy: OutputFunctionStrategy,
                         private val optimizations: OptimizationLevel,
                         private val synthesizer: ExpressionSynthesizer) {
    constructor(name: String, tableDslFile: File, strategy: OutputFunctionStrategy, optimizations: OptimizationLevel,
                synthesizer: ExpressionSynthesizer) :
            this(name, GetetaFacade.readTables(tableDslFile), strategy, optimizations, synthesizer)

    @Suppress("Unused") // meant for unit tests
    constructor(name: String, tableDsl: String, strategy: OutputFunctionStrategy, optimizations: OptimizationLevel,
                synthesizer: ExpressionSynthesizer) :
            this(name, GetetaFacade.parseTableDSL(tableDsl), strategy, optimizations, synthesizer)

    companion object {
        private val HISTORY_VAR_REGEX = Regex("""^code\$(.+)__history._\$([0-9]+)$""")
    }

    // accumulated over all tables (SVariable::name -> type)
    private val inputs = linkedMapOf<String, SMVType>()
    private val outputs = linkedMapOf<String, SMVType>()
    private val referenceVariables = linkedMapOf<String, SMVType>() // inputs and outputs referenced in references
    private val references = mutableMapOf<String, SMVType>() // the concrete references to historical values
    private var maxLookBack = 0
    // maps SVariable names to names for temporary variables / struct member names
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
        require(tables.none { it.constraintVariables.isNotEmpty() }) {
            "Global variables are currently unsupported"
        }
        require(tables.none { it.functions.isNotEmpty() }) {
            "Functions are currently unsupported"
        }
        require(tables.none { table ->
            table.programVariables.any { variable ->
                variable.name.startsWith(ExpressionSynthesizer.TEMPORARY_VARIABLE_PREFIX)
            }
        }) {
            "Variable names must not start with the prefix ${ExpressionSynthesizer.TEMPORARY_VARIABLE_PREFIX}, which " +
                    "is reserved for temporary variables"
        }

        // extract context information
        var unrolledRowCount = 0
        tables.forEach { table ->
            val inputVariables = table.programVariables.filter { it.isAssumption }.toSet()
            val variables = table.programVariables.map { it.name to it }.toMap()

            table.parseContext.let { context ->
                val historyVariables = mutableSetOf<String>()
                context.refs.forEach { (sVariable, lookBack) ->
                    historyVariables += sVariable.name
                    maxLookBack = max(maxLookBack, -lookBack)
                }
                // don't iterate over context.vars directly to preserve original declaration order
                table.programVariables.forEach programVariables@{ variable ->
                    val sVariableName = context.vars.getValue(variable).name

                    if (variableNames.containsKey(sVariableName)) return@programVariables
                    variableNames[sVariableName] = variable.name

                    if (inputVariables.contains(variable)) {
                        inputs[sVariableName] = variable.logicType
                        translator.variableReplacement[sVariableName] = "input.${variable.name}"
                    } else {
                        outputs[sVariableName] = variable.logicType
                        translator.variableReplacement[sVariableName] = "output.${variable.name}"
                    }

                    if (historyVariables.contains(sVariableName)) {
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
            }.forEach references@{ (sVariableName, match) ->
                val (variableName, lookBehind) = match.destructured
                if (references.containsKey(sVariableName)) return@references
                references[sVariableName] = variables.getValue(variableName).logicType
                translator.variableReplacement[sVariableName] = "var_history.get_value(${lookBehind}).${variableName}"
                variableNames[sVariableName] = "__history_${variableName}_${lookBehind}"
            }

            val automaton = GetetaFacade.constructTable(table).automaton
            automata.add(automaton)
            // loop over table.region.flat() instead of automaton.rowStates to preserve declaration order
            states.add(table.region.flat().flatMap { row -> automaton.rowStates.getValue(row) })
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
                
                template <typename T>
                class history<T, 0> {
                public:
                    void add_value(const T& value) {}
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
                    require(!inputCheckExpr.contains("output.")) {
                        "Referring to output variables in assumptions is unsupported"
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

    // TODO: support "one BDD per whole row", "one BDD per state combination" and "big BDD" modes
    //       prerequisite for the second one: we need a way to signal unsatisfiability and a fallback mechanism
    //                                        based on row priority
    //       third one: encode automaton state into formula, generate 1 huge ITE cascade for all GTTs and variables
    private fun generateOutputFunctions(outputExpressions: Map<String, SMVExpr>): List<String> {
        // figure out synthesis method and dependencies for each result variable
        val needsConversionToBitmap = outputExpressions.mapValues { (_, expr) ->
            !optimizations.optimizeAssignments || expr.getSingleAssignmentExpr() == null
        }
        val variableDependencies = outputExpressions.mapValues { (name, expr) ->
            expr.accept(OutputExpressionDependencyVisitor(outputs.keys, name))
        }
        val bitmapDependencies = variableDependencies.filterKeys { needsConversionToBitmap.getValue(it) }


        // all input/history variables we need for at least one bitmap expression need to be converted once
        val conversions = bitmapDependencies.values.flatten().toSet()
                .filter { (_, isOutput) -> !isOutput }
                .map { (v, _) ->
                    "auto ${variableNames.getValue(v)} = to_bitset(${translator.variableReplacement.getValue(v)});"
                }
        // non-bitmap output variables need to be converted before their first usage in a bitmap expression
        val outputConversions = mutableMapOf<String, List<String>>()
        val convertedOutputs = mutableSetOf<String>()
        bitmapDependencies.forEach { (variable, dependencies) ->
            val outputDependencies = dependencies.filter { (_, isOutput) -> isOutput }.map { (dep, _) -> dep }.toSet()
            val newConversions = (outputDependencies - convertedOutputs)
                    .filter { !needsConversionToBitmap.getValue(it) }
            outputConversions[variable] = newConversions.map { v ->
                "auto ${variableNames.getValue(v)} = to_bitset(${translator.variableReplacement.getValue(v)});"
            }
            convertedOutputs.addAll(newConversions)
        }

        // figure out dependencies between the different outputs and sort topologically
        val outputDependencies = variableDependencies.values.foldIndexed(listOf<Pair<Int, Int>>()) { i, acc, deps ->
            acc + deps.filter { (_, isOutput) -> isOutput }
                    .map { (outputVariable, _) -> Pair(variableDependencies.keys.indexOf(outputVariable), i) }
        }
        val sortedOutputs = requireNotNull(topologicalSort(variableDependencies.keys.toList(), outputDependencies)) {
            "Circular output dependencies are unsupported"
        }

        // generate ITE expression for each output variable in the right order
        val context = synthesizer.CppContext(variableNames)
        val outputCalculations = sortedOutputs.flatMap { resultVariable ->
            val expr = outputExpressions.getValue(resultVariable)
            val name = variableNames.getValue(resultVariable)
            if (!needsConversionToBitmap.getValue(resultVariable)) {
                listOf("output.$name = ${expr.getSingleAssignmentExpr()!!.accept(translator)};")
            } else {
                val variables = variableDependencies.getValue(resultVariable) + Pair(resultVariable, false)
                outputConversions.getValue(resultVariable) +
                        "auto $name = std::bitset<bit_size_v<decltype(output.$name)>>();" +
                        synthesizer.synthesize(
                                expr,
                                listOf(resultVariable),
                                variables.map { (v, _) ->
                                    v to generateCppDataType(
                                            inputs[v] ?: outputs[v] ?: references.getValue(v)
                                    )
                                }.toMap(),
                                context
                        ) +
                        "from_bitset(${name}, output.$name);"
            }
        }

        return conversions + outputCalculations
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
            else -> fail("Unexpected integer width")
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
                    set + case.condition.accept(this) + case.then.accept(this)
                }
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


class ExpressionSynthesizer(private val pythonExecutable: String = "python") {

    companion object {
        const val TEMPORARY_VARIABLE_PREFIX = "__tmp"
    }

    fun synthesize(formula: SMVExpr, resultVariables: Iterable<String>, variables: Map<String, CppType>,
                   context: CppContext): List<String> =
            callOmega(
                    formula.accept(SmvToOmegaTranslator(context.variableNameMap)),
                    resultVariables.map { context.variableNameMap.getValue(it) },
                    variables.map { (variable, type) ->
                        "${context.variableNameMap.getValue(variable)}${cppToOmegaType(type)}"
                    }
            ).let { assignments -> context.translateIteAssignments(assignments, variables) }

    inner class CppContext(val variableNameMap: Map<String, String>) {
        private var temporaryVariableCounter = 0

        fun translateIteAssignments(iteAssignments: Iterable<String>, variables: Map<String, CppType>): List<String> {
            val translator = IteToCppTranslator(
                    variables.mapKeys { (k, _) -> variableNameMap.getValue(k) },
                    TEMPORARY_VARIABLE_PREFIX, temporaryVariableCounter
            )
            val assignments = iteAssignments.map { expression ->
                val parser = IteLanguageParser(CommonTokenStream(IteLanguageLexer(CharStreams.fromString(expression))))
                "${parser.assignment().accept(translator)};"
            }
            val temporaries = translator.getVariableDeclarations()
            temporaryVariableCounter += temporaries.size
            return temporaries + assignments
        }
    }

    private fun cppToOmegaType(cppType: CppType): String = when (cppType) {
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

    private fun callOmega(formula: String, resultVariables: List<String>, definitions: List<String>): Iterable<String> {
        val arguments = listOf(pythonExecutable, "-") +
                resultVariables.flatMap { resultVariable -> listOf("--result", resultVariable) } +
                formula + definitions
        val outputFile = createTempFile()
        val process = ProcessBuilder(arguments)
                .redirectInput(ProcessBuilder.Redirect.PIPE)
                .redirectOutput(outputFile)
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
            fail("Synthesis via omega failed (formula: ${formula})")
        }

        return outputFile.bufferedReader().use { reader ->
            reader.readLines().dropLastWhile { it.isEmpty() }
        }
    }


    /**
     * Translates SMV expressions to expressions the omega library understands
     */
    private class SmvToOmegaTranslator(private val variableNameMap: Map<String, String>) :
            SMVAstDefaultVisitorNN<String>() {
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

    private class IteToCppTranslator(private val variableContext: Map<String, CppType>,
                                     private val cacheVarPrefix: String, private val initialCacheVarSuffix: Int) :
            IteLanguageBaseVisitor<String>() {
        private val iteExprCache = linkedMapOf<String, String>() // preserving insertion order is crucial

        fun getVariableDeclarations(): List<String> =
                iteExprCache.map { (expr, varName) -> "bool $varName = $expr;" }

        override fun visitAssignment(ctx: IteLanguageParser.AssignmentContext): String =
                "${ctx.identifier().accept(this)} = ${ctx.expr().accept(this)}"

        override fun visitExpr(ctx: IteLanguageParser.ExprContext): String =
                ctx.iteExpr()?.accept(this)
                        ?: ctx.expr()?.let { "(not ${it.accept(this)})" }
                        ?: ctx.identifier()?.accept(this)
                        ?: ctx.BOOLEAN()?.text?.toLowerCase()
                        ?: ctx.INTEGER()!!.text

        override fun visitIteExpr(ctx: IteLanguageParser.IteExprContext): String =
                iteExprCache.getOrPut(
                        "(${ctx.expr(0).accept(this)}) ? (${ctx.expr(1).accept(this)}) : ${ctx.expr(2).accept(this)}",
                        { "${cacheVarPrefix}_${initialCacheVarSuffix + iteExprCache.size}" }
                )

        override fun visitIdentifier(ctx: IteLanguageParser.IdentifierContext): String =
                if (variableContext.containsKey(ctx.text) && variableContext[ctx.text] == CppType.BOOL) {
                    "${ctx.text}[0]"
                } else { // identifier must refer to a specific bit
                    "${ctx.text.substringBeforeLast('_')}[${ctx.text.substringAfterLast('_')}]"
                }
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
 * Checks if a SMVExpr is a value assignment to a SVariable and returns the corresponding expression.
 */
private fun SMVExpr.getSingleAssignmentExpr(): SMVExpr? =
        (this as? SBinaryExpression)?.takeIf { operator == SBinaryOperator.EQUAL }?.run {
            right.takeIf { left is SVariable } ?: left.takeIf { right is SVariable }
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
