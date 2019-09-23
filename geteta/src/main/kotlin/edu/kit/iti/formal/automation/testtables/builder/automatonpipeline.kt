package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.testtables.algorithms.StateReachability
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.SpecialState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.automata.TransitionType
import edu.kit.iti.formal.automation.testtables.model.options.Mode
import kotlin.collections.set

class AutomatonBuilderPipeline(
        val table: GeneralizedTestTable,
        var steps: List<AutomatonConstructionTransformer> = listOf()) {
    init {
        steps = listOf(
                RowGroupExpander(),
                InitialAutomataCreator(),
                if (table.options.mode == Mode.CONCRETE_TABLE)
                    AutomatonConcretizerTransformation()
                else
                    RowStateCreator(),
                TransitionCreator(),
                InitialReachability()
        )//AddMutualExclusionForStates())
    }

    fun transform(): AutomataTransformerState {
        val automaton = TestTableAutomaton()
        val init = AutomataTransformerState(table, automaton)
        steps.fold(init) { acc, transformer -> transformer.transform(acc);acc }
        return init
    }
}

val Duration.minimum: Int
    get() = when (this) {
        is Duration.OpenInterval -> lower
        is Duration.ClosedInterval -> lower
        is Duration.Omega -> 0
    }

val Duration.maximum: Int
    get() = when (this) {
        is Duration.OpenInterval -> minimum + 1
        is Duration.ClosedInterval -> upper
        is Duration.Omega -> 1
    }


val stateNameError = "__ERROR__"
val stateNameSentinel = "__SENTINEL__"


/**
 * If the gtt contains a row group with a minimum amount of iteration, we expand it under maintaining
 * the reachability.
 *
 * Also maintins [AutomataTransformerState.flatRegion] and [AutomataTransformerState.stateReachability]
 */
open class RowGroupExpander : AbstractTransformer<AutomataTransformerState>() {
    override fun transform() {
        model.testTable.region = rewrite(model.testTable.region)
        model.flatRegion = model.testTable.region.flat()
        model.stateReachability = StateReachability(model.testTable.region)
    }

    companion object {
        /**
         * creates a new region, expand the children and itself.
         */
        fun rewrite(region: Region): Region {
            val m = region.duration.minimum
            //expand this region if necessary
            val r = if (m == 0) region else expand(region)

            val children = ArrayList<TableNode>(r.children.size)
            //expand this region if necessary
            for (child in r.children) {
                when (child) {
                    is TableRow -> children.add(child)
                    is Region -> children.add(rewrite(child))
                }
            }
            r.children = children
            return r
        }

        /**
         * Unwind the given region
         */
        fun expand(r: Region): Region {
            if (r.duration == Duration.Omega || !r.duration.isRepeatable
                    || r.duration.minimum == 0) {
                return r
            }
            val seq = ArrayList<TableNode>(r.children.size)
            val m = r.duration.maximum
            for (iter in 1..m) {
                val t = Region(r.id + "_${iter}")
                t.duration = when {
                    (iter == m && r.duration is Duration.OpenInterval) ->
                        Duration.OpenInterval(0, r.duration.pflag)
                    (r.duration is Duration.ClosedInterval && r.duration.minimum < iter && iter <= r.duration.maximum) ->
                        Duration.ClosedInterval(0,1, r.duration.pflag)
                    else ->
                        Duration.ClosedInterval(1, 1, r.duration.pflag)
                }

                r.children.forEach {
                    t.children.add(it.clone().also { it.id = "${t.id}_${it.id}" })
                }
                seq.add(t)
            }
            val new = Region(r.id, seq)
            new.duration = Duration.ClosedInterval(1, 1, false)
            return new
        }
    }
}

class InitialAutomataCreator : AbstractTransformer<AutomataTransformerState>() {
    override fun transform() {
        model.automaton.stateError = SpecialState(stateNameError)
        model.automaton.stateSentinel = SpecialState(stateNameSentinel)
    }
}

/*        model.tableModule.stateVars.add(model.errorVariable)

        // disable in the beginning
        model.tableModule.initExpr.add(model.errorVariable.not())

        val e = model.testTable.region.flat().stream()
                .flatMap { s -> s.automataStates.stream() }
                .map { s -> s.defFailed as SMVExpr }
                .reduce { a, b -> a.or(b) }
                .orElse(SLiteral.TRUE)
        val a = SAssignment(model.errorVariable, e)
        model.tableModule.nextAssignments.add(a)

        val e = model.sentinelState.automataStates[0].incoming.stream()
                .map { it.defForward }
                .map { fwd -> fwd as SMVExpr }
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElse(SLiteral.FALSE)
        val a = SAssignment(endSentinel, e.or(endSentinel))
        tm.nextAssignments.add(a)
*/

/**
 * Creates the rowStates and definition for each row and cycle including error and endSentinel.
 * Created by weigl on 17.12.16.
 *
 * @version 3
 */
open class RowStateCreator : AbstractTransformer<AutomataTransformerState>() {
    override fun transform() {
        val flat = model.flatRegion
        flat.forEach { this.introduceState(it) }
    }

    open fun createRowStates(s: TableRow): List<RowState> {
        val duration = s.duration
        return when (duration) {
            is Duration.Omega -> {
                val a = RowState(s, 1)
                a.strongRepetition = true
                listOf(a)
            }
            is Duration.OpenInterval ->
                if (duration.lower == 0) {
                    listOf(RowState(s, 1).also { a ->
                        a.optional = true
                        a.weakRepeat = true
                        a.progressFlag = duration.pflag
                    })
                } else
                    (1..duration.lower).map {
                        RowState(s, it).also { a ->
                            a.optional = it == duration.lower
                            a.weakRepeat = a.optional
                            if (a.optional)
                                a.progressFlag = duration.pflag
                        }
                    }
            is Duration.ClosedInterval ->
                (1..duration.upper).map {
                    RowState(s, it).also { a ->
                        a.optional = it >= duration.lower
                        if (a.optional)
                            a.progressFlag = duration.pflag
                    }
                }
        }
    }

    private fun introduceState(s: TableRow) {
        val states = createRowStates(s)
        model.automaton.rowStates[s] = states
    }
}


/**
 * Creates an mutual exclusion for states, based on the progress flag.
 *
class AddMutualExclusionForStates : AbstractTransformer<AutomataTransformerState>() {
override fun transform() {
model.testTable.region.flat().forEach {
if(it.duration.pflag){
val astate = model.automaton.getState(it,)
model.automaton.mutualExclusiveStates.computeIfAbsent()
it.outgoing
}
}

//TODO("not implemented")
}
}*/

class InitialReachability : AbstractTransformer<AutomataTransformerState>() {
    override fun transform() {
        model.flatRegion
                .filter { it.isInitialReachable }
                .forEach { it ->
                    val astate = model.automaton.getState(it, 0)
                    astate?.let { model.automaton.initialStates += it }
                }
    }
}

class TransitionCreator : AbstractTransformer<AutomataTransformerState>() {
    override fun transform() {
        model.flatRegion.forEach(this::internalTransitions)
        model.flatRegion.forEach(this::externalTransitions)
        errorTransitions()
        sentinelTransitions()
        selfLoops()
    }

    private fun sentinelTransitions() {
        val sentinel = model.stateReachability.endSentinel
        val sentinelState = model.automaton.stateSentinel

        sentinel.incoming.forEach { it ->
            model.automaton.getStates(it)
                    ?.filter { it.optional }
                    ?.forEach { oFrom ->
                        model.automaton.addTransition(oFrom, sentinelState, TransitionType.ACCEPT)
                    }
        }
    }

    private fun selfLoops() {
        model.automaton.rowStates.values.flatMap { it }
                .filter { it.weakRepeat || it.strongRepetition }
                .forEach {
                    model.automaton.addTransition(it, it,
                            transitionTypeAccept(it.row.duration))
                }

        model.automaton.addTransition(model.automaton.stateSentinel,
                model.automaton.stateSentinel, TransitionType.TRUE)
    }

    private fun errorTransitions() {
        val errorState = model.automaton.stateError
        model.flatRegion.forEach {
            model.automaton.getStates(it)?.forEach { state ->
                model.automaton.addTransition(
                        state, errorState, TransitionType.FAIL)
            }
        }
    }

    private fun internalTransitions(s: TableRow) {
        model.automaton.getStates(s)?.let { states ->
            states.zipWithNext { a, b ->
                val pflag = s.duration.pflag && s.duration.isOptional(a.time)
                model.automaton.addTransition(a, b,
                        if (pflag) TransitionType.ACCEPT_PROGRESS else TransitionType.ACCEPT)
            }
        }
    }

    private fun externalTransitions(s: TableRow) {
        val jumpOut = model.automaton.getStates(s)?.filter { it.optional } ?: listOf()
        s.outgoing.filter { it != model.stateReachability.endSentinel }
                .forEach { to ->
                    model.automaton.getFirstState(to)?.let { toState ->
                        jumpOut.forEach { out ->
                            model.automaton.addTransition(out, toState,
                                    transitionTypeAccept(s.duration))
                        }
                    }
                }
    }
}

/**
 * This transformation ensures a specified minimal execution of cycles in rows.
 */
class AutomatonConcretizerTransformation : RowStateCreator() {
    override fun createRowStates(s: TableRow): List<RowState> {
        val cto = model.testTable.options.cycles
        val c = cto.getCount(s.id, s.duration)
        s.duration = Duration.ClosedInterval(c, c, false)
        return super.createRowStates(s)
    }
}


/*
 *
private fun introduceAutomatonState(automatonTableRow: TableRow.AutomatonState) {
val `var` = automatonTableRow.smvVariable

// sate variable
model.tableModule.stateVars.add(`var`)

//initialize state variable with true iff isStartState
model.tableModule.initExpr.add(if (automatonTableRow.isStartState) `var` else `var`.not())

//If one predeccor is true, then we are true.
var incoming: Stream<TableRow.AutomatonState> = automatonTableRow.incoming.stream()

//remove self-loop on DET_WAIT, because we cannot use `_fwd`, we need `_keep`
if (automatonTableRow.state.duration.isDeterministicWait) {
incoming = incoming.filter { `as` -> `as` != automatonTableRow }
}

var activate = incoming
.map { inc ->
var fwd: SMVExpr = inc.defForward
/* If incoming state is det.wait, then this state becomes only active
 *  if it has not fired before.
*/
if (inc.state.duration.isDeterministicWait) {
val inputAndState = automatonTableRow.smvVariable.and(automatonTableRow.state.defInput).not()
fwd = fwd.and(inputAndState)
}
fwd
}
.map { SMVExpr::class.java.cast(it) }
.reduce(SMVFacade.reducer(SBinaryOperator.OR))
.orElse(SLiteral.FALSE)


if (automatonTableRow.state.duration.isDeterministicWait) {
// If this state is true, it stays true, until
// no successor was correctly guessed.
activate = activate.or(
`var`.and(automatonTableRow.state.defProgress
))
//TODO add following state (s->!s_in)
}

/*
if (automatonTableRow.isUnbounded()) {
or = SMVFacade.combine(SBinaryOperator.OR, or,
automatonTableRow.getDefForward());
}*/

val assignment = SAssignment(
automatonTableRow.smvVariable, activate)
model.tableModule.nextAssignments.add(assignment)
}


private fun define(defOutput: SVariable, combine: SMVExpr) {
model.tableModule.definitions[defOutput] = combine
}
}

private val Duration.isDeterministicWait: Boolean
get() =
when (this) {
is Duration.OpenInterval -> pflag
is Duration.ClosedInterval -> pflag
else -> false
}
 */


private fun transitionTypeAccept(duration: Duration) =
        if (duration.pflag) TransitionType.ACCEPT_PROGRESS
        else TransitionType.ACCEPT
