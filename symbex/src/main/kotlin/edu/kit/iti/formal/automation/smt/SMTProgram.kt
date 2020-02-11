package edu.kit.iti.formal.automation.smt

import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SExprFacade.sexpr
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SSymbol
import java.util.*

/**
 * This class represents a reactive program in SMT formulas.
 *
 *
 * Additionally it provides some meta data over these function.
 *
 *
 * An SMT program consist out of three parts:
 *
 *  * A predicate *init(X)* for valid initial states *X*
 *  * A predicate *next(X,I,X')* for valid successor states
 *  * A description of states *X*
 *  * A description of input values *I*
 *
 *
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
class SMTProgram(
        var inputDataTypes: MutableMap<String, SExpr> = HashMap(),
        var stateDataTypes: MutableMap<String, SExpr> = HashMap(),
        var initPredicates: MutableMap<String, SExpr> = TreeMap(),
        var nextPredicates: MutableMap<String, SExpr> = TreeMap(),
        var nextDefines: MutableMap<String, SExpr> = TreeMap(),
        var initFuncName: String = "init",
        var nextFuncName: String = "next") {

    val initFunction: SExpr
        get() {
            return sexpr(
                    DEFINE_FUNCTION, initFuncName,
                    sexpr(createSortSExpr(STATE_NAME, stateDataTypes)),
                    SMT_BOOLEAN,
                    initBody)
        }

    protected val initBody: SExpr
        get() {
            val body = SList(SSymbol("and"))
            this.initPredicates.forEach { name, pred ->
                val eq = SList()
                eq.add(SSymbol("="))
                eq.add(SSymbol(STATE_NAME + SSymbol(name)))
                eq.add(pred)
                body.add(eq)
            }
            return body
        }

    val nextFunction: SExpr
        get() {
            val s = createSortSExpr(STATE_NAME, this.stateDataTypes)
            val i = createSortSExpr(STATE_NAME, this.inputDataTypes)
            val t = createSortSExpr(NEW_STATE_NAME, this.stateDataTypes)
            val args = toSExpr(s + i + t)
            val func = sexpr(DEFINE_FUNCTION, this.nextFuncName, args, SMT_BOOLEAN, nextBody)
            return func
        }

    val nextBody: SExpr
        get() {
            val body = SList()
            body.add(SSymbol("and"))
            this.nextPredicates.forEach { (name, pred) ->
                val eq = SList()
                eq.add(SSymbol("="))
                eq.add(SSymbol(NEW_STATE_NAME + name))
                eq.add(pred)
                body.add(eq)
            }

            return nextDefines.entries.toList().foldRight(body) { (k, v), acc ->
                SList("let", SList(SList(k, v) as SExpr), acc)
            }
        }

    /**
     * @return
     */
    val preamble: String
        get() {
            val sb = StringBuilder()
            sb.append("(set-logic QF_BV)\n")
            sb.append(
                    "(define-fun <> ((a Bool) (b Bool)) Bool\n" + "  (not (= a b)))\n")

            for (i in 1..64) {
                sb.append(String.format("(define-fun <> ((a (_ BitVec %d)) (b (_ BitVec %d))) Bool (not (= a b)))\n", i, i))
            }


            val init = initFunction
            val next = nextFunction
            sb.append(init.toString()).append("\n\n")
            sb.append(next.toString()).append("\n\n")
            return sb.toString()
        }

    private fun toSExpr(sortSExpr: Collection<SExpr>): SExpr = SList(sortSExpr)

    /*
    public SExpr getStateDataType() throws SExprParserException {
        return createRecord(stateDataTypeName, stateDataTypes);
    }

    public SExpr getInputDataType() throws SExprParserException {
        return createRecord(getInputDataTypeName(), inputDataTypes);
    }
    */

    fun getDefineSteps(prefix: String, suffix: String) =
            getDefineInputTypes(prefix, suffix) + getDefineStateTypes(prefix, suffix)

    fun getDefineStateTypes(prefix: String, suffix: String) = this.stateDataTypes.entries
            .map { e -> createDefineConst(prefix + e.key + suffix, e.value) }

    fun getDefineInputTypes(prefix: String, suffix: String) = this.inputDataTypes.entries
            .map { e -> createDefineConst(prefix + e.key + suffix, e.value) }

    private fun createDefineConst(name: String, sort: SExpr): SExpr =
            sexpr("declare-const", name, sort)

    /**
     * @return
     */
    fun getStepDefinition(withInput: Boolean, prefix: String = "", suffix: String = ""): String {
        val sb = StringBuilder()
        val init = getDefineInputTypes(prefix, suffix)
        val next = getDefineStateTypes(prefix, suffix)

        val vars = if (withInput) (init + next) else next

        vars.forEach { SExpr ->
            sb.append(SExpr.toString()).append("\n\n")
        }
        return sb.toString()
    }

    fun getAssertInit(suffix: String): SExpr {
        val asser = SList(SSymbol("assert"))
        val app = SList()
        asser.add(app)
        app.add(SSymbol(this.initFuncName))
        this.stateDataTypes.keys.forEach { name -> app.add(SSymbol(name + suffix)) }
        return asser
    }

    fun getAssertNext(previousSuffix: String, nextSuffix: String): SExpr {
        val asser = SList()
        asser.add(SSymbol("assert"))
        val app = SList()
        app.add(SSymbol(this.nextFuncName))
        asser.add(app)
        this.stateDataTypes.keys.forEach { name -> app.add(SSymbol(name + previousSuffix)) }


        this.inputDataTypes.keys.forEach { name -> app.add(SSymbol(name + previousSuffix)) }

        this.stateDataTypes.keys.forEach { name -> app.add(SSymbol(name + nextSuffix)) }

        return asser
    }

    companion object {
        val NEW_STATE_NAME = "new"
        val STATE_NAME = "old"
        val INPUT_NAME = "input"

        val DEFINE_FUNCTION = "define-fun"
        val SMT_BOOLEAN = "Bool"

        val DECLARE_DATATYPES = "declare-datatypes"

        /**
         * adds the given arguments in the map into the given SExprs.
         *
         * @param dt
         */
        private fun createSortSExpr(prefix: String, dt: Map<String, SExpr>) =
                dt.entries.map { entry ->
                    val s = SList()
                    s.add(SSymbol(prefix + entry.key))
                    s.add(entry.value)
                    s
                }
    }
}
