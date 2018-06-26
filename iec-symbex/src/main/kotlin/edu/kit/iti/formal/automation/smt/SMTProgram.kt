package edu.kit.iti.formal.automation.smt

import com.google.common.collect.Streams
import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory.newAtomicSexp
import de.tudresden.inf.lat.jsexp.SexpFactory.newNonAtomicSexp
import de.tudresden.inf.lat.jsexp.SexpParserException
import java.util.*
import java.util.stream.Stream

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
        var inputDataTypes: MutableMap<String, Sexp> = HashMap(),
        var stateDataTypes: MutableMap<String, Sexp> = HashMap(),
        var initPredicates: MutableMap<String, Sexp> = TreeMap(),
        var nextPredicates: MutableMap<String, Sexp> = TreeMap(),
        var initFuncName: String = "init",
        var nextFuncName: String = "next") {

    val initFunction: Sexp
        @Throws(SexpParserException::class)
        get() {
            val func = newNonAtomicSexp()
            func.add(newAtomicSexp(DEFINE_FUNCTION))
            func.add(newAtomicSexp(this.initFuncName))
            func.add(toSexp(createSortSexp(STATE_NAME, this.stateDataTypes)))
            func.add(newAtomicSexp(SMT_BOOLEAN))
            func.add(initBody)
            return func
        }

    protected val initBody: Sexp
        get() {
            val body = newNonAtomicSexp()
            body.add(newAtomicSexp("and"))
            this.initPredicates.forEach { name, pred ->
                val eq = newNonAtomicSexp()
                eq.add(newAtomicSexp("="))
                eq.add(newAtomicSexp(STATE_NAME + newAtomicSexp(name)))
                eq.add(pred)
                body.add(eq)
            }
            return body
        }

    val nextFunction: Sexp
        @Throws(SexpParserException::class)
        get() {
            val func = newNonAtomicSexp()
            func.add(newAtomicSexp(DEFINE_FUNCTION))
            func.add(newAtomicSexp(this.nextFuncName))

            val s = createSortSexp(STATE_NAME, this.stateDataTypes)
            val i = createSortSexp(STATE_NAME, this.inputDataTypes)
            val t = createSortSexp(NEW_STATE_NAME, this.stateDataTypes)
            val args = toSexp(Streams.concat(s, i, t))
            func.add(args)

            func.add(newAtomicSexp(SMT_BOOLEAN))
            func.add(nextBody)
            return func
        }

    protected val nextBody: Sexp
        @Throws(SexpParserException::class)
        get() {
            val body = newNonAtomicSexp()
            body.add(newAtomicSexp("and"))
            this.nextPredicates.forEach { name, pred ->
                val eq = newNonAtomicSexp()
                eq.add(newAtomicSexp("="))
                eq.add(newAtomicSexp(NEW_STATE_NAME + name))
                eq.add(pred)
                body.add(eq)
            }
            return body
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


            try {
                val init = initFunction
                val next = nextFunction
                sb.append(init.toIndentedString()).append("\n\n")
                sb.append(next.toIndentedString()).append("\n\n")
            } catch (e: SexpParserException) {
                e.printStackTrace()
            }

            return sb.toString()
        }

    private fun toSexp(sortSexp: Stream<Sexp>): Sexp {
        val list = newNonAtomicSexp()
        sortSexp.forEach { list.add(it) }
        return list
    }

    /*
    public Sexp getStateDataType() throws SexpParserException {
        return createRecord(stateDataTypeName, stateDataTypes);
    }

    public Sexp getInputDataType() throws SexpParserException {
        return createRecord(getInputDataTypeName(), inputDataTypes);
    }
    */

    fun getDefineSteps(prefix: String, suffix: String): Stream<Sexp> {
        return Streams.concat(
                getDefineInputTypes(prefix, suffix),
                getDefineStateTypes(prefix, suffix)
        )
    }

    fun getDefineStateTypes(prefix: String, suffix: String): Stream<Sexp> {
        return this.stateDataTypes.entries.stream()
                .map { e -> createDefineConst(prefix + e.key + suffix, e.value) }
    }

    fun getDefineInputTypes(prefix: String, suffix: String): Stream<Sexp> {
        return this.inputDataTypes.entries.stream()
                .map { e -> createDefineConst(prefix + e.key + suffix, e.value) }
    }

    private fun createDefineConst(name: String, sort: Sexp): Sexp {
        val s = newNonAtomicSexp()
        s.add(newAtomicSexp("declare-const"))
        s.add(newAtomicSexp(name))
        s.add(sort)
        return s
    }

    /**
     * @return
     */
    fun getStepDefinition(withInput: Boolean, suffix: String): String {
        val sb = StringBuilder()
        val init = getDefineInputTypes("", suffix)
        val next = getDefineStateTypes("", suffix)

        val vars = if (withInput) Stream.concat(init, next) else next

        vars.forEach { sexp ->
            sb.append(sexp.toIndentedString())
                    .append("\n\n")
        }
        return sb.toString()
    }

    fun getAssertInit(suffix: String): Sexp {
        val asser = newNonAtomicSexp()
        asser.add(newAtomicSexp("assert"))
        val app = newNonAtomicSexp()
        asser.add(app)
        app.add(newAtomicSexp(this.initFuncName))
        this.stateDataTypes.keys.forEach { name -> app.add(newAtomicSexp(name + suffix)) }
        return asser
    }

    fun getAssertNext(previousSuffix: String, nextSuffix: String): Sexp {
        val asser = newNonAtomicSexp()
        asser.add(newAtomicSexp("assert"))
        val app = newNonAtomicSexp()
        app.add(newAtomicSexp(this.nextFuncName))
        asser.add(app)
        this.stateDataTypes.keys.forEach { name -> app.add(newAtomicSexp(name + previousSuffix)) }


        this.inputDataTypes.keys.forEach { name -> app.add(newAtomicSexp(name + previousSuffix)) }

        this.stateDataTypes.keys.forEach { name -> app.add(newAtomicSexp(name + nextSuffix)) }

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
         * adds the given arguments in the map into the given sexps.
         *
         * @param dt
         */
        private fun createSortSexp(prefix: String, dt: Map<String, Sexp>): Stream<Sexp> {
            return dt.entries.stream()
                    .map { entry ->
                        val s = newNonAtomicSexp()
                        s.add(newAtomicSexp(prefix + entry.key))
                        s.add(entry.value)
                        s
                    }
        }
    }


}
