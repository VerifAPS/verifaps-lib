package edu.kit.iti.formal.stvs.logic.specification.smtlib

import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory
import java.util.*
import java.util.function.Consumer
import java.util.stream.Collectors

/**
 * Represents a S-Expression of form ( expr_1 expr_2 expr_3 ... expr_n)
 *
 * @author Carsten Csiky
 */
class SList : SExpression {
    private var sexp: MutableList<SExpression> = arrayListOf()

    /**
     * Creates an instance from a list of [SExpression].
     * if the passed list must be modifiable for the methods add() and allAll() to work properly
     * @param sexp list of [SExpression]
     */
    /**
     * Creates an empty SList.
     */
    @JvmOverloads
    constructor(sexp: List<SExpression> = ArrayList()) {
        this.sexp.addAll(sexp)
    }

    /**
     * Helper constructor. Creates a [SAtom] for any passed string an calls
     * [SList.SList]
     *
     * @param vals atomic expressions as string
     */
    constructor(vararg vals: String) : this(vals.map { SAtom(it) })

    constructor(command: String) : this() {
        addAll(command)
    }

    /**
     * Creates an SList with the first argument interpreted as atomic expression followed by
     * `sexp`.
     *
     * @param command atomic command expression
     * @param sexp following expressions
     */
    constructor(command: String, vararg sexp: SExpression) : this() {
        addAll(SAtom(command))
        addAll(listOf(*sexp))
    }

    /**
     * Creates an instance by using an [Sexp] as a base. Every item in `exp` will become
     * an item in this list.
     *
     * @param exp base expression
     */
    constructor(exp: Sexp) {
        sexp = LinkedList()
        exp.forEach(Consumer { sitem: Sexp -> this.addSexp(sitem) })
    }

    private fun addSexp(sitem: Sexp) {
        sexp!!.add(SExpression.Companion.fromSexp(sitem))
    }

    override val isAtom: Boolean
        get() = false

    override fun toSexpr(): Sexp? {
        val exp = SexpFactory.newNonAtomicSexp()
        sexp!!.forEach(Consumer { sitem: SExpression? -> addItemToSexp(exp, sitem) })
        return exp
    }

    override fun toText(): String? {
        return (" ( " + list!!.stream().map { obj: SExpression? -> obj!!.toText() }.collect(Collectors.joining(" "))
                + " ) ")
    }

    fun addAll(vararg sexp: SExpression): SList {
        return addAll(listOf(*sexp))
    }

    fun addAll(vararg values: String): SList {
        return addAll(Arrays.stream(values).map { string: String? -> SAtom(string) }
            .collect(Collectors.toList()))
    }

    fun addAll(exprs: Collection<SExpression>): SList {
        sexp!!.addAll(exprs!!)
        return this
    }

    fun addListElements(values: List<String?>): SList {
        return addAll(values.stream().map { string: String? -> SAtom(string) }
            .collect(Collectors.toList()))
    }

    val list: List<SExpression>
        get() = this.sexp

    /**
     * Returns the List as a string
     *
     * @return string representation: "(item_1 item_2 ... item_n)"
     */
    override fun toString(): String {
        return "( " + list!!.stream().map { obj: SExpression? -> obj.toString() }
            .collect(Collectors.joining(" ")) + " )"
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val list = o as SList

        return if (sexp != null) sexp == list.sexp else list.sexp == null
    }

    override fun hashCode(): Int {
        return if (sexp != null) sexp.hashCode() else 0
    }

    companion object {
        private fun addItemToSexp(exp: Sexp, sitem: SExpression?) {
            exp.add(sitem!!.toSexpr())
        }

        fun sexpr(vararg vals: String): SList {
            return SList(*vals)
        }


        fun sexpr(command: String, vararg vals: SExpression): SList {
            return SList(command, *vals)
        }


        fun sexpr(sexp: Sexp): SList {
            return SList(sexp)
        }
    }
}
