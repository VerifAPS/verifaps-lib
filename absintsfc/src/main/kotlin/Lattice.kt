/**
 *
 * @author Alexander Weigl
 * @version 1 (20.11.18)
 */
abstract class Lattice<T>(
        val elements: Set<T>
) {

    open fun cup(seq: Collection<T>): T {
        return seq.reduce(this::cup)
    }

    abstract fun cup(a: T, b: T): T

    open fun cap(seq: Collection<T>): T {
        return seq.reduce(this::cap)
    }

    abstract fun cap(a: T, b: T): T
}

enum class TaintEq { EQUAL, NOT_EQUAL }

class TaintEqLattice : Lattice<TaintEq>(TaintEq.entries.toSet()) {
    override fun cup(a: TaintEq, b: TaintEq): TaintEq {
        return when {
            a == TaintEq.NOT_EQUAL || b == TaintEq.NOT_EQUAL ->
                TaintEq.NOT_EQUAL
            else ->
                TaintEq.EQUAL
        }
    }

    override fun cap(a: TaintEq, b: TaintEq): TaintEq {
        return when {
            a == TaintEq.EQUAL || b == TaintEq.EQUAL ->
                TaintEq.EQUAL
            else ->
                TaintEq.NOT_EQUAL
        }
    }
}