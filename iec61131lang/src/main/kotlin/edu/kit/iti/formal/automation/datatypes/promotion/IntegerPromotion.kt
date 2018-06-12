package edu.kit.iti.formal.automation.datatypes.promotion

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.AnyInt


class IntegerPromotion : TypePromotion {
    override fun getPromotion(a: AnyDt, b: AnyDt) =
            if (a is AnyInt && b is AnyInt) {
                when {
                    (a.isSigned && b.isSigned) ->
                        if (a.bitLength >= b.bitLength) a else b
                    (!a.isSigned && !b.isSigned) ->
                        if (a.bitLength >= b.bitLength) a else b
                    else -> findNext(a, b)
                }
            } else null

    private fun findNext(a: AnyInt, b: AnyInt): AnyInt {
        var (signed, unsigned) = if (a.isSigned) Pair(a, b) else Pair(b, a)
        while (signed.upperBound < unsigned.upperBound) {
            if (signed.next().isPresent)
                signed = signed.next().get()
            else break
        }
        return signed
    }

    companion object {
        val INSTANCE = IntegerPromotion()
    }
}
