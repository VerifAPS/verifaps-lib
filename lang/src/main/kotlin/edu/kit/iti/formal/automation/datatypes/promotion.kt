package edu.kit.iti.formal.automation.datatypes

fun getPromotion(a: AnyDt, b: AnyDt): AnyDt? = a.accept(PromotionVisitor(b))
infix fun AnyDt.promoteWith(other: AnyDt): AnyDt? = getPromotion(this, other)


class PromotionVisitor(val other: AnyDt) : DataTypeVisitor<AnyDt> {
    override fun defaultVisit(obj: Any) = null
    override fun visit(real: AnyReal): AnyDt? {
        return when (other) {
            is AnyReal ->
                //silent assumption: only REAL and LREAL
                if (real == other) real else AnyReal.LREAL
            is AnyInt -> real
            else -> null
        }
    }

    override fun visit(anyInt: AnyInt): AnyDt? {
        return when (other) {
            is AnyReal -> getPromotion(other, anyInt)
            is AnyInt -> {
                when {
                    (anyInt.isSigned && other.isSigned) ->
                        if (anyInt.bitLength >= other.bitLength) anyInt else other
                    (!anyInt.isSigned && !other.isSigned) ->
                        if (anyInt.bitLength >= other.bitLength) anyInt else other
                    else -> findNext(anyInt, other)
                }
            }
            else -> null
        }
    }

    override fun visit(anyBit: AnyBit): AnyDt? {
        return when (other) {
            is AnyBit ->
                if (anyBit.bitLength >= other.bitLength) anyBit else other
            else -> null
        }
    }


    override fun visit(enumerateType: EnumerateType): AnyDt? {
        return when (other) {
            enumerateType -> enumerateType
            is AnyInt -> getPromotion(AnyInt(enumerateType.bitlength), other)
            else -> null
        }
    }

    override fun visit(string: IECString.STRING): AnyDt? {
        return if (string == other) string
        else null
    }

    override fun visit(wString: IECString.WSTRING): AnyDt? {
        return if (wString == other) wString
        else null
    }

    private fun findNext(a: AnyInt, b: AnyInt): AnyInt {
        var (signed, unsigned) = if (a.isSigned) Pair(a, b) else Pair(b, a)
        while (signed.upperBound < unsigned.upperBound) {
            signed = signed.next() ?: break
        }
        return signed
    }
}
