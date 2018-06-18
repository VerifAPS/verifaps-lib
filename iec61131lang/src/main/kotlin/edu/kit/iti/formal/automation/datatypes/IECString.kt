package edu.kit.iti.formal.automation.datatypes

abstract class IECString : AnyDt() {
    object WSTRING : IECString() {
        override fun repr(obj: Any) = "WSTRING#\"$obj\""
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    /** Constant `STRING_16BIT`  */
    object STRING : IECString() {
        override fun repr(obj: Any) = "WSTRING#'$obj'"
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }
}
