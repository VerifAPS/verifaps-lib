package edu.kit.iti.formal.stvs.model.code

import edu.kit.iti.formal.stvs.model.common.NullableProperty
import javafx.beans.property.SimpleListProperty
import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import org.antlr.v4.runtime.Token
import tornadofx.getValue
import tornadofx.setValue

/**
 * Represents the effective model of sourcecode. The formal model ([ParsedCode]) is
 * extracted from this.
 * @author Lukas
 * @author Philipp
 */
class Code {
    @Transient
    val filenameProperty: StringProperty = SimpleStringProperty(null)
    var filename: String? by filenameProperty

    @Transient
    val sourceCodeProperty: StringProperty = SimpleStringProperty("")
    var sourcecode: String by sourceCodeProperty

    /**
     * last valid parsed Code.
     */
    @Transient
    val parsedCodeProperty = NullableProperty<ParsedCode?>()
    var parsedCode: ParsedCode? by parsedCodeProperty

    @Transient
    val tokensProperty: SimpleListProperty<Token> = SimpleListProperty(FXCollections.observableArrayList())
    var tokens: ObservableList<Token> by tokensProperty

    @Transient
    val syntaxErrorsProperty: SimpleListProperty<SyntaxError> = SimpleListProperty(FXCollections.observableArrayList())
    var syntaxErrors: ObservableList<SyntaxError> by syntaxErrorsProperty

    /**
     * Creates a codefile which is invalidated.
     *
     * @param filename name of the codefile
     * @param sourcecode content of the codefile
     */
    constructor(filename: String? = null, sourcecode: String = "") {
        this.filename = filename
        this.sourcecode = sourcecode
        invalidate()
    }

    /**
     * Creates a default codefile.
     */
    init {
        invalidate()
    }

    private fun invalidate() {
        if (sourcecode.isEmpty()) {
            tokens.setAll()
            syntaxErrors.setAll()
            parsedCode = null
            return
        }

        ParsedCode.parseCode(
            sourcecode,
            { col -> tokens.setAll(col) },
            { col -> syntaxErrors.setAll(col) },
            { newValue -> parsedCode = newValue })
    }

    fun updateSourcecode(sourcecode: String) {
        sourceCodeProperty.set(sourcecode)
        invalidate()
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is Code) return false

        if (sourcecode != other.sourcecode) return false

        return true
    }

    override fun hashCode(): Int {
        return sourcecode.hashCode()
    }
}
