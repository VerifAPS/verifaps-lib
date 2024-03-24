package edu.kit.iti.formal.stvs.model.code

import edu.kit.iti.formal.stvs.model.common.NullableProperty
import javafx.beans.property.SimpleListProperty
import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty
import javafx.collections.FXCollections
import org.antlr.v4.runtime.Token
import tornadofx.getValue
import tornadofx.setValue

/**
 * Represents the effective model of sourcecode. The formal model ([ParsedCode]) is
 * extracted from this.
 * @author Lukas
 * @author Philipp
 */
class Code @JvmOverloads constructor(filename: String? =  "", sourcecode: String? = "") {
    val filenameProperty: StringProperty = SimpleStringProperty(filename)
    var filename by filenameProperty

    val sourceCodeProperty: StringProperty = SimpleStringProperty(sourcecode)
    var sourcecode: String by sourceCodeProperty

    /**
     * last valid parsed Code.
     */
    val parsedCodeProperty = NullableProperty<ParsedCode?>()
    var parsedCode by parsedCodeProperty

    val tokensProperty: SimpleListProperty<Token> = SimpleListProperty(FXCollections.observableArrayList())
    var tokens by tokensProperty

    val syntaxErrorsProperty: SimpleListProperty<SyntaxError> = SimpleListProperty(FXCollections.observableArrayList())
    var syntaxErrors by syntaxErrorsProperty

    /**
     * Creates a codefile which is invalidated.
     *
     * @param filename name of the codefile
     * @param sourcecode content of the codefile
     */
    /**
     * Creates a default codefile.
     */
    init {
        invalidate()
    }

    private fun invalidate() {
        ParsedCode.parseCode(
            sourceCodeProperty.get(),
            { col: List<Token?>? -> tokens.setAll(col) },
            { col: List<SyntaxError?>? -> syntaxErrors.setAll(col) },
            { newValue: ParsedCode? -> parsedCode = newValue })
    }

    fun updateSourcecode(sourcecode: String) {
        sourceCodeProperty.set(sourcecode)
        invalidate()
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is Code) return false

        if (filename != other.filename) return false
        if (sourcecode != other.sourcecode) return false
        if (parsedCode != other.parsedCode) return false
        if (syntaxErrors != other.syntaxErrors) return false

        return true
    }

    override fun hashCode(): Int {
        var result = filename?.hashCode() ?: 0
        result = 31 * result + sourcecode.hashCode()
        result = 31 * result + (parsedCode?.hashCode() ?: 0)
        result = 31 * result + (syntaxErrors?.hashCode() ?: 0)
        return result
    }
}
