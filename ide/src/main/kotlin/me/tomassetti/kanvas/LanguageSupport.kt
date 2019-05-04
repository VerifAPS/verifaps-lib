package me.tomassetti.kanvas

import edu.kit.iti.formal.automation.ide.CodeEditor
import edu.kit.iti.formal.automation.ide.Lookup
import me.tomassetti.antlr.None
import org.antlr.v4.runtime.ANTLRInputStream
import org.antlr.v4.runtime.Lexer
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import org.fife.ui.rsyntaxtextarea.parser.Parser
import java.awt.Color

//data class ParserData(val ruleNames: Array<String>, val vocabulary: Vocabulary, val atn: ATN)

interface LanguageSupport {
    fun createParser(textArea: CodeEditor, lookup: Lookup): Parser? = null

    val isCodeFoldingEnabled: Boolean
        get() = false

    val mimeType: String
    val extension: Collection<String>
    val syntaxScheme: SyntaxScheme
    val antlrLexerFactory: AntlrLexerFactory

    fun configure(textArea: RSyntaxTextArea) {}
}

abstract class BaseLanguageSupport : LanguageSupport {
    override val syntaxScheme: SyntaxScheme
        get() = DefaultSyntaxScheme()
}

class DefaultSyntaxScheme : SyntaxScheme(false) {
    override fun getStyle(index: Int): Style {
        val style = Style()
        style.foreground = Color.WHITE
        return style
    }
}

object NoneLanguageSupport : BaseLanguageSupport() {
    override val mimeType: String = "text/plain"
    override val extension: Set<String> = setOf("txt")

    override val antlrLexerFactory: AntlrLexerFactory
        get() = object : AntlrLexerFactory {
            override fun create(code: String): Lexer = None(ANTLRInputStream(code))
        }

    override fun toString(): String {
        return "default language support"
    }
}
