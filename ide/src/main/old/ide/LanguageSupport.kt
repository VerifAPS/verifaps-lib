package edu.kit.iti.formal.automation.ide


import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.atn.ATN
import org.antlr.v4.runtime.atn.ATNDeserializer
import org.antlr.v4.runtime.atn.LexerATNSimulator
import org.antlr.v4.runtime.atn.PredictionContextCache
import org.antlr.v4.runtime.dfa.DFA
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import org.fife.ui.rsyntaxtextarea.parser.Parser
import java.awt.Color


interface AntlrLexerFactory {
    fun create(code: String): Lexer
}


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
        style.foreground = Color.BLACK
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

class None(input: CharStream?) : Lexer(input) {
    companion object {
        const val WHITESPACE = 1
        const val NON_WHITESPACE = 2
        val ruleNames = arrayOf("WHITESPACE", "NON_WHITESPACE")

        @Deprecated("Use {@link #VOCABULARY} instead.")
        val tokenNames: Array<String>
        const val _serializedATN = "\u0003\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\u0002\u0004\u000e\b\u0001\u0004\u0002\t\u0002" +
                "\u0004\u0003\t\u0003\u0003\u0002\u0003\u0002\u0003\u0003\u0006\u0003\u000b\n\u0003\r\u0003\u000e\u0003\u000c\u0002\u0002\u0004\u0003\u0003\u0005\u0004\u0003\u0002\u0003\u0005\u0002\u000b" +
                "\u000C\u000f\u000f\"\"\u000e\u0002\u0003\u0003\u0002\u0002\u0002\u0002\u0005\u0003\u0002\u0002\u0002\u0003\u0007\u0003\u0002\u0002\u0002\u0005\n\u0003\u0002\u0002\u0002\u0007\b\t" +
                "\u0002\u0002\u0002\b\u0004\u0003\u0002\u0002\u0002\t\u000b\n\u0002\u0002\u0002\n\t\u0003\u0002\u0002\u0002\u000b\u000c\u0003\u0002\u0002\u0002\u000c\n\u0003\u0002\u0002\u0002\u000c" +
                "\r\u0003\u0002\u0002\u0002\r\u0006\u0003\u0002\u0002\u0002\u0004\u0002\u000c\u0002"
        val _ATN = ATNDeserializer().deserialize(_serializedATN.toCharArray())
        protected val _decisionToDFA: Array<DFA?>
        protected val _sharedContextCache = PredictionContextCache()
        private val _LITERAL_NAMES = arrayOf<String>()
        private val _SYMBOLIC_NAMES = arrayOf(null, "WHITESPACE", "NON_WHITESPACE")
        val VOCABULARY: Vocabulary = VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES)
        var modeNames = arrayOf("DEFAULT_MODE")

        init {
            RuntimeMetaData.checkVersion("4.5.1", RuntimeMetaData.VERSION)
        }

        init {
            tokenNames = Array(_SYMBOLIC_NAMES.size) { i ->
                VOCABULARY.getLiteralName(i)
                        ?: VOCABULARY.getSymbolicName(i)
                        ?: "<INVALID>"
            }
        }

        init {
            _decisionToDFA = arrayOfNulls(_ATN.numberOfDecisions)
            for (i in 0 until _ATN.numberOfDecisions) {
                _decisionToDFA[i] = DFA(_ATN.getDecisionState(i), i)
            }
        }
    }

    @Deprecated("")
    override fun getTokenNames(): Array<String> {
        return Companion.tokenNames
    }

    override fun getVocabulary(): Vocabulary = VOCABULARY

    override fun getGrammarFileName(): String = "None.g4"

    override fun getRuleNames(): Array<String> = Companion.ruleNames

    override fun getSerializedATN(): String = _serializedATN

    override fun getModeNames(): Array<String> = Companion.modeNames

    override fun getATN(): ATN = _ATN

    init {
        _interp = LexerATNSimulator(this, _ATN, _decisionToDFA, _sharedContextCache)
    }
}