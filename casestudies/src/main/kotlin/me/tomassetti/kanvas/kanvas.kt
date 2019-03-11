package me.tomassetti.kanvas

import me.tomassetti.kolasu.model.Node
import org.fife.ui.autocomplete.*
import java.awt.Color
import java.awt.Point
import java.util.*
import javax.swing.text.BadLocationException
import javax.swing.text.Document
import javax.swing.text.JTextComponent
import javax.swing.text.Segment

private val BACKGROUND = Color(39, 40, 34)
private val BACKGROUND_SUBTLE_HIGHLIGHT = Color(49, 50, 44)
private val BACKGROUND_DARKER = Color(23, 24, 20)
private val BACKGROUND_LIGHTER = Color(109, 109, 109)

abstract class AbstractCompletionProviderBase : CompletionProviderBase() {
    private val seg = Segment()

    override fun getCompletionsAt(comp: JTextComponent?, p: Point?): MutableList<Completion>? {
        throw UnsupportedOperationException("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun getParameterizedCompletions(tc: JTextComponent?): MutableList<ParameterizedCompletion>? {
        throw UnsupportedOperationException("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    protected fun isValidChar(ch: Char): Boolean {
        return Character.isLetterOrDigit(ch) || ch == '_'
    }

    override fun getAlreadyEnteredText(comp: JTextComponent): String {
        val doc = comp.document

        val dot = comp.caretPosition
        val root = doc.defaultRootElement
        val index = root.getElementIndex(dot)
        val elem = root.getElement(index)
        var start = elem.startOffset
        var len = dot - start
        try {
            doc.getText(start, len)
        } catch (ble: BadLocationException) {
            ble.printStackTrace()
            return EMPTY_STRING
        }

        val segEnd = seg.offset + len
        start = segEnd - 1
        while (start >= seg.offset && seg.array != null && isValidChar(seg.array[start])) {
            start--
        }
        start++

        len = segEnd - start
        return if (len == 0) EMPTY_STRING else String(seg.array, start, len)
    }
}

fun LanguageSupport<*>.autoCompletionSuggester() = AutoCompletionContextProvider(this.parserData!!.ruleNames,
        this.parserData!!.vocabulary, this.parserData!!.atn)

fun createCompletionProvider(languageSupport: LanguageSupport<*>, context: Context, nodeSupplier: () -> Node?): CompletionProvider {
    if (languageSupport.parserData == null) {
        return object : AbstractCompletionProviderBase() {

            override fun getCompletionsImpl(comp: JTextComponent?): MutableList<Completion> {
                return LinkedList()
            }

        }
    }
    val cp = object : AbstractCompletionProviderBase() {
        val thisACPB = this

        private val autoCompletionSuggester = languageSupport.autoCompletionSuggester()

        private fun pointInCode(comp: JTextComponent): me.tomassetti.kolasu.model.Point {
            val doc = comp.document
            val dot = comp.caretPosition
            val root = doc.defaultRootElement
            val currLineIndex = root.getElementIndex(dot)
            val currentLine = root.getElement(currLineIndex)
            val startLine = currentLine.startOffset
            return me.tomassetti.kolasu.model.Point(currLineIndex, dot - startLine)
        }

        private fun beforeCaret(comp: JTextComponent): String {
            val doc = comp.document

            val dot = comp.caretPosition
            val root = doc.defaultRootElement
            val currLineIndex = root.getElementIndex(dot)
            val sb = StringBuffer()
            for (i in 0 until currLineIndex) {
                val elem = root.getElement(i)
                var start = elem.startOffset
                val len = elem.endOffset - start
                sb.append(doc.getText(start, len))
            }

            sb.append(beforeCaretOnCurrentLine(doc, dot, currLineIndex))
            return sb.toString()
        }

        private fun beforeCaretOnCurrentLine(doc: Document, dot: Int, currLineIndex: Int): String {
            val root = doc.defaultRootElement
            val elem = root.getElement(currLineIndex)
            var start = elem.startOffset
            val len = dot - start
            return doc.getText(start, len)
        }

        override fun getCompletionsImpl(comp: JTextComponent): MutableList<Completion>? {
            val retVal = ArrayList<Completion>()
            val code = beforeCaret(comp)
            val autoCompletionContext = autoCompletionSuggester.autoCompletionContext(
                    EditorContextImpl(code, languageSupport.antlrLexerFactory, nodeSupplier))
            autoCompletionContext.proposals.forEach {
                if (it.first.type != -1) {
                    retVal.addAll(languageSupport.propositionProvider.fromTokenType(
                            AutocompletionSurroundingInformation(
                                    nodeSupplier(),
                                    autoCompletionContext.preecedingTokens,
                                    it.second,
                                    pointInCode(comp)), it.first.type, context).map {
                        BasicCompletion(thisACPB, it)
                    })
                }
            }

            return retVal

        }
    }
    return cp
}
