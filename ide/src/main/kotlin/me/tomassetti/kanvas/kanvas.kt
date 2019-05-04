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

