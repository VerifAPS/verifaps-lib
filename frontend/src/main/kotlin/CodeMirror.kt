import org.w3c.dom.Element
import org.w3c.dom.HTMLTextAreaElement

@JsNonModule
@JsModule("codemirror")
external class CodeMirror(e: Element, options: Any = definedExternally) {

    companion object {
        var version: String
        var defaults: dynamic
        fun fromTextArea(textArea: HTMLTextAreaElement, config: Any = definedExternally): CodeMirror
        fun defineMode(name: String, value: Any)
        fun defineExtension(name: String, value: Any)
        fun defineDocExtension(name: String, value: Any)
        fun defineOption(name: String, default: Any, updateFunc: Function<Any>)
        fun defineInitHook(func: Function<Any>)
        fun registerHelper(type: String, name: String, value: Function<Any>)
        fun registerGlobalHelper(type: String, name: String, predicate: Function<Any>, value: Any)
        class Pos(line: Int, ch: Int, sticky: String = definedExternally)

        fun changeEnd(change: Change): Pos
        fun countColumn(line: String, index: Number, tabSize: Number): Number
        fun defineSimpleMode(name: String, any: Any)
    }

    fun getValue(separator: String = definedExternally): String
    fun setValue(content: String)
    fun getRange(from: Pos, to: Pos, separator: String = definedExternally): String
    fun replaceRange(replacement: String, from: Pos, to: Pos, origin: String = definedExternally)
    fun getLine(n: Int): String
    fun lineCount(): Int
    fun firstLine(): Int
    fun lastLine(): Int
    fun getLineHandle(num: Int): dynamic // LineHandle
    fun getLineNumber(handle: Any): Int

    fun markClean()

    fun changeGeneration(closeEvent: Boolean = definedExternally)
    fun isClean(generation: Int = definedExternally): Boolean
    fun getSelection(lineSep: String = definedExternally): String
    fun getSelections(lineSep: String = definedExternally): Array<String>
    fun replaceSelection(replacement: String, select: String = definedExternally)
    fun replaceSelections(replacements: Array<String>, select: String = definedExternally)
    fun setSize(width: Number, height: Number)
    fun setSize(width: String, height: String)
    fun scrollTo(x: Number, y: Number)
    fun getScrollInfo(): ScrollInfo
    fun scrollIntoView(what: Pos, margin: Number = definedExternally)
    fun scrollIntoView(what: Coords, margin: Number = definedExternally)
    fun cursorCoords(where: Boolean, mode: String): Coords
    fun cursorCoords(where: Pos, mode: String): Coords
    fun charCoords(pos: Pos, mode: String = definedExternally): Coords
    fun coordsChar(obj: Any, mode: String = definedExternally): Pos
    fun lineAtHeight(height: Number, mode: String = definedExternally): Number
    fun heightAtLine(line: Int, mode: String = definedExternally, includeWidgets: Boolean = definedExternally): Number
    // fun heightAtLine(line: LineHandle, mode: String = definedExternally, includeWidgets: Boolean = definedExternally): Number
    fun defaultTextHeight(): Number

    fun defaultCharWidth(): Number
    fun getViewport(): dynamic
    fun refresh()
    fun getMode(): dynamic
    fun getModeAt(pos: Pos): dynamic
    fun getTokenAt(post: Pos, precise: Boolean = definedExternally): dynamic
    fun getLineTokens(line: Int, precise: Boolean): Array<dynamic>
    fun getTokenTypeAt(pos: Pos): String
    fun getHelpers(pos: Pos, type: String): Array<dynamic>
    fun getHelper(pos: Pos, type: String): dynamic
    fun getStateAfter(line: Int = definedExternally, precise: Boolean = definedExternally): dynamic
    fun <T> operation(func: Function<T>): T
    fun startOperation()
    fun endOperation()
    fun indentLine(line: Int, dir: String)
    fun indentLine(line: Int, dir: Int = definedExternally)
    fun toggleOverwrite(value: Boolean = definedExternally)
    fun isReadOnly(): Boolean
    fun lineSeparator(): String
    fun execCommand(name: String)
    fun posFromIndex(index: Int): Pos
    fun indexFromPos(pos: Pos): Int
    fun focus()
    fun getInputField(): Element
    fun getWrapperElement(): Element
    fun getScrollerElement(): Element
    fun getGutterElement(): Element
    fun getCursor(): Pos

    fun setOption(option: String, value: Any)

    fun getOption(option: String): dynamic
    fun addKeyMap(map: Any, bottom: Boolean)
    fun removeKeyMap(map: Any)

    fun on(type: String, func: Function<Any>)

    fun off(type: String, func: Function<Any>)
    fun markText(from: Pos, to: Pos, options: Any = definedExternally): dynamic // TextMarker
}

fun defineSimpleMode(name: String, f: SimpleModeBuilder.() -> Unit) {
    val b = SimpleModeBuilder()
    val any = b.eval(f)
    CodeMirror.defineSimpleMode(name, any)
}

class SimpleModeBuilder {
    val map: dynamic = object {}
    lateinit var curMode: Array<dynamic>


    fun mode(modeName: String, f: SimpleModeBuilder.() -> Unit) {
        curMode = arrayOf<dynamic>()
        map[modeName] = curMode
        f()
    }

    fun match(regex: Regex, token: String,
              dedent: Boolean? = null,
              indent: Boolean? = null,
              next: String? = null) {
        val m: dynamic = object {}
        m.regex = regex.pattern
        m.token = token
        if (dedent != null) m.dedent = dedent
        if (indent != null) m.indent = indent
        if (next != null) m.next = next
        curMode.push(m)
    }

    fun hit(regex: String, token: String) {
        match(regex.toRegex(), token)
    }

    fun eval(f: SimpleModeBuilder.() -> Unit): Any {
        f(this)
        console.log(map)
        return map
    }

    fun meta(function: Meta.() -> Unit) {
        val meta = Meta()
        function(meta)
        map["meta"] = meta
    }

    class Meta {
        var dontIndentStates: Array<String> = arrayOf()
        var lineComment: String = "//"
    }
}

typealias Pos = CodeMirror.Companion.Pos

data class ScrollInfo
(
        @JsName("left")
        val left: Number,
        @JsName("top")
        val top: Number,
        @JsName("width")
        val width: Number,
        @JsName("height")
        val height: Number,
        @JsName("clientWidth")
        val clientWidth: Number,
        @JsName("clientHeight")
        val clientHeight: Number
)

data class Coords
(
        @JsName("left")
        val left: Number,
        @JsName("right")
        val right: Number,
        @JsName("top")
        val top: Number,
        @JsName("bottom")
        val bottom: Number
)

data class Change
(
        @JsName("to")
        val to: Number,
        @JsName("from")
        val from: Number,
        @JsName("text")
        val text: String
)


fun <T> Array<T>.push(item: T) {
    asDynamic().push(item)
}

fun <T> Array<T>.pop(): T = asDynamic().pop() as T
