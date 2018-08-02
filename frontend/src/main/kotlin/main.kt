import org.w3c.dom.HTMLOptionElement
import kotlin.browser.document
import kotlin.browser.window

fun main(args: Array<String>) {
    App.toString()
}

fun defineStMode() {
    val REKEYWORDS = """(IF|ARRAY|CASE|AT|BY|CONSTANT|FOR|ELSIF|END_CASE|EXIT|F_EDGE|INTERVAL|NIL|NON_RETAIN|OF|ON|PRIORITY|READ_ONLY|READ_WRITE|RETAIN|RETURN|=>|R_EDGE|SINGLE|STRUCT|TASK|TO|WHILE|TYPE|UNTIL)\b""".toRegex(RegexOption.IGNORE_CASE)
    val BUILT_DATATPYES = """(?: ANY|ANY_BIT|ANY_DATE|DT|DATE|ANY_DERIVED|ANY_ELEMENTARY|ANY_INT|ANY_NUM|ANY_REAL|ANY_STRING|BOOL|BYTE|DATE_AND_TIME|DINT|DWORD|INT|LINT|LREAL|LWORD|REAL|SINT|STRING|TIME|TIME_OF_DAY|TOD|UDINT|UINT|ULINT|USINT|WORD|WSTRING)""".toRegex(RegexOption.IGNORE_CASE)
    val RE_ST_OPEN_BLOCK = """(VAR_OUTPUT|CONFIGURATION|FUNCTION|FUNCTION_BLOCK|REPEAT|STRUCT|RESOURCE|VAR|VAR_ACCESS|VAR_CONFIG|VAR_EXTERNAL|VAR_GLOBAL|VAR_INPUT|THEN|VAR_IN_OUT|VAR_TEMP|WITH|PROGRAM|DO)\b""".toRegex(RegexOption.IGNORE_CASE)
    val RE_ST_CLOSE_BLOCK = """(UNTIL|END_CASE|END_CONFIGURATION|END_FOR|END_FUNCTION|END_FUNCTION_BLOCK|END_IF|END_PROGRAM|END_REPEAT|END_RESOURCE|END_STRUCT|END_TYPE|END_VAR|END_WHILE)\b""".toRegex(RegexOption.IGNORE_CASE);

    defineSimpleMode("st") {
        mode("start") {
            // The regex matches the token, the token property contains the type
            hit(regex = """TEST!!!""", token = "string")

            hit(regex = """(WSTRING#)?"(?:[^\\]|\\.)*?(?:"|$)""", token = "string")
            hit(regex = """(STRING#)?'(?:[^\\]|\\.)*?(?:'|$)""", token = "string")

            hit(regex = """(TIME_OF_DAY|TOD)#\d{ 1, 2 }:\d{ 1, 2 }:\d{ 1, 2 }(\.[0 - 9]{ ,3 })""", token = "atom")
            hit(regex = """(DATE)#\d+-\d+-\d+""", token = "atom")
            hit(regex = """(TIME|T)#((\d|[_])+(ms|s|m|h))*""", token = "atom")
            hit(regex = """(DATE_AND_TIME|DT)#\d+-\d+-\d+-\d{1,2}:\d{1,2}:\d{1,2}(\.[0-9]{,3})""", token = "atom")
            match(regex = REKEYWORDS, token = "keyword")
            match(regex = RE_ST_OPEN_BLOCK, token = "keyword", indent = true)
            match(regex = RE_ST_CLOSE_BLOCK, token = "keyword", dedent = true)

            match(regex = """true|false|null""".toRegex(RegexOption.IGNORE_CASE), token = "atom")
            match(regex = """(U?[SLD]? INT #)?((1[06]|8|2)#)?[_\d]+""".toRegex(RegexOption.IGNORE_CASE),
                    token = "number")
            match(regex = """(L? REAL #)?[\d_]+\.[\d_]+(e\d+)?""".toRegex(RegexOption.IGNORE_CASE), token = "number")
            hit(regex = """\ { .*?\ } """, token = "hint")
            hit(regex = """\/\/.*""", token = "comment")

            // A next property will cause the mode to move to a different state
            match(regex = """/\*""".toRegex(), token = "comment", next = "comment")
            match(regex = """\(\*""".toRegex(), token = "comment", next = "commentRound")

            hit(regex = """[\w][\w\d]*""", token = "variable")
        }
        mode("commentRound") {
            match(regex = """.*?\*\)""".toRegex(), token = "comment", next = "start")
            hit(regex = """.*""", token = "comment")
        }
        // The multi-line comment state.
        mode("comment") {
            match(regex = """.*?\*/""".toRegex(), token = "comment", next = "start")
            hit(regex = """.*""", token = "comment")
        }
// The meta property contains global information about the mode. It
// can contain properties like lineComment, which are supported by
// all modes, and also directives like dontIndentStates, which are
// specific to simple modes.
        meta {
            dontIndentStates = arrayOf("comment")
            lineComment = "//"
        }
    }
}

object App {
    val code = document.getElementById("editor")
    lateinit var stCodeEditor: CodeMirror

    init {
        defineStMode()
        if (code == null)
            window.alert("No element#code defined!")
        else {
            stCodeEditor = CodeMirror(code, object {
                val mode = "st"
                val lineNumbers = true
            })
            stCodeEditor.setSize("100%", "100%")
            stCodeEditor.setValue("\nfun main(args: Array<String>) { \n\tprintln(\"Hello, World\")\n}\n")
        }

        //Activate tabs
        jQuery("#tabs").tabs()
        jQuery("#tt-accordion").accordion(object {
            val heightStyle = "content"
            val collapsible = true
        })

        jQuery("#body").split(object {
            val orientation = "vertical"
            val limit = 10
            val position = "50%" // if there is no percentage it interpret it as pixels
            val onDrag = { event: JQueryEventObject ->
                //console.log(splitter.position());
            }
        })

        //layouting editor
        jQuery(window).resize(this::layoutEditor)
        layoutEditor(null)
        //
        showExamples()
    }

    /**
     * This function calculates the layout.
     */
    fun layoutEditor(evt: JQueryEventObject?) {
        val headerHeight = jQuery("#header").height().toFloat()
        val viewportHeight = jQuery(window).height().toFloat()
        val editorDiv = jQuery("#editor").width().toFloat()
        val h = viewportHeight - headerHeight - 10
        //stCodeEditor.setSize(editorDiv, h)
        jQuery("#body,#editor").height(h)
    }

    fun showExamples() {
        val cboExample = jQuery("#examples");
        cboExample.bind("change") { evt ->
            val selected = cboExample.`val`()
            val ex = CodeExamples.get(selected)
            if (ex != null)
                stCodeEditor.setValue(ex.content)
        }

        val examples = CodeExamples.examples
        console.log(examples)
        examples.forEach { value ->
            val opt = document.createElement("option") as HTMLOptionElement
            opt.text = value.name
            cboExample.append(opt)
        }
    }

}