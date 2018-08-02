import App.stCodeEditor
import org.w3c.dom.HTMLOptionElement
import kotlin.browser.document

/**
 *
 * @author Alexander Weigl
 * @version 1 (02.08.18)
 */
//http://codemirror.net/demo/simplemode.html

val REKEYWORDS = "(?:table|row|group|options|g?var|state|input|output|as|omega|>>|function)\b".toRegex()
val RE_ST_OPEN_BLOCK = "(?:[{])".toRegex()
val RE_ST_CLOSE_BLOCK = "(?:[}])".toRegex()

/*import 'codemirror/addon/mode/simple';
import 'codemirror/lib/codemirror.css';
import 'codemirror/theme/monokai.css';
import CodeMirror from 'codemirror';
*/

object TestTableTab {
    val serviceExtractInterface = Service("$KIT_SERVICE_HOST/geteta/generate")
    val serviceExamples = Service("$KIT_SERVICE_HOST/geteta/examples")
    val serviceRender = Service("$KIT_SERVICE_HOST/geteta/render")

    lateinit var ttEditor: CodeMirror

    init {
        defineTestTableMode()


    }

    fun defineTestTableMode() {
        defineSimpleMode("testtable") {
            mode("start") {
                hit(regex = """"(?:[^\\]|\.)*?(?:\"|$)""", token = "string")
                hit(regex = """(TIME_OF_DAY|TOD)#\d{1,2}:\d{1,2}:\d{1,2}(\.[0-9]{,3})?""", token = "atom")
                hit(regex = """(DATE)#\d+-\d+-\d+""", token = "atom")
                hit(regex = """(TIME|T)#((\d|[_])+(ms|s|m|h))*""", token = "atom")
                hit(regex = """(DATE_AND_TIME|DT)#\d+-\d+-\d+-\d{ 1, 2 }:\d{ 1, 2 }:\d{ 1, 2 }(\.[0 - 9]{ ,3 })""", token = "atom")
                match(regex = REKEYWORDS, token = "keyword")
                match(regex = RE_ST_OPEN_BLOCK, token = "keyword", indent = true)
                match(regex = RE_ST_CLOSE_BLOCK, token = "keyword", dedent = true)
                hit(regex = "true|false|null", token = "atom")
                //{regex = "(U?[SLD]?INT#)?((1[06]|8|2)#)?[_\d]+/i, token =  "number")
                hit(regex = """((1[06]|8|2)#)?[_\d]+""", token = "number")
                //{regex = "(L?REAL#)?[\d_]+\.[\d_]+(e\d+)?/i, token =  "number")
                hit(regex = """[\d_]+\.[\d_]+(e\d+)?""", token = "number")
                hit(regex = """\/\/.*$""", token = "comment")
                match(regex = """/\*""".toRegex(), token = "comment", next = "comment")
                hit(regex = """[\w][\w\d]*""", token = "variable")
            }
            // The multi-line comment state.
            mode("comment") {
                match(regex = """.*?\*/""".toRegex(), token = "comment", next = "start")
                hit(regex = ".*", token = "comment")
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

    fun doTTfromInterface() {
        val code = App.stCodeEditor.getValue()
        console.log(code)
        serviceExtractInterface.post(code)
                .then {
                    console.log(it)
                    ttEditor.setValue(it.body)
                }.catch {
                    ttEditor.setValue("ERROR! : $it")
                }
    }


    var ttExamples: Array<TTExample> = arrayOf()

    fun loadTTExamples() {
        val cboExample = jQuery("#tt-example")
        val getCurrentSelectedExample = { ->
            ttExamples.find {
                it.name === cboExample.`val`()
            }
        }

        jQuery("#tt-btn-load-code").bind("click") {
            val ex = getCurrentSelectedExample()
            if (ex != null)
                stCodeEditor.setValue(ex.code)
        }

        jQuery("#tt-btn-load-testtable").bind("click") {
            val ex = getCurrentSelectedExample()
            if (ex != null)
                ttEditor.setValue(ex.testtable)
        }

        serviceExamples.get()
                .then {
                    ttExamples = JSON.parse(it.body as String)
                    ttExamples.forEach { value ->
                        val opt = document.createElement("option") as HTMLOptionElement
                        opt.text = value.name
                        cboExample.append(opt)
                    }
                }.catch { console.log(it) }
    }

    fun doTTRender() {
        val tt = ttEditor.getValue()
        serviceRender.post(tt).then {
            console.log(it.body)
            jQuery("#tt-render-result").html(it.body as String)
        }.catch { console.log(it) }
    }

    init {
        defineTestTableMode()
        val ttEditorElement = document.getElementById("tt-editor")
        if (ttEditorElement != null) {
            ttEditor = CodeMirror(ttEditorElement, object {
                val lineNumbers = true
                val gutter = arrayOf("gutter-errors", "gutter-warnings")
                val mode = "testtable"
            })
            ttEditor.setValue("table name {\n}")
        }
        jQuery("#btn-tt-generate").bind("click") { doTTfromInterface() }
        jQuery("#btn-tt-render").bind("click") { doTTRender() }
        loadTTExamples()
    }
}

data class TTExample(val name: String, val code: String, val testtable: String)
