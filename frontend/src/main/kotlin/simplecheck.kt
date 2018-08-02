import org.w3c.dom.HTMLOptionElement
import kotlin.browser.document

/**
 *
 * @author Alexander Weigl
 * @version 1 (02.08.18)
 */
class SimpleCheck(
        val id: String,
        val name: String,
        val endpoint: Service
) {
    val desc: String = ""
}

object SimpleCheckTab {
    val typesAndNames = SimpleCheck(
            id = "SyntaxAndNames",
            name = "Check Syntax and Names",
            endpoint = Service("$KIT_SERVICE_HOST/syntax")
    )

    val SIMPLE_CHECKS = listOf(typesAndNames)

    val resultDiv = jQuery("div#check-results");
    val cboChecks = jQuery("select#checks");
    val btnRun = jQuery("button#run-check");

    init {
        SIMPLE_CHECKS.forEach {
            val opt =
                    document.createElement("option") as HTMLOptionElement
            opt.text = it.name
            opt.value = it.id
            cboChecks.append(opt)
        }
        btnRun.bind("click", this::runCurrentCheck)
    }

    fun runCurrentCheck(evt: JQueryEventObject) {
        val v = cboChecks.`val`()
        val item = SIMPLE_CHECKS.find { it.id == v }
        console.log(item)
        if (item != null) {
            val code = App.stCodeEditor.getValue()
            item.endpoint.post(code)
                    .then { resultDiv.html(it.body.toString()) }
                    .catch { resultDiv.html("Error: $it") }
        }
    }
}