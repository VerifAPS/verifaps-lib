import kotlinx.html.classes
import kotlinx.html.div
import kotlinx.html.dom.create
import kotlinx.html.p
import kotlin.browser.document
import kotlin.dom.clear

/**
 *
 * @author Alexander Weigl
 * @version 1 (02.08.18)
 */


sealed class CodeExample {
    abstract val id: String
    abstract val name: String
    abstract val description: String
    abstract val exampleType: String
    abstract val stCode: String
}

data class SimpleCodeExample(
        override val id: String,
        override var name: String,
        override var description: String,
        override var stCode: String
) : CodeExample() {
    override val exampleType: String = "simple"
}

data class GetetaExample(
        override val id: String,
        override var name: String,
        override var description: String,
        override var stCode: String,
        var testtable: String) : CodeExample() {
    override val exampleType: String = "testtable"
}

data class RegressionExample(override val id: String,
                             override var name: String,
                             override var description: String,
                             override var stCode: String)
    : CodeExample() {
    override val exampleType: String = "simple"
}

object CodeExamples {
    fun get(selected: Any) = examples.find { it.name == selected }

    val exampleService = Service("$KIT_SERVICE_HOST/examples")
    var examples: Array<CodeExample> = arrayOf()

    init {
        exampleService.get()
                .then {
                    if (it.status == 200.toShort()) {
                        examples = JSON.parse(it.body as String)
                        render()
                    } else {
                        console.log("Could not load examples: ${it.status}: ${it.statusText}")
                    }
                }
                .catch { console.log(it) }
    }

    private fun render() {
        document.getElementById("examples")?.clear()
        examples.forEach {
            document.getElementById("examples")?.append(
                    render(it))

        }
    }

    private fun render(it: CodeExample) {
        document.create.div {
            div {
                classes += "header"
                +it.name
            }
            p { +it.description }
        }
    }
}