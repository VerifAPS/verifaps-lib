import com.github.jferard.fastods.OdsDocument
import com.github.jferard.fastods.OdsFactory
import com.github.jferard.fastods.style.TableCellStyle
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.report.Counterexample
import natorder.NaturalOrderComparator
import java.io.File
import java.util.*
import java.util.logging.Logger
import kotlin.collections.ArrayList
import kotlin.collections.HashMap

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
class CounterExampleModel constructor(val variables: MutableMap<String, Boolean>,
                                      val trace: MutableList<MutableMap<String, String>>) {

    constructor(ce: Counterexample) : this(TreeMap(), ArrayList()) {
        ce.step[0].input.forEach { variables.put(it.name, true) }
        ce.step[0].state.forEach { variables.put(it.name, false) }
        ce.step.forEach {
            val map = HashMap<String, String>()
            it.state.forEach { map.put(it.name, it.value) }
            it.input.forEach { map.put(it.name, it.value) }
            trace.add(map)
        }
    }

    fun inputVariables() =
            variables.filter { it.value }
                    .map { it.key }
                    .sortedDescending()

    fun outpuVariables() =
            variables.filter { !it.value }
                    .map { it.key }
                    .sortedDescending()
}

class ODSTableWriter constructor(
        private val counterExample: CounterExampleModel,
        private val gtt: GeneralizedTestTable,
        private val varialeSorter: Comparator<String>,
        private val styles: Map<String, TableCellStyle>
) : Runnable {

    class Builder private constructor() {
        lateinit var counterExample: CounterExampleModel
        lateinit var testTable: GeneralizedTestTable
        var varialeSorter: Comparator<String> = String.CASE_INSENSITIVE_ORDER
        var styles: MutableMap<String, TableCellStyle> = HashMap()

        fun style(key: String, style: TableCellStyle) {
            styles[key] = style
            this
        }

        fun build() = ODSTableWriter(counterExample, testTable, varialeSorter, styles)
    }

    override fun run() {
        val odsFactory = OdsFactory.create(Logger.getLogger("example"), Locale.US)
        val writer = odsFactory.createWriter()
        val document = writer.document()

        writeCounterExample(document)

        val table = document.addTable("")

        val style = TableCellStyle.builder("green cell style").backgroundColor("#00ff00").build()
        for (y in 0..49) {
            val row = table.nextRow()
            val cell = row.walker
            for (x in 0..4) {
                cell.setFloatValue(x * y)
                cell.setStyle(style)
                cell.next()
            }
        }
        writer.saveAs(File("readme_example.ods"))
    }


    fun writeCounterExample(document: OdsDocument) {
        val natorder = NaturalOrderComparator()
        //variable order
        val inputVariables = counterExample.inputVariables()
        val stateVariables = counterExample.outpuVariables()
        val table = document.addTable("raw counter example",
                counterExample.trace.size + 10,
                inputVariables.size + stateVariables.size + 10)
        val variables = stateVariables + inputVariables
        //val headerStyle = styles["cehdr"]
        //write header
        val hdr = table.nextRow()
        val cell = hdr.walker
        cell.next()//skip one
        for (v in variables) {
            cell.setStringValue(v)
            // cell.setStyle(headerStyle)
            cell.next()
        }

        var i = 0
        for (step in counterExample.trace) {
            val row = table.nextRow()
            val cell = row.walker
            cell.setFloatValue(i)
            cell.next()
            for (v in variables) {
                cell.setStringValue(step[v])
                cell.next()
            }
        }
    }
}