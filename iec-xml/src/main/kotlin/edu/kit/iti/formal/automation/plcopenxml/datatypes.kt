package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.automation.st.util.CodeWriter
import org.jdom2.Element

/**
 *
 * @author Alexander Weigl
 * @version 1 (22.07.18)
 */
open class DataTypeExtractor(val datatypes: List<Element>,
                             val writer: CodeWriter,
                             val translator: List<XMLTranslator> = listOf(EnumTranslator, StructTranslator)) {
    fun run() {
        datatypes.forEach { translate(it) }
    }

    private fun translate(e: Element) {
        translator.forEach {
            if (it.isCapableOf(e))
                it.translate(e, writer)
        }
    }
}
