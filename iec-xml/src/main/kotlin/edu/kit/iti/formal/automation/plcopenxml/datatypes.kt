package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
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
        writer.append("TYPE").increaseIndent()
        datatypes.forEach { translate(it) }
        writer.decreaseIndent().nl().append("END_TYPE").nl().nl()
    }

    private fun translate(e: Element) {
        translator.forEach {
            if (it.isCapableOf(e))
                it.translate(e, writer)
        }
    }
}
