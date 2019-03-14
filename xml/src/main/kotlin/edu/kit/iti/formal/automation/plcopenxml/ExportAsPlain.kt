package edu.kit.iti.formal.automation.plcopenxml

import org.jdom2.JDOMException
import java.io.IOException
import java.io.OutputStreamWriter

/**
 * @author Alexander Weigl
 * @version 1 (20.02.18)
 */
object ExportAsPlain {
    @Throws(JDOMException::class, IOException::class)
    @JvmStatic
    fun main(args: Array<String>) {
        for (arg in args) {
            IECXMLFacade.extractPLCOpenXml(arg, OutputStreamWriter(System.out))
        }
    }
}
