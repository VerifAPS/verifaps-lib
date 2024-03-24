package edu.kit.iti.formal.stvs.model.examples

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
class MinMaxExample : Example() {
    init {
        name = "MinMaxWarning"
        description = "Example of iFM'17 Paper"
        htmlHelp = "minmax.html"
        sessionFile = javaClass.getResource("minmax.xml")
    }
}
