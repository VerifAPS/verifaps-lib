package edu.kit.iti.formal.stvs.model.examples

/**
 * @author Alexander Weigl
 * @version 1 (09.04.17)
 */
class LinearRegressionCombinedExample : Example() {
    init {
        name = "Linear Regression in Combination"
        description = "presented at INDIN 2017"
        htmlHelp = "lrcombined.html"
        sessionFile = javaClass.getResource("lrcombined.xml")
    }
}
