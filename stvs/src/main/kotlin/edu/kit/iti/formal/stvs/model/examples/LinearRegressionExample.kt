package edu.kit.iti.formal.stvs.model.examples

/**
 * @author Alexander Weigl
 * @version 1 (09.04.17)
 */
class LinearRegressionExample : Example() {
    init {
        name = "Linear Regression"
        description = "presented at INDIN 2017"
        htmlHelp = "linearregression.html"
        sessionFile = javaClass.getResource("linearregression.xml")
    }
}
