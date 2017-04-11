package edu.kit.iti.formal.stvs.model.examples;

/**
 * @author Alexander Weigl
 * @version 1 (09.04.17)
 */
public class LinearRegressionExample extends Example {
    public LinearRegressionExample() {
        name = "Linear Regression";
        description = "presented at INDIN 2017";
        htmlHelp = "linearregression.html";
        sessionFile = getClass().getResource("linearregression.xml");
    }
}
