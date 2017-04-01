package edu.kit.iti.formal.stvs.model.examples;

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
public final class MinMaxExample extends Example {
    public MinMaxExample() {
        name = "MinMaxWarning";
        description = "Example of iFM'17 Paper";
        htmlHelp = "https://formal.iti.kit.edu/minmax.html";
        sessionFile = getClass().getResource("minmax.xml");
    }
}
