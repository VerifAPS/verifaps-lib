package edu.kit.iti.formal.stvs.model.examples;

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
public final class ElevatorExample extends Example {
    public ElevatorExample() {
        name = "Elevator";
        description = "Demo";
        htmlHelp = null;//getClass().getResource("minmax.html");
        sessionFile = getClass().getResource("elevator.xml");
    }
}
