package edu.kit.iti.formal.stvs.model.examples

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
class ElevatorExample : Example() {
    init {
        name = "Elevator"
        description = "Simple Demonstration"
        htmlHelp = javaClass.getResource("elevator.html").toExternalForm()
        sessionFile = javaClass.getResource("elevator.xml")
    }
}
