package edu.kit.iti.formal.stvs.model.examples

/**
 * Created by weigl on 14.07.2017.
 */
class ConveyorBeltExample : Example() {
    init {
        name = "Conveyor Belt"
        description = "A conveyor belt with multiple light barriers for error detection."
        sessionFile = ConveyorBeltExample::class.java.getResource("conveyorbelt.xml")
        htmlHelp = ConveyorBeltExample::class.java.getResource("conveyorbelt.html")?.toExternalForm()
    }
}

