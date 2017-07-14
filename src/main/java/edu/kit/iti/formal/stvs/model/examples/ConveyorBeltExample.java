package edu.kit.iti.formal.stvs.model.examples;

/**
 * Created by weigl on 14.07.2017.
 */
public class ConveyorBeltExample extends Example {

    public ConveyorBeltExample() {
        name = "Conveyor Belt";
        description = "A conveyor belt with multiple light barriers for error detection.";
        sessionFile = ConveyorBeltExample.class.getResource("conveyorbelt.xml");
        htmlHelp = ConveyorBeltExample.class.getResource("conveyorbelt.html").toExternalForm();
    }
}

