package edu.kit.iti.formal.stvs.model.examples

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
class PedestrianLightExample : Example() {
    init {
        name = "Pedestrian Light"
        description = "Demo"
        htmlHelp = javaClass.getResource("light.html").toExternalForm() //"https://formal.iti.kit.edu/stvs/minmax.html";
        sessionFile = javaClass.getResource("light.xml")
    }
}
