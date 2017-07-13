package edu.kit.iti.formal.stvs.model.examples;

import java.net.URL;

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
public final class PedestrianLightExample extends Example {
    public PedestrianLightExample() {
        name = "Pedestrian Light";
        description = "Demo";
        htmlHelp = getClass().getResource("light.html").toExternalForm();//"https://formal.iti.kit.edu/stvs/minmax.html";
        sessionFile = getClass().getResource("light.xml");
    }
}
