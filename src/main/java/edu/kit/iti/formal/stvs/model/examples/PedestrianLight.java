package edu.kit.iti.formal.stvs.model.examples;

import java.net.URL;

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
public final class PedestrianLight extends Example {
    public PedestrianLight() {
        name = "Pedestrian Light";
        description = "Demo";
        htmlHelp = getClass().getResource("minmax.html").toExternalForm();//"https://formal.iti.kit.edu/stvs/minmax.html";
        sessionFile = getClass().getResource("light.xml");
    }
}
