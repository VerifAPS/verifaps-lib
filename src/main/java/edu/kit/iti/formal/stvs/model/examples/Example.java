package edu.kit.iti.formal.stvs.model.examples;

import java.net.URL;

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
public class Example {
    protected String name;
    protected String description;
    protected String htmlHelp;
    protected URL sessionFile;

    public String getName() {
        return name;
    }

    public String getDescription() {
        return description;
    }


    public String getHtmlHelp() {
        return htmlHelp;
    }

    public URL getSessionFile() {
        return sessionFile;
    }
}
