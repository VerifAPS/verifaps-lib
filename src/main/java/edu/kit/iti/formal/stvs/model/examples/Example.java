package edu.kit.iti.formal.stvs.model.examples;

import java.net.URL;

/**
 * This class represents an loadoable example.
 * <p>
 * You should derive this to add a new example to the system.
 * Examples are found via the {@link java.util.ServiceLoader} utility.
 *
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 * @see java.util.ServiceLoader
 */
public class Example {
    protected String name;
    protected String description;
    protected String htmlHelp;
    protected URL sessionFile;

    /**
     * The name of the example  to be displayed in the menu item.
     *
     * @return
     */
    public String getName() {
        return name;
    }

    /**
     * A text explaining further details, e.g. the conference.
     * This is used as a tooltip or sub-header.
     *
     * @return
     */
    public String getDescription() {
        return description;
    }

    /**
     * The name of the html page to loaded.
     *
     * @return a String if there is one html page or null.
     */
    public String getHtmlHelp() {
        return htmlHelp;
    }

    /**
     * The session (xml) file to be loaded.
     *
     * @return
     */
    public URL getSessionFile() {
        return sessionFile;
    }
}
