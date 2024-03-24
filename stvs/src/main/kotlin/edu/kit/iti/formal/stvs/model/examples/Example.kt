package edu.kit.iti.formal.stvs.model.examples

import java.net.URL

/**
 * This class represents an loadoable example.
 *
 *
 * You should derive this to add a new example to the system.
 * Examples are found via the [java.util.ServiceLoader] utility.
 *
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 * @see java.util.ServiceLoader
 */
open class Example {
    /**
     * The name of the example to be displayed in the menu item.
     *
     * @return
     */
    var name: String? = null
        protected set

    /**
     * A text explaining further details, e.g. the conference.
     * This is used as a tooltip or sub-header.
     *
     * @return
     */
    var description: String? = null
        protected set

    /**
     * The name of the html page to loaded.
     *
     * @return a String if there is one html page or null.
     */
    var htmlHelp: String? = null
        protected set

    /**
     * The session (xml) file to be loaded.
     *
     * @return
     */
    var sessionFile: URL? = null
        protected set
}
