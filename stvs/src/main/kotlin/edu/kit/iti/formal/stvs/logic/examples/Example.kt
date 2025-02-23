package edu.kit.iti.formal.stvs.logic.examples

import java.net.URL

/**
 * This class represents a loadoable example.
 *
 *
 * You should derive this to add a new example to the system.
 * Examples are found via the [java.util.ServiceLoader] utility.
 *
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 * @see java.util.ServiceLoader
 */
data class Example(
    /**
     * The name of the example to be displayed in the menu item.
     *
     * @return
     */
    var name: String,

    /**
     * A text explaining further details, e.g. the conference.
     * This is used as a tooltip or sub-header.
     *
     * @return
     */
    var description: String,

    /**
     * The name of the HTML page to load.
     *
     * @return a String if there is one HTML page or null.
     */
    var htmlHelp: String?,

    /**
     * The session (xml) file to be loaded.
     *
     * @return
     */
    var sessionFile: String,
) {
    val sessionUrl: URL
        get() = javaClass.getResource("/edu/kit/iti/formal/stvs/model/examples/$sessionFile")!!
}
