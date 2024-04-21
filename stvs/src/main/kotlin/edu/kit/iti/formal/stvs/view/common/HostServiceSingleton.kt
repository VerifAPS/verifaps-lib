package edu.kit.iti.formal.stvs.view.common

import javafx.application.HostServices

/**
 * Created by csicar on 16.03.17.
 */
object HostServiceSingleton {
    var instance: HostServices? = null
        set(newInstance) {
            check(field == null) { "already set" }
            field = newInstance
        }
}
