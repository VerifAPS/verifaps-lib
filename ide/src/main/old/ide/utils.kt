package edu.kit.iti.formal.automation.ide

import bibliothek.gui.dock.common.action.CAction
import bibliothek.gui.dock.common.action.CButton
import bibliothek.gui.dock.common.action.core.CommonSimpleButtonAction
import bibliothek.gui.dock.common.intern.DefaultCDockable
import java.awt.event.ActionEvent
import javax.swing.*
import kotlin.properties.ReadWriteProperty
import kotlin.reflect.KProperty
import java.util.ArrayList
import java.io.IOException
import java.awt.Desktop
import java.io.File
import java.net.URI


fun DefaultCDockable.addAction(action: IdeAction) {
    val act = CButton(action.name, action.smallIcon)
    act.addActionListener(action)
    //TODO register property change listener
    addAction(act)
}

class LambdaAction(val lambda: () -> Unit) : IdeAction() {
    override fun actionPerformed(e: ActionEvent?) = lambda()
}

val ACTION_MENU_PATH_KEY = "MENU_PATH"
val ACTION_PRIO_KEY = "PRIO_KEY"
val ACTION_TOOLBAR_KEY = "TOOLBAR_KEY"

abstract class IdeAction : AbstractAction() {
    var name: String? by map(Action.NAME)
    var largeIcon: Icon? by map(Action.LARGE_ICON_KEY)
    var smallIcon: Icon? by map(Action.SMALL_ICON)
    var accelerator: KeyStroke? by map(Action.ACCELERATOR_KEY)
    var actionCommand: String? by map(Action.ACTION_COMMAND_KEY)
    var mnemonic: Char? by map(Action.MNEMONIC_KEY)
    var longDescription: String? by map(Action.LONG_DESCRIPTION)
    var shortDescription: String? by map(Action.SHORT_DESCRIPTION)
    var selected: Boolean? by map(Action.SELECTED_KEY)
    var menuPath: String by map(ACTION_MENU_PATH_KEY)
    var priority: Int by map(ACTION_PRIO_KEY)
    var toolbarId: String? by map(ACTION_TOOLBAR_KEY)

    inner class map<T>(val key: String) : ReadWriteProperty<IdeAction, T> {
        override fun getValue(thisRef: IdeAction, property: KProperty<*>): T = getValue(key) as T
        override fun setValue(thisRef: IdeAction, property: KProperty<*>, value: T) = putValue(key, value)
    }
}


fun createAction(name: String,
                 menuPath: String = "",
                 accel: KeyStroke? = null,
                 prio: Int = 0,
                 shortDesc: String? = null,
                 longDesc: String? = null,
                 smallIcon: Icon? = null,
                 largeIcon: Icon? = null,
                 fontIcon: FontIcon? = null,
                 f: () -> Unit): IdeAction {
    val myAction = LambdaAction(f)
    myAction.priority = prio
    myAction.name = name
    myAction.menuPath = menuPath
    myAction.accelerator = accel
    myAction.shortDescription = shortDesc
    myAction.longDescription = longDesc
    myAction.smallIcon = smallIcon
    myAction.largeIcon = largeIcon

    if (fontIcon != null) {
        myAction.largeIcon = IconFontSwing.buildIcon(fontIcon, 24f)
        myAction.smallIcon = IconFontSwing.buildIcon(fontIcon, 16f)
    }
    return myAction
}

interface DesktopServices {

}


object DesktopApi {
    val os: EnumOS
        get() {
            val s = System.getProperty("os.name").toLowerCase()
            return when {
                s.contains("win") -> return EnumOS.windows
                s.contains("mac") -> return EnumOS.macos
                s.contains("solaris") -> return EnumOS.solaris
                s.contains("sunos") -> return EnumOS.solaris
                s.contains("linux") -> return EnumOS.linux
                s.contains("unix") -> return EnumOS.linux
                else -> EnumOS.unknown
            }
        }

    fun browse(uri: URI): Boolean {
        if (openSystemSpecific(uri.toString())) return true
        return browseDESKTOP(uri)
    }

    fun open(file: File): Boolean {

        if (openSystemSpecific(file.path)) return true

        return if (openDESKTOP(file)) true else false

    }

    fun edit(file: File): Boolean {
        // you can try something like
        // runCommand("gimp", "%s", file.getPath())
        // based on user preferences.
        if (openSystemSpecific(file.path)) return true
        return if (editDESKTOP(file)) true else false
    }


    private fun openSystemSpecific(what: String): Boolean {

        val os = os

        if (os.isLinux) {
            if (runCommand("kde-open", "%s", what)) return true
            if (runCommand("gnome-open", "%s", what)) return true
            if (runCommand("xdg-open", "%s", what)) return true
        }

        if (os.isMac) {
            if (runCommand("open", "%s", what)) return true
        }

        if (os.isWindows) {
            if (runCommand("explorer", "%s", what)) return true
        }

        return false
    }

    private fun browseDESKTOP(uri: URI): Boolean {
        logOut("Trying to use Desktop.getDesktop().browse() with " + uri.toString())
        try {
            if (!Desktop.isDesktopSupported()) {
                logErr("Platform is not supported.")
                return false
            }

            if (!Desktop.getDesktop().isSupported(Desktop.Action.BROWSE)) {
                logErr("BROWSE is not supported.")
                return false
            }

            Desktop.getDesktop().browse(uri)

            return true
        } catch (t: Throwable) {
            logErr("Error using desktop browse.", t)
            return false
        }

    }

    private fun openDESKTOP(file: File): Boolean {
        logOut("Trying to use Desktop.getDesktop().open() with $file")
        try {
            if (!Desktop.isDesktopSupported()) {
                logErr("Platform is not supported.")
                return false
            }

            if (!Desktop.getDesktop().isSupported(Desktop.Action.OPEN)) {
                logErr("OPEN is not supported.")
                return false
            }

            Desktop.getDesktop().open(file)

            return true
        } catch (t: Throwable) {
            logErr("Error using desktop open.", t)
            return false
        }

    }

    private fun editDESKTOP(file: File): Boolean {
        logOut("Trying to use Desktop.getDesktop().edit() with $file")
        try {
            if (!Desktop.isDesktopSupported()) {
                logErr("Platform is not supported.")
                return false
            }

            if (!Desktop.getDesktop().isSupported(Desktop.Action.EDIT)) {
                logErr("EDIT is not supported.")
                return false
            }

            Desktop.getDesktop().edit(file)

            return true
        } catch (t: Throwable) {
            logErr("Error using desktop edit.", t)
            return false
        }

    }


    private fun runCommand(command: String, args: String, file: String): Boolean {

        logOut("Trying to exec:\n   cmd = $command\n   args = $args\n   %s = $file")

        val parts = prepareCommand(command, args, file)

        try {
            val p = Runtime.getRuntime().exec(parts) ?: return false

            try {
                val retval = p.exitValue()
                if (retval == 0) {
                    logErr("Process ended immediately.")
                    return false
                } else {
                    logErr("Process crashed.")
                    return false
                }
            } catch (itse: IllegalThreadStateException) {
                logErr("Process is running.")
                return true
            }

        } catch (e: IOException) {
            logErr("Error running command.", e)
            return false
        }

    }


    private fun prepareCommand(command: String, args: String?, file: String): Array<String> {
        val parts = ArrayList<String>()
        parts.add(command)
        if (args != null) {
            for (s in args.split(" ".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()) {
                val a = String.format(s, file) // put in the filename thing
                parts.add(a.trim { it <= ' ' })
            }
        }
        return parts.toTypedArray()
    }

    private fun logErr(msg: String, t: Throwable) {
        System.err.println(msg)
        t.printStackTrace()
    }

    private fun logErr(msg: String) {
        System.err.println(msg)
    }

    private fun logOut(msg: String) {
        println(msg)
    }

    enum class EnumOS {
        linux, macos, solaris, unknown, windows;

        val isLinux: Boolean
            get() = this == linux || this == solaris


        val isMac: Boolean
            get() = this == macos


        val isWindows: Boolean
            get() = this == windows
    }
}