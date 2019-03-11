package edu.kit.iti.formal.automation.ide

import java.awt.event.ActionEvent
import javax.swing.*
import kotlin.properties.ReadWriteProperty
import kotlin.reflect.KProperty

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.03.19)
 */

class LambdaAction(val lambda: () -> Unit) : MyAction() {
    override fun actionPerformed(e: ActionEvent?) = lambda()
}

val ACTION_MENU_PATH_KEY = "MENU_PATH"
val ACTION_PRIO_KEY = "PRIO_KEY"

abstract class MyAction : AbstractAction() {
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

    inner class map<T>(val key: String) : ReadWriteProperty<MyAction, T> {
        override fun getValue(thisRef: MyAction, property: KProperty<*>): T = getValue(key) as T
        override fun setValue(thisRef: MyAction, property: KProperty<*>, value: T) = putValue(key, value)
    }
}


fun createAction(name: String, menuPath: String, accel: KeyStroke? = null,
                 prio: Int = 0,
                 shortDesc: String? = null,
                 longDesc: String? = null,
                 smallIcon: Icon? = null,
                 largeIcon: Icon? = null,
                 fontIcon: FontIcon? = null,
                 f: () -> Unit): MyAction {
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

abstract class TabbedPanel : JPanel() {
    val tabPane: JTabbedPane?
        get() = parent as? JTabbedPane

    var title: String? = null
        set(value) {
            tabPane?.also {
                it.setTitleAt(it.indexOfComponent(this), value)
            }
            field = value
        }
    var icon: Icon? = null
        set(value) {
            tabPane?.also {
                it.setIconAt(it.indexOfComponent(this), value)
            }
            field = value
        }

    var tip: String? = null
        set(value) {
            tabPane?.also {
                it.setToolTipTextAt(it.indexOfComponent(this), value)
            }
            field = value
        }
}