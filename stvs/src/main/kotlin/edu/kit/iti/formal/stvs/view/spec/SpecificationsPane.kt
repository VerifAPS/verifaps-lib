package edu.kit.iti.formal.stvs.view.spec

import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.scene.layout.AnchorPane

/**
 * This Pane displays a collection of specifications as tabs.
 *
 * @author Carsten Csiky
 */
class SpecificationsPane : AnchorPane() {
    val tabPane: TabPane = TabPane()
    val addButton: Button = Button("+")

    /**
     * Creates an empty instance.
     */
    init {
        ViewUtils.setupClass(this)


        setTopAnchor(tabPane, 0.0)
        setLeftAnchor(tabPane, 0.0)
        setRightAnchor(tabPane, 0.0)
        setBottomAnchor(tabPane, 0.0)
        setTopAnchor(addButton, 5.0)
        setRightAnchor(addButton, 5.0)

        children.addAll(tabPane, addButton)
    }

    val tabs: ObservableList<Tab?>
        get() = tabPane.tabs

    /**
     * Defines what should be invoked if a tab is added.
     * @param listener method to invoke
     */
    fun onTabAdded(listener: Runnable) {
        addButton.onAction = EventHandler { actionEvent: ActionEvent? ->
            listener.run()
        }
    }
}
