package edu.kit.iti.formal.stvs.view.menu

import javafx.scene.control.Menu
import javafx.scene.control.MenuBar
import javafx.scene.control.MenuItem
import javafx.scene.control.SeparatorMenuItem
import javafx.scene.input.KeyCombination

/**
 * Created by csicar on 10.01.17.
 *
 * @author Carsten Csiky
 */
class StvsMenuBar : MenuBar() {
    var file: Menu = Menu("_File")
    var help: Menu = Menu("Help")
    var examples: Menu = Menu("_Examples")

    // create menu-items
    var open: MenuItem = MenuItem("_Open")
    val openOther = Menu("Open ...")
    val openSpec = MenuItem("Open Specification")
    val openCode = MenuItem("Open Code")
    val openSession = MenuItem("Open Session")
    val openRecent = Menu("Open Recent...")
    val openRecentItems: MutableList<MenuItem> = arrayListOf()
    val saveCode = MenuItem("_Save Code")
    val saveSpec = MenuItem("Save Specification")
    val saveSessionAs = MenuItem("Save Session As")
    val saveAll = MenuItem("Save Session")
    val config = MenuItem("_Preferences")
    val wizard = MenuItem("Rerun configuration wizard")
    val newCode = MenuItem("New Code")
    val newSpec = MenuItem("New Specification")
    val about = MenuItem("About")

    /**
     * Menu bar at the top of the window.
     */
    init {
        open.accelerator = KeyCombination.keyCombination("Ctrl+o")
        saveSessionAs.accelerator = KeyCombination.keyCombination("Shift+Ctrl+s")
        saveAll.accelerator = KeyCombination.keyCombination("Ctrl+s")
        config.accelerator = KeyCombination.keyCombination("Ctrl+,")

        // Add menu items to "open other" menu
        openOther.items.addAll(openSpec, openCode, openSession)

        // Add menu items to "file" menu
        file.items.addAll(
            newCode, newSpec, open, openOther, openRecent,
            (SeparatorMenuItem()), saveCode, saveSpec, saveAll,
            saveSessionAs, (SeparatorMenuItem()), config
        )

        //edit.getItems().addAll(config);
        help.items.addAll(about, wizard)

        // Add menus to menubar
        menus.addAll(file, examples, help)
    }
}
