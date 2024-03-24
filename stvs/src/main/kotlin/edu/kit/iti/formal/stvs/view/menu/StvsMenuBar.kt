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
    // create top-level menus
    var file: Menu = Menu("_File")

    //public Menu edit;
    //edit = new Menu("Edit");
    var help: Menu = Menu("Help")
    var examples: Menu = Menu("_Examples")

    var openOther: Menu
    var openRecent: Menu
    var openRecentItems: MutableList<MenuItem?>

    // create menu-items
    var open: MenuItem = MenuItem("_Open")
    var openSpec: MenuItem
    var openCode: MenuItem
    var openSession: MenuItem
    var saveCode: MenuItem
    var saveSpec: MenuItem
    var saveAll: MenuItem
    var config: MenuItem
    var wizard: MenuItem
    var newCode: MenuItem
    var newSpec: MenuItem
    var saveSessionAs: MenuItem
    var about: MenuItem

    /**
     * Menu bar at the top of the window.
     */
    init {
        open.accelerator = KeyCombination.keyCombination("Ctrl+o")
        openOther = Menu("Open ...")
        openSpec = MenuItem("Open Specification")
        openCode = MenuItem("Open Code")
        openSession = MenuItem("Open Session")
        openRecent = Menu("Open Recent...")
        openRecentItems = ArrayList()

        saveCode = MenuItem("_Save Code")
        saveSpec = MenuItem("Save Specification")

        saveSessionAs = MenuItem("Save Session As")
        saveSessionAs.accelerator = KeyCombination.keyCombination("Shift+Ctrl+s")

        saveAll = MenuItem("Save Session")
        saveAll.accelerator = KeyCombination.keyCombination("Ctrl+s")

        config = MenuItem("_Preferences")
        config.accelerator = KeyCombination.keyCombination("Ctrl+,")

        wizard = MenuItem("Rerun configuration wizard")

        newCode = MenuItem("New Code")
        newSpec = MenuItem("New Specification")

        about = MenuItem("About")

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
