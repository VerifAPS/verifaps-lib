package edu.kit.iti.formal.stvs.view.menu;

import java.util.ArrayList;
import java.util.List;

import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.input.KeyCombination;


/**
 * Created by csicar on 10.01.17.
 *
 * @author Carsten Csiky
 */
public class StvsMenuBar extends MenuBar {

  public Menu file;
  public Menu edit;
  public Menu help;

  public Menu openOther;
  public Menu openRecent;
  public List<MenuItem> openRecentItems;

  public MenuItem open;
  public MenuItem openSpec;
  public MenuItem openCode;
  public MenuItem openSession;
  public MenuItem saveCode;
  public MenuItem saveSpec;
  public MenuItem saveAll;
  public MenuItem config;
  public MenuItem wizard;
  public MenuItem newCode;
  public MenuItem newSpec;
  public MenuItem saveSessionAs;
  public MenuItem about;

  /**
   * Menu bar at the top of the window.
   */
  public StvsMenuBar() {
    // create top-level menus
    file = new Menu("File");
    edit = new Menu("Edit");
    help = new Menu("Help");

    // create menu-items
    open = new MenuItem("Open");
    open.setAccelerator(KeyCombination.keyCombination("Ctrl+o"));
    openOther = new Menu("Open ...");
    openSpec = new MenuItem("Open Specification");
    openCode = new MenuItem("Open Code");
    openSession = new MenuItem("Open Session");
    openRecent = new Menu("Open Recent...");
    openRecentItems = new ArrayList<>();

    saveCode = new MenuItem("Save Code");
    saveSpec = new MenuItem("Save Specification");

    saveSessionAs = new MenuItem("Save Session As");
    saveSessionAs.setAccelerator(KeyCombination.keyCombination("Shift+Ctrl+s"));

    saveAll = new MenuItem("Save Session");
    saveAll.setAccelerator(KeyCombination.keyCombination("Ctrl+s"));

    config = new MenuItem("Preferences");
    config.setAccelerator(KeyCombination.keyCombination("Ctrl+,"));

    wizard = new MenuItem("Rerun configuration wizard");


    newCode = new MenuItem("New Code");
    newSpec = new MenuItem("New Specification");

    about = new MenuItem("About");

    // Add menu items to "open other" menu
    openOther.getItems().addAll(openSpec, openCode, openSession);

    // Add menu items to "file" menu
    file.getItems().addAll(newCode, newSpec, open, openOther, openRecent, (new SeparatorMenuItem()),
        saveCode, saveSpec, saveAll, saveSessionAs);

    edit.getItems().addAll(config, wizard);

    help.getItems().addAll(about);

    // Add menus to menubar
    this.getMenus().addAll(file, edit, help);
  }
}
