package edu.kit.iti.formal.stvs.view.menu;

import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.input.KeyCombination;


/**
 * Created by csicar on 10.01.17.
 */
public class StvsMenuBar extends MenuBar {
  public Menu file;
  public Menu edit;
  public Menu view;
  public Menu help;

  public MenuItem open;
  public MenuItem saveCode;
  public MenuItem saveSpec;
  public MenuItem saveAll;

  public StvsMenuBar() {
    //create top-level menus
    file = new Menu("File");
    edit = new Menu("Edit");
    view = new Menu("View");
    help = new Menu("Help");

    //create menu-items
    open = new MenuItem("Open");
    open.setAccelerator(KeyCombination.keyCombination("Ctrl+o"));

    saveCode = new MenuItem("Save Code");
    saveSpec = new MenuItem("Save Specification");

    saveAll = new MenuItem("Save all");
    saveAll.setAccelerator(KeyCombination.keyCombination("Ctrl+Shift+s"));


    //add menu-items to
    file.getItems().addAll(open, saveCode, saveSpec, saveAll);

    //add menus to itself
    this.getMenus().addAll(file, edit, view, help);
  }

}
