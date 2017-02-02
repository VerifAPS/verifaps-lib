package edu.kit.iti.formal.stvs.view.menu;

import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.input.KeyCombination;


/**
 * Created by csicar on 10.01.17.
 */
public class StvsMenuBar extends MenuBar {

  public Menu file;
  public Menu edit;
  public Menu view;
  public Menu help;

  public Menu openOther;

  public MenuItem open;
  public MenuItem openSpec;
  public MenuItem openCode;
  public MenuItem openSession;
  public MenuItem saveCode;
  public MenuItem saveSpec;
  public MenuItem saveAll;
  public MenuItem config;

  public StvsMenuBar() {
    //create top-level menus
    file = new Menu("File");
    edit = new Menu("Edit");
    view = new Menu("View");
    help = new Menu("Help");

    //create menu-items
    open = new MenuItem("Open");
    openOther = new Menu("Open ...");
    open.setAccelerator(KeyCombination.keyCombination("Ctrl+o"));
    openSpec = new MenuItem("Open Specification");
    openCode = new MenuItem("Open Code");
    openSession = new MenuItem("Open Session");


    saveCode = new MenuItem("Save Code");
    saveSpec = new MenuItem("Save Specification");

    saveAll = new MenuItem("Save all");
    saveAll.setAccelerator(KeyCombination.keyCombination("Ctrl+Shift+s"));

    config = new MenuItem("Configuration");
    config.setAccelerator(KeyCombination.keyCombination("Ctrl+,"));


    //add menu-items to
    openOther.getItems().addAll(openSpec, openCode, openSession);
    file.getItems().addAll(open, openOther, saveCode, saveSpec, saveAll, (new
        SeparatorMenuItem()), config);

    //add menus to itself
    this.getMenus().addAll(file, edit, view, help);
  }

}
