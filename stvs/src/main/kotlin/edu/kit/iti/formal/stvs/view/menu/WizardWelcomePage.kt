package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.StvsApplication;
import javafx.scene.control.Label;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.HBox;

/**
 * Created by leonk on 23.03.2017.
 */
public class WizardWelcomePage extends WizardPage {

  public WizardWelcomePage() {
    super("Welcome!");
    HBox introBox = new HBox(20);
    ImageView logo =
        new ImageView(new Image(StvsApplication.class.getResourceAsStream("logo.png")));
    Label intro = new Label(
        "Thank you for choosing STVerificationStudio!\nThis wizard will guide you through the installation of all third party dependencies.");
    introBox.getChildren().addAll(logo, intro);
    getChildren().add(introBox);
  }
}
