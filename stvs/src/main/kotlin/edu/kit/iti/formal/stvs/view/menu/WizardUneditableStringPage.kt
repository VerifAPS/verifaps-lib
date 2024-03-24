package edu.kit.iti.formal.stvs.view.menu;

import javafx.beans.property.StringProperty;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.VBox;
import javafx.scene.text.TextAlignment;

/**
 * Created by leonk on 23.03.2017.
 */
public class WizardUneditableStringPage extends WizardPage {

  public WizardUneditableStringPage(String title, String description,
      StringProperty uneditableText) {
    super(title);
    TextField uneditableTextField = new TextField();
    uneditableTextField.textProperty().bind(uneditableText);
    Label descriptionLabel = new Label(description);
    descriptionLabel.setWrapText(true);
    descriptionLabel.setTextAlignment(TextAlignment.JUSTIFY);
    this.getChildren().addAll(descriptionLabel, uneditableTextField);
    uneditableTextField.setDisable(true);
  }
}
