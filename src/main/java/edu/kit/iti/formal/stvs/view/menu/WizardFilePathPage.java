package edu.kit.iti.formal.stvs.view.menu;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.view.common.ActualHyperLink;
import edu.kit.iti.formal.stvs.view.common.FileSelectionField;

import java.io.File;

import javafx.beans.Observable;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.StringProperty;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;


/**
 * Created by leonk on 22.03.2017.
 */
public class WizardFilePathPage extends WizardPage {
  private final FileSelectionField filePathField = new FileSelectionField();
  private final BooleanProperty valid = new SimpleBooleanProperty();
  private final HBox notValidContainer = new HBox(20.0);

  public WizardFilePathPage(String title, String description, StringProperty filePath) {
    super(title);

    Node notValidIcon = GlyphsDude.createIcon(FontAwesomeIcon.EXCLAMATION_TRIANGLE);
    notValidContainer.getChildren().addAll(notValidIcon,
        new Label("Something is wrong with this path. Not all features of STVS will work as expected!"));
    notValidContainer.visibleProperty().bind(valid.not());
    filePathField.getTextField().textProperty().addListener(this::validator);
    validator(filePathField.getTextField().textProperty());

    this.getChildren().addAll(new Label(description), filePathField, notValidContainer);
    filePathField.getTextField().textProperty().bindBidirectional(filePath);

  }

  public WizardFilePathPage(String title, String description, StringProperty filePath,
      String downloadLink) {
    this(title, description, filePath);
    this.getChildren().addAll(new Label("Download the dependency from:"),
        new ActualHyperLink(downloadLink, downloadLink));
  }

  private void validator(Observable observable) {
    String path = filePathField.getTextField().textProperty().get();
    if (path != null && new File(path).canRead()) {
      valid.setValue(true);
    } else {
      valid.setValue(false);
    }
  }

  public boolean isValid() {
    return valid.get();
  }

  public BooleanProperty validProperty() {
    return valid;
  }
}
