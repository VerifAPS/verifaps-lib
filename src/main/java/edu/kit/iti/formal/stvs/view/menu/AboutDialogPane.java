package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.StvsApplication;
import javafx.geometry.Pos;
import javafx.scene.control.*;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.VBox;
import javafx.scene.text.Font;

/**
 * <p>
 * The Dialog Pane that shows 'About' information.
 * </p>
 *
 * <p>
 * Is created when the user clicks on 'Help' -> 'About' and shows the name and version information,
 * etc.
 * </p>
 *
 * <p>
 * Created by csicar on 16.02.17.
 * </p>
 *
 * @author Carsten Csiky
 */
public class AboutDialogPane extends DialogPane {

  private VBox content;

  /**
   * Creates the Dialog Pane that displays 'About' information.
   */
  public AboutDialogPane() {
    Image logo = new Image(StvsApplication.class.getResourceAsStream("logo.png"));
    ImageView logoView = new ImageView(logo);
    Label name = new Label("Structured Text Verification Studio - STVS");
    name.setFont(Font.font("DejaVu Sans Mono", 30));
    Label version = new Label("Version: 1.1");

    this.content = new VBox(logoView, name, version);
    this.content.setAlignment(Pos.CENTER);
    this.getButtonTypes().addAll(ButtonType.CLOSE);
    this.setContent(content);

  }
}
