package edu.kit.iti.formal.stvs.view.spec.table;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.view.spec.Lockable;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.geometry.Insets;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.layout.VBox;
import org.controlsfx.control.PopOver;

public class CommentPopOver extends PopOver implements Lockable {
  private final BooleanProperty editable = new SimpleBooleanProperty(true);
  private final TextArea textArea;

  private final ButtonBar buttonBar;

  private final Button saveButton;

  public CommentPopOver() {
    super();
    textArea = new TextArea();
    saveButton = GlyphsDude.createIconButton(FontAwesomeIcon.SAVE);
    buttonBar = new ButtonBar();
    buttonBar.getButtons().addAll(saveButton);
    VBox content = new VBox(textArea, buttonBar);
    content.setPadding(new Insets(5));
    this.setTitle("Edit Comment");
    this.setContentNode(content);
    textArea.editableProperty().bind(editable);

  }


  @Override
  public boolean getEditable() {
    return editable.get();
  }

  @Override
  public BooleanProperty getEditableProperty() {
    return editable;
  }

  @Override
  public void setEditable(boolean editable) {
    this.editable.set(editable);
  }

  public TextArea getTextArea() {
    return textArea;
  }

  public Button getSaveButton() {
    return saveButton;
  }

}
