package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.view.spec.Lockable;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.geometry.Insets;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.scene.control.TextArea;
import javafx.scene.layout.GridPane;

/**
 * @author Carsten Csiky
 */
public class CommentPopup extends Dialog<String> implements Lockable {
  private TextArea commentField;
  private String commentContent;
  private final BooleanProperty editable;

  public CommentPopup(String commentContent) {
    super();
    this.setTitle("Edit Comment");
    this.setContentText("Comment");
    this.commentContent = commentContent;
    this.commentField = new TextArea(commentContent);
    editable = new SimpleBooleanProperty();
    GridPane grid = new GridPane();
    grid.setHgap(10);
    grid.setVgap(10);
    grid.setPadding(new Insets(20, 150, 10, 10));
    grid.add(commentField, 0, 0);


    this.getDialogPane().getButtonTypes().addAll(ButtonType.APPLY, ButtonType.CANCEL);
    this.getDialogPane().setContent(grid);
    this.getDialogPane().setId("CommentPopupPane");


  }

  public TextArea getCommentField() {
    return commentField;
  }

  @Override
  public boolean getEditable() {
    return editable.get();
  }

  @Override
  public void setEditable(boolean b) {
    editable.set(b);
  }

  @Override
  public BooleanProperty getEditableProperty() {
    return editable;
  }
}
