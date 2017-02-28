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
 * <p>The popup dialog for editing comments on table cells, rows or tables as a whole.</p>
 *
 * @author Carsten Csiky
 */
public class CommentPopup extends Dialog<String> implements Lockable {
  private TextArea commentField;
  private String commentContent;
  private final BooleanProperty editable;

  /**
   * <p>Creates a javafx dialog with a text area for a comment that can be edited,
   * if this class has not been locked (see {@link Lockable}).</p>
   *
   * @param commentContent the initial comment content of the dialog.
   */
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
  public void setEditable(boolean editable) {
    this.editable.set(editable);
  }

  @Override
  public BooleanProperty getEditableProperty() {
    return editable;
  }
}
