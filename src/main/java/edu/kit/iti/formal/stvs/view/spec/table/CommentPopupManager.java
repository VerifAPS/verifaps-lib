package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.Commentable;

import java.util.Optional;

import javafx.beans.property.StringProperty;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;

/**
 * <p>
 * This is the class that manages a popup for a given {@link Commentable} model instance.
 * </p>
 *
 * @author Carsten Csiky
 */
public class CommentPopupManager {
  private boolean editable;
  private StringProperty comment;
  private Dialog dialog;
  private GlobalConfig globalConfig;

  /**
   * <p>
   * This constructor opens a new {@link CommentPopup} with its text initialized to the given
   * {@link Commentable}'s comment. If the user changes the comment and closes the dialog, the
   * {@link Commentable}'s comment is updated.
   * </p>
   *
   * <p>
   * This constructor therefore manages the whole cycle of editing a comment (open, edit, close,
   * update).
   * </p>
   *
   * @param commentable the commentable model to be updated.
   * @param editable whether the comment should be editable or only to open a dialog for comment
   *        viewing purposes
   * @param globalConfig a configuration that might influence the editor's appearence (for example
   *        font size)
   */
  public CommentPopupManager(Commentable commentable, boolean editable, GlobalConfig globalConfig) {
    this.globalConfig = globalConfig;
    CommentPopup popup = new CommentPopup(commentable.getComment());
    popup.setEditable(editable);

    popup.setResultConverter((dialogButton) -> {
      if (dialogButton != ButtonType.APPLY) {
        return null;
      }
      return popup.getCommentField().getText();
    });
    Optional<String> newValue = popup.showAndWait();
    System.out.println(newValue);
    newValue.ifPresent(commentable::setComment);

  }

  public StringProperty getCommentProperty() {
    return comment;
  }

}
