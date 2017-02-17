package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.Commentable;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.StringProperty;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.scene.layout.Pane;

import java.util.Optional;

public class CommentPopupManager {
  private boolean editable;
  private StringProperty comment;
  private Dialog dialog;
  private GlobalConfig globalConfig;

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
