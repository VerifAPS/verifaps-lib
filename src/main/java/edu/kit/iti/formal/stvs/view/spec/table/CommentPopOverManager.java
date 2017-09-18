package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.Commentable;
import javafx.scene.Node;

public class CommentPopOverManager {
  private final Commentable commentable;
  private final boolean editable;
  private final CommentPopOver commentPopOver;

  public CommentPopOverManager(Commentable commentable, boolean editable, Node node) {
    this(commentable, editable, node, 0.0, 0.0);
  }

  public CommentPopOverManager(Commentable commentable, boolean editable, Node node, double x, double y) {
    if (node == null) {
      throw new NullPointerException("Node node cannot be null");
    }
    this.commentable = commentable;
    this.editable = editable;
    this.commentPopOver = new CommentPopOver();
    commentPopOver.show(node);
    commentPopOver.getTextArea().setText(commentable.getComment());
    commentPopOver.getSaveButton().setOnAction(actionEvent -> {
      commentable.setComment(commentPopOver.getTextArea().getText());
      commentPopOver.hide();
    });
  }
}
