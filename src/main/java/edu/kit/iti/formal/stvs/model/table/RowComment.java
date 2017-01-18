package edu.kit.iti.formal.stvs.model.table;

import java.util.function.Consumer;

/**
 * Created by Philipp on 11.01.2017.
 */
public class RowComment implements Commentable {

  private String comment;

  public RowComment(String comment) {
    this.comment = comment;
  }

  @Override
  public void setComment(String comment) {

  }

  @Override
  public String getComment() {
    return null;
  }

  @Override
  public void addCommentListener(Consumer<Commentable> consumer) {

  }
}
