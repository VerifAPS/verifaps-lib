package edu.kit.iti.formal.stvs.model.code;

/**
 * Created by philipp on 09.01.17.
 *
 * @author Philipp
 */
public class FoldableCodeBlock {

  private int startLine;
  private int endLine;

  FoldableCodeBlock(int start, int end) {
    this.startLine = start;
    this.endLine = end;
  }

  public int getStartLine() {
    return startLine;
  }

  public int getEndLine() {
    return endLine;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof FoldableCodeBlock)) {
      return false;
    }

    FoldableCodeBlock that = (FoldableCodeBlock) obj;

    return startLine == that.startLine && endLine == that.endLine;
  }

  @Override
  public int hashCode() {
    int result = startLine;
    result = 31 * result + endLine;
    return result;
  }
}
