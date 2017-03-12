package edu.kit.iti.formal.stvs.model.code;

/**
 * A block of source code. Although code folding is not supported by the view, this class may be
 * used in future versions to implement code folding.
 *
 * @author Philipp
 */
public class FoldableCodeBlock {

  private int startLine;
  private int endLine;

  /**
   * Create a new FoldableCodeBlock from a start and an end line index (inclusive).
   * @param start The index of the first line of the block
   * @param end The index of the last line of the block
   */
  FoldableCodeBlock(int start, int end) {
    this.startLine = start;
    this.endLine = end;
  }

  /**
   * Get the index of the last line of the code block.
   * @return The index of the first line of the code block
   */
  public int getStartLine() {
    return startLine;
  }

  /**
   * Get the index of the first line of the code block.
   * @return The index of the first line of the code block
   */
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
