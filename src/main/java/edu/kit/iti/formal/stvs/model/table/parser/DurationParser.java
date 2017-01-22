package edu.kit.iti.formal.stvs.model.table.parser;

import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.LowerBoundedInterval;

import java.util.Optional;
import java.util.regex.Pattern;


/**
 * @author Benjamin Alt
 */
public class DurationParser {
  private static final String WILDCARD = "*";
  private static final String LEFT_PARENTHESIS = "[";
  private static final String RIGHT_PARENTHESIS = "]";
  private static final String SEPARATOR = ",";
  private static final Pattern DURATION_EXPR_PATTERN = Pattern.compile("\\[\\s*[0-9]+\\s*,\\s*[0-9]+\\s*\\]");



  public LowerBoundedInterval parse(ConstraintDuration constraintDuration) {
    String durationString = constraintDuration.getAsString().trim();
    if (durationString.equals(WILDCARD)) {
      return new LowerBoundedInterval(0, Optional.empty());
    } else if (durationString.startsWith(LEFT_PARENTHESIS)) {
      String leftBound = durationString.substring(1, durationString.indexOf(SEPARATOR)).trim();
      String rightBound = durationString.substring()
    }
  }
}
