package edu.kit.iti.formal.stvs.model.expressions;

import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;

/**
 * Created by philipp on 23.01.17.
 */
public class TestIntervalParser {

  private static void assertParseEqual(String toBeParsed, String elaborationText, int lower, Integer upper)
    throws ParseException {
    assertEquals("Parse " + toBeParsed + elaborationText,
        new LowerBoundedInterval(lower, Optional.ofNullable(upper)),
        IntervalParser.parse(toBeParsed));
  }

  @Test
  public void testWildcard() throws ParseException {
    assertParseEqual("-", " as [0,-]", 0, null);
  }

  @Test
  public void testUpperBoundWildcard() throws ParseException {
    assertParseEqual("[5,-]", "", 5, null);
  }

  @Test
  public void testSimpleInterval() throws ParseException {
    assertParseEqual("[1,3]", "", 1, 3);
  }

  @Test
  public void testConstant() throws ParseException {
    assertParseEqual("3", " as [3,3]", 3, 3);
  }

  @Test(expected = ParseException.class)
  public void testNotNumbersInInterval() throws ParseException {
    assertParseEqual("[a,b]", " should fail", 0, 0);
  }

  @Test(expected = ParseException.class)
  public void testLowerBoundHigherThanHigherBound() throws ParseException {
    assertParseEqual("[3,2]", " should fail", 3, 2);
  }
}
