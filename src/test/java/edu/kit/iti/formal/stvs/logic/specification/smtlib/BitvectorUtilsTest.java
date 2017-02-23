package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by leonk on 21.02.2017.
 */
public class BitvectorUtilsTest {
  @Test
  public void testEquality(){
    for(int i = -32768; i <= 32767; i++){
      assertEquals(i, BitvectorUtils.intFromHex(BitvectorUtils.hexFromInt(i, 4), true));
    }
    for(int i = 0; i <= 65535; i++){
      assertEquals(i, BitvectorUtils.intFromHex(BitvectorUtils.hexFromInt(i, 4), false));
    }
  }

  @Test
  public void testCritical(){
    assertEquals(32767, BitvectorUtils.intFromHex("#x7FFF", true));
    assertEquals(-32768, BitvectorUtils.intFromHex("#x8000", true));
    assertEquals(0, BitvectorUtils.intFromHex("#x0000", true));
    assertEquals(-1, BitvectorUtils.intFromHex("#xFFFF", true));

    assertEquals(32767, BitvectorUtils.intFromHex("#x7FFF", false));
    assertEquals(32768, BitvectorUtils.intFromHex("#x8000", false));
    assertEquals(0, BitvectorUtils.intFromHex("#x0000", false));
    assertEquals(65535, BitvectorUtils.intFromHex("#xFFFF", false));
  }

  @Test(expected = IllegalArgumentException.class)
  public void testWrongFormat(){
    BitvectorUtils.intFromHex("notvalid", true);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testNull(){
    BitvectorUtils.intFromHex(null, false);
  }
}