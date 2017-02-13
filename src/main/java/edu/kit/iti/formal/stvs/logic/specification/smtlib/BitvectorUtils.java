package edu.kit.iti.formal.stvs.logic.specification.smtlib;

/**
 * Created by leonk on 12.02.2017.
 */
public class BitvectorUtils {
  private static final char[] HEX_CHARS = new char[]{'0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
      'A', 'B', 'C', 'D', 'E', 'F'};

  public static String hexFromInt(int integer, int length) {
    if (integer < 0) {
      integer = (int) (Math.pow(16, length)) + integer;
    }
    String result = "";
    for (int i = 0; i < length; i++) {
      result = HEX_CHARS[integer % 16] + result;
      integer /= 16;
    }
    return "#x" + result;
  }

  public static int intFromHex(String hex, boolean signed) {
    if (hex == null || !hex.matches("\\#x[a-fA-F0-9]+"))
      throw new IllegalArgumentException("hex does not match expected format");
    hex = hex.substring(2);
    int result = 0;
    for (int i = 0; i < hex.length(); i++) {
      result *= 16;
      result += Integer.parseInt(hex.charAt(i) + "", 16);
    }
    int full = ((int) Math.pow(16, hex.length()));
    if (result >= full / 2 && signed) result = -(full - result);
    return result;
  }
}
