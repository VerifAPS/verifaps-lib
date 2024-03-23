package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Arrays;

/**
 * Helper class for quickly creating values of {@link TypeEnum}.
 *
 * @author Philipp
 */
public class TypeFactory {

  /**
   * Generates an enum type from name and values.
   *
   * @param name the name of the enum type
   * @param values the possible values that this enum type has
   * @return an instance of {@link TypeEnum}
   */
  public static TypeEnum enumOfName(String name, String... values) {
    return new TypeEnum(name, Arrays.asList(values));
  }

}
