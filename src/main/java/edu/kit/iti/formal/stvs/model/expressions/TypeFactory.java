package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Arrays;

public class TypeFactory {

  public static TypeEnum enumOfName(String name, String... values) {
    return new TypeEnum(name, Arrays.asList(values));
  }

}
