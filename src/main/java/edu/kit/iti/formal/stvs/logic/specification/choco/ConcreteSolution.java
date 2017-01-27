package edu.kit.iti.formal.stvs.logic.specification.choco;

import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;

import java.util.Map;

/**
 * Created by leonk on 26.01.2017.
 */
public class ConcreteSolution {

  private final Map<String, ValueInt> intMap;
  private final Map<String, ValueBool> boolMap;
  private final Map<String, ValueEnum> enumMap;

  public ConcreteSolution(Map<String, ValueInt> intMap, Map<String, ValueBool> boolMap, Map<String, ValueEnum> enumMap) {
    this.intMap = intMap;
    this.boolMap = boolMap;
    this.enumMap = enumMap;
  }

  public Map<String, ValueInt> getIntMap() {
    return intMap;
  }

  public Map<String, ValueBool> getBoolMap() {
    return boolMap;
  }

  public Map<String, ValueEnum> getEnumMap() {
    return enumMap;
  }
}
