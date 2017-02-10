package edu.kit.iti.formal.stvs.util;

import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * Created by philipp on 06.02.17.
 */
public class MapUtil {

  private MapUtil() {
  }

  public static <K, V0, V1> Map<K, V1> mapValues(Map<K, V0> sourceMap, Function<V0, V1> mapper) {
    return mapValuesWithKey(sourceMap, (key, value) -> mapper.apply(value));
  }

  public static <K, V0, V1> Map<K, V1> mapValuesWithKey(Map<K, V0> sourceMap, BiFunction<K, V0, V1> mapper) {
    Map<K, V1> map = new HashMap<K, V1>();
    mapValuesWithKey(sourceMap, map, mapper);
    return map;
  }

  public static <K, V0, V1> void mapValuesWithKey(Map<K, V0> sourceMap, Map<K, V1> mapToAddTo, BiFunction<K, V0, V1> mapper) {
    for (Map.Entry<K, V0> entry : sourceMap.entrySet()) {
      mapToAddTo.put(entry.getKey(), mapper.apply(entry.getKey(), entry.getValue()));
    }
  }
}
