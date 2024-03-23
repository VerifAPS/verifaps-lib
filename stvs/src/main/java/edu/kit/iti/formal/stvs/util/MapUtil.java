package edu.kit.iti.formal.stvs.util;

import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * Util class for map functions.
 *
 * @author Philipp
 */
public class MapUtil {

  private MapUtil() {}

  /**
   * Applies {@link MapUtil#mapValuesWithKey(Map, Map, BiFunction)} with an empty target
   * map and ignores indices of source elements.
   *
   * @param sourceMap map to operate on.
   * @param mapper Function that maps from {@code sourceMap}
   *               elements to {@code mapToAddTo} elements.
   * @param <K> index type of both maps
   * @param <V0> value type of source map
   * @param <V1> value type of target map
   * @see MapUtil#mapValuesWithKey(Map, Map, BiFunction)
   * @return map with mapped values
   */
  public static <K, V0, V1> Map<K, V1> mapValues(Map<K, V0> sourceMap, Function<V0, V1> mapper) {
    return mapValuesWithKey(sourceMap, (key, value) -> mapper.apply(value));
  }


  /**
   * Applies {@link MapUtil#mapValuesWithKey(Map, Map, BiFunction)} with an empty target map.
   *
   * @param sourceMap map to operate on.
   * @param mapper Function that maps from {@code sourceMap}
   *               elements and their index to {@code mapToAddTo} elements.
   * @param <K> index type of both maps
   * @param <V0> value type of source map
   * @param <V1> value type of target map
   * @see MapUtil#mapValuesWithKey(Map, Map, BiFunction)
   * @return map with mapped values
   */
  public static <K, V0, V1> Map<K, V1> mapValuesWithKey(Map<K, V0> sourceMap,
      BiFunction<K, V0, V1> mapper) {
    Map<K, V1> map = new HashMap<K, V1>();
    mapValuesWithKey(sourceMap, map, mapper);
    return map;
  }

  /**
   * Takes each element of {@code sourceMap} and calls {@code mapper}
   * with the index and value of the element.
   * The returned value is added to {@code mapToAddTo}.
   *
   * @param sourceMap map to operate on.
   * @param mapToAddTo Target map. Mapped elements will be put in this map.
   * @param mapper Function that maps from {@code sourceMap}
   *               elements and their index to {@code mapToAddTo} elements.
   * @param <K> index type of both maps
   * @param <V0> value type of source map
   * @param <V1> value type of target map
   */
  public static <K, V0, V1> void mapValuesWithKey(Map<K, V0> sourceMap, Map<K, V1> mapToAddTo,
      BiFunction<K, V0, V1> mapper) {
    for (Map.Entry<K, V0> entry : sourceMap.entrySet()) {
      mapToAddTo.put(entry.getKey(), mapper.apply(entry.getKey(), entry.getValue()));
    }
  }
}
