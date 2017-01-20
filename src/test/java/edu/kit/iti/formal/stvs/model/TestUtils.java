package edu.kit.iti.formal.stvs.model;

import java.util.Collection;
import java.util.Set;

/**
 * Created by Philipp on 20.01.2017.
 */
public class TestUtils {

  private TestUtils() {
  }

  public static <T> boolean collectionsEqual(Collection<T> as, Collection<T> bs) {
    if (as == bs) return true;
    if (as == null || bs == null) return false;
    if (as.size() != bs.size()) return false;

    return as.stream().allMatch(elem -> bs.stream().anyMatch(elem::equals));
  }

  public static <T> void assertCollectionsEqual(Collection<T> as, Collection<T> bs) {
    if (!collectionsEqual(as, bs)) {
      String error = String.format("Unequal collections: %n" +
          "Expected: %s%n" +
          "Actual  : %s%n", as, bs);
      throw new AssertionError(error);
    }
  }
}
