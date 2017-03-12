package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Gets invoked by {@link ValueBool#match}. This interface provides a way to handle a value with
 * unknown type by calling {@link Value#match}. If the value is an instance of {@link ValueBool}
 * this handler is invoked.
 */
@FunctionalInterface
public interface ValueBooleanHandler<R> {
  /**
   * This method is called by {@link ValueBool#match}.
   *
   * @param value The value that the matched value represents
   * @return Object of type {@code R}
   */
  R handle(boolean value);
}
