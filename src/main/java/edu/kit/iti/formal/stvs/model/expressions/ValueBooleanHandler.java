package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Gets invoked by {@link ValueBool#match}. This interface provides a way to handle an unknown value
 * by calling {@link Value#match}. If the value is an instance of {@link ValueBool} this handler is
 * called.
 */
@FunctionalInterface
public interface ValueBooleanHandler<R> {
  /**
   * Must implement a method that gets called by {@link ValueBool#match}
   *
   * @param value The value that the matched value represents
   * @return Object of type {@code R}
   */
  R handle(boolean value);
}
