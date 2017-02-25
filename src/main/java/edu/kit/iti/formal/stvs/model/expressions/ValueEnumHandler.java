package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Gets invoked by {@link ValueEnum#match}.
 * This interface provides a way to handle an unknown value by calling
 * {@link Value#match}. If the value is an instance of {@link ValueEnum} this handler is called.
 */
@FunctionalInterface
public interface ValueEnumHandler<R> {
  /**
   * Must implement a method that gets called by {@link ValueEnum#match}
   * @param value The value that the matched value represents
   * @return Object of type {@code R}
   */
  R handle(ValueEnum value);
}
