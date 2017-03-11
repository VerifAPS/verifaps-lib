package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Gets invoked by {@link ValueInt#match}. This interface provides a way to handle a value of
 * unknown type by calling {@link Value#match}. If the value is an instance of {@link ValueInt} this
 * handler is called.
 */
@FunctionalInterface
public interface ValueIntegerHandler<R> {
  /**
   * Must implement a method that gets called by {@link ValueInt#match}.
   *
   * @param value The value that the matched value represents
   * @return Object of type {@code R}
   */
  R handle(int value);
}
