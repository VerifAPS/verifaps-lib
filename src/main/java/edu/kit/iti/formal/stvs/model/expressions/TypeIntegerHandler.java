package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Gets invoked by {@link TypeInt#match}.
 * This interface provides a way to handle an unknown type by calling
 * {@link Type#match}. If the type is an instance of {@link TypeInt} this handler is called.
 */
@FunctionalInterface
public interface TypeIntegerHandler<R> {
  /**
   * Must implement a method that gets called by {@link TypeInt#match}
   *
   * @return Object of type {@code R}
   */
  R handle();
}
