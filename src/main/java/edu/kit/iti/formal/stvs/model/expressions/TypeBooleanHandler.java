package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Gets invoked by {@link TypeBool#match}. This interface provides a way to handle an unknown type
 * by calling {@link Type#match}. If the type is an instance of {@link TypeBool} this handler is
 * called.
 */
@FunctionalInterface
public interface TypeBooleanHandler<R> {
  /**
   * Must implement a method that gets called by {@link TypeBool#match}.
   *
   * @return Object of type {@code R}
   */
  R handle();
}
