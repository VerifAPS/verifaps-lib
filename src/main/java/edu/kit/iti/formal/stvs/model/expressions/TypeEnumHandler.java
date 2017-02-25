package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Gets invoked by {@link TypeEnum#match}.
 * This interface provides a way to handle an unknown type by calling
 * {@link Type#match}. If the type is an instance of {@link TypeEnum} this handler is called.
 */
@FunctionalInterface
public interface TypeEnumHandler<R> {
  /**
   * Must implement a method that gets called by {@link TypeEnum#match} and handle
   * the enum type accordingly.
   *
   * @param typeEnum {@link TypeEnum} from which this method was called
   * @return Object of type {@code R}
   */
  R handle(TypeEnum typeEnum);
}
