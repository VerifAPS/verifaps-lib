package edu.kit.iti.formal.stvs.logic.specification.choco;

import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.expression.discrete.relational.ReExpression;

import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Wraps a choco ArithmeticExpression OR a choco RelationalExpression
 */
public class ChocoExpressionWrapper {
  private final Optional<ArExpression> optionalArExpression;
  private final Optional<ReExpression> optionalReExpression;

  protected ChocoExpressionWrapper(ArExpression arExpression) {
    this.optionalArExpression = Optional.ofNullable(arExpression);
    this.optionalReExpression = Optional.empty();
  }

  protected ChocoExpressionWrapper(ReExpression reExpression) {
    this.optionalArExpression = Optional.empty();
    this.optionalReExpression = Optional.ofNullable(reExpression);
  }

  protected void ifArithmetic(Consumer<ArExpression> consumer) {
    optionalArExpression.ifPresent(consumer);
  }

  protected void ifRelational(Consumer<ReExpression> consumer) {
    optionalReExpression.ifPresent(consumer);
  }

  protected <R> Optional<R> ifArithmetic(Function<ArExpression, R> function) {
    return optionalArExpression.map(function);
  }

  protected <R> Optional<R> ifRelational(Function<ReExpression, R> function) {
    return optionalReExpression.map(function);
  }

  public void postIfRelational(){
    ifRelational(ReExpression::post);
  }

  /**
   * Reifies a relational expression as a variable and gives it back as an arithmetic expression
   *
   * Example:
   * The expression "x > 3" is a relationalExpression.
   * Reifying introduces a variable "a = x > 3" which is a boolean (integer with bounds [0,1])
   * This variable can be seen as an arithmetic expression
   *
   * @param reExpression Relational expression to be converted
   * @return arithmetic expression
   */
  private static ArExpression convertToArithmetic(ReExpression reExpression) {
    return reExpression.decompose().reify();
  }

  /**
   * Tries to convert the wrapped expression into an arithmetic expression.
   * At the time this is always possible.
   * If other non discrete expressions are allowed in the future this might change because of the distinction in choco.
   *
   * @return arithmetic expression
   */
  protected ArExpression convertToArithmetic() {
    return optionalArExpression.orElseGet(
        () -> {
          return optionalReExpression
              .map(ChocoExpressionWrapper::convertToArithmetic)
              .orElseThrow(() -> {
                return new IllegalStateException("The Expression can not be converted");
              });
        }
    );
  }

  protected <R> R autoArithmetic(Function<ArExpression, R> arFunction) {
    ArExpression arExpression = convertToArithmetic();
    return arFunction.apply(arExpression);
  }
}
