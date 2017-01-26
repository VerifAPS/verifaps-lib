package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.expressions.Value;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collector;

/**
 * This is a wrapper for a choco model which allows to assign values for a subset of the used variables
 * at any moment after creation.
 */
public class ChocoModel {
  private Model model = new Model();
  private Map<String, BoolVar> bools = new HashMap<>();
  private Map<String, IntVar> ints = new HashMap<>();
  private Map<String, IntVar> enums = new HashMap<>();
  private Set<Constraint> assignment = new HashSet<>();

  public ChocoModel(String name) {
    model = new Model(name);
  }

  public ArExpression addBool(String name) {
    if (bools.containsKey(name)) {
      return bools.get(name);
    }
    BoolVar bool = model.boolVar(name);
    bools.put(name, bool);
    return bool;
  }

  public ArExpression addInt(String name) {
    if (ints.containsKey(name)) {
      return ints.get(name);
    }
    IntVar integ = model.intVar(name, IntVar.MIN_INT_BOUND, IntVar.MAX_INT_BOUND);
    ints.put(name, integ);
    return integ;
  }

  public ArExpression addBoolLiteral(boolean value) {
    return model.boolVar(value);
  }

  public ArExpression addIntLiteral(int value) {
    return model.intVar(value);
  }

  public void addEnum(String name, int elements) {
    //TODO: Implement Enums. Propably with IntVars. Requires order of enum values of some kind...
  }

  public void solve() {
    model.getSolver().reset();
    model.getSolver().solve();
  }

  public void clearAssignment() {
    assignment.forEach(constraint -> model.unpost(constraint));
    assignment.clear();
  }

  public void solve(Map<String, Value> values) {
    //Clears previous assignment
    clearAssignment();
    //Posts a new constraint to set each variable in the map to a specific value
    values.entrySet().forEach(entry -> {
      Optional<Constraint> optionalConstraint = entry.getValue().match(
          integer -> {
            if (ints.containsKey(entry.getKey())) {
              Constraint constraint = ints.get(entry.getKey()).intVar().eq(integer).decompose();
              return Optional.of(constraint);
            }
            return Optional.empty();
          },
          bool -> {
            if (ints.containsKey(entry.getKey())) {
              Constraint constraint = ints.get(entry.getKey()).intVar().eq(bool ? 1 : 0).decompose();
              return Optional.of(constraint);
            }
            return Optional.empty();
          },
          enumeration -> Optional.empty()
      );
      optionalConstraint.ifPresent(constraint -> {
        constraint.post();
        assignment.add(constraint);
      });
    });
    solve();
  }

  public Map<String, BoolVar> getBools() {
    return bools;
  }

  public Map<String, IntVar> getInts() {
    return ints;
  }

  public Map<String, IntVar> getEnums() {
    return enums;
  }
}
