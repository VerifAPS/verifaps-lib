package edu.kit.iti.formal.stvs.logic.specification;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;

import java.util.HashMap;
import java.util.Map;

/**
 * This is a wrapper for a choco model which allows to assign values for a subset of the used variables
 * at any moment after creation.
 */
public class ChocoModel {
  private Model model = new Model();
  private Map<String, BoolVar> bools = new HashMap<>();
  private Map<String, IntVar> ints = new HashMap<>();
  private Map<String, IntVar> enums = new HashMap<>();

  public ChocoModel(String name) {
    model = new Model(name);
  }

  public ArExpression addBool(String name) {
    BoolVar bool = model.boolVar(name);
    bools.put(name, bool);
    return bool;
  }

  public ArExpression addInt(String name) {
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

  public Solver getSolver(){
    return model.getSolver();
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
