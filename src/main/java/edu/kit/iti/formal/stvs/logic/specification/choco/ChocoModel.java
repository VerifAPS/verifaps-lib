package edu.kit.iti.formal.stvs.logic.specification.choco;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solution;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.objective.ObjectiveStrategy;
import org.chocosolver.solver.objective.OptimizationPolicy;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.search.strategy.strategy.AbstractStrategy;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
  //TODO:Should this be here? An ordered List of Enum values is required for their mapping to ints
  private Map<String, List<String>> orderedEnumTypes = new HashMap<>();
  private Map<String, TypeEnum> enumTypes = new HashMap<>();

  public static int MAX_BOUND = 32767;
  public static int MIN_BOUND = -32768;

  public ChocoModel(String name) {
    model = new Model(name);
  }

  protected ArExpression addBool(String name) {
    if (bools.containsKey(name)) {
      return bools.get(name);
    }
    BoolVar bool = model.boolVar(name);
    bools.put(name, bool);
    return bool;
  }

  protected ArExpression addInt(String name) {
    if (ints.containsKey(name)) {
      return ints.get(name);
    }
    IntVar integ = model.intVar(name, MIN_BOUND, MAX_BOUND);
    ints.put(name, integ);
    return integ;
  }

  protected ArExpression addEnum(String name, TypeEnum type) {
    //Add enum as int
    if (enums.containsKey(name)) {
      return enums.get(name);
    }
    orderedEnumTypes.put(
        type.getTypeName(), type.getValues().stream().map(ValueEnum::getEnumValue).collect(Collectors.toList())
    );
    enumTypes.put(name, type);
    IntVar integ = model.intVar(name, MIN_BOUND, MAX_BOUND);
    enums.put(name, integ);
    //Add constraints to int to be in range of its mapped values
    integ.ge(0).post();
    integ.lt(type.getValues().size()).post();
    return integ;
  }

  protected ArExpression addBoolLiteral(boolean value) {
    return model.boolVar(value);
  }

  protected ArExpression addIntLiteral(int value) {
    return model.intVar(value);
  }

  protected ArExpression addEnumLiteral(Type type, String enumValue) {
    return model.intVar(findIndexOfEnumValue(type, enumValue));
  }

  private int findIndexOfEnumValue(Type type, String enumValue){
    return orderedEnumTypes.get(type.getTypeName()).indexOf(enumValue);
  }

  public Optional<Map<String, Value>> solve() {

    model.clearObjective();

    List<IntVar> intVars = Stream.of(bools, ints, enums).flatMap(
        map -> map.values().stream()
    ).collect(Collectors.toList());
    //Sum of absolute values of all variables should be minimal to prevent high values
    ArExpression sumOfAbsolutes = intVars.stream()
        .map(ArExpression::abs)
        .reduce(ArExpression::add)
        .orElseThrow(() -> new IllegalStateException("Cold not build objective Expression"));
    model.setObjective(Model.MINIMIZE, sumOfAbsolutes.intVar());

    model.getSolver().reset();
    //Always choose the bound that minimizes the objective first
    ObjectiveStrategy objectiveStrategy = new ObjectiveStrategy(sumOfAbsolutes.intVar(), OptimizationPolicy.DICHOTOMIC);
    //AbstractStrategy strategy = Search.sequencer(Search.defaultSearch(model), objectiveStrategy);
    model.getSolver().setSearch(objectiveStrategy, Search.defaultSearch(model));
    //improves solution (if existent) in every iteration
    Solution solution = new Solution(model);
    while (model.getSolver().solve()) {
      solution.record();
    }
    if (model.getSolver().isFeasible() == ESat.TRUE) {
      return Optional.of(buildSolution(solution));
    } else {
      return Optional.empty();
    }
  }

  public void clearAssignment() {
    assignment.forEach(constraint -> model.unpost(constraint));
    assignment.clear();
  }

  public Optional<Map<String, Value>> solve(Map<String, Value> values) {
    //Clears previous assignment
    clearAssignment();
    //Posts a new constraint to set each variable in the map to a specific value
    values.entrySet().forEach(entry -> {
      Optional<Constraint> optionalConstraint = entry.getValue().match(
          integer -> {
            if (ints.containsKey(entry.getKey())) {
              Constraint constraint = ints.get(entry.getKey()).eq(integer).decompose();
              return Optional.of(constraint);
            }
            return Optional.empty();
          },
          bool -> {
            if (ints.containsKey(entry.getKey())) {
              Constraint constraint = ints.get(entry.getKey()).eq(bool ? 1 : 0).decompose();
              return Optional.of(constraint);
            }
            return Optional.empty();
          },
          enumeration -> {
            if (enums.containsKey(entry.getKey())) {
              Constraint constraint = enums.get(entry.getKey()).eq(
                  findIndexOfEnumValue(enumeration.getType(), enumeration.getEnumValue())
              ).decompose();
              return Optional.of(constraint);
            }
            return Optional.empty();
          }
      );
      optionalConstraint.ifPresent(constraint -> {
        constraint.post();
        assignment.add(constraint);
      });
    });
    return solve();
  }

  private Map<String, Value> buildSolution(Solution solution) {
    Map<String, ValueBool> boolMap = bools.entrySet().stream()
        .collect(Collectors.toMap(
            Map.Entry::getKey,
            entry -> ValueBool.of(solution.getIntVal(entry.getValue()) == 1)
        ));
    Map<String, ValueInt> intMap = ints.entrySet().stream()
        .collect(Collectors.toMap(
            Map.Entry::getKey,
            entry -> new ValueInt(solution.getIntVal(entry.getValue()))
        ));
    Map<String, ValueEnum> enumMap = enums.entrySet().stream()
        .collect(Collectors.toMap(
            Map.Entry::getKey,
            entry ->{
              List<String> enumValues = orderedEnumTypes.get(
                  enumTypes.get(entry.getKey()).getTypeName()
              );
              String enumValueString = enumValues.get(solution.getIntVal(entry.getValue()));
              TypeEnum type = enumTypes.get(entry.getKey());
              return new ValueEnum(enumValueString, type);
            }
        ));
    Map<String, Value> builtSolution = new HashMap<>();
    builtSolution.putAll(boolMap);
    builtSolution.putAll(intMap);
    builtSolution.putAll(enumMap);
    return builtSolution;
  }

  protected Map<String, BoolVar> getBools() {
    return bools;
  }

  protected Map<String, IntVar> getInts() {
    return ints;
  }

  protected Map<String, IntVar> getEnums() {
    return enums;
  }

  public void init(Map<String, Type> typeContext) {
    typeContext.entrySet().forEach(entry -> {
      entry.getValue().match(
          () -> addInt(entry.getKey()),
          () -> addBool(entry.getKey()),
          (e) -> addEnum(entry.getKey(), e)
      );
    });
  }
}
