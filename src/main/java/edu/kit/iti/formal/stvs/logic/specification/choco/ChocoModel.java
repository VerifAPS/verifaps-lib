package edu.kit.iti.formal.stvs.logic.specification.choco;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

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
    IntVar integ = model.intVar(name, IntVar.MIN_INT_BOUND, IntVar.MAX_INT_BOUND);
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
    IntVar integ = model.intVar(name, IntVar.MIN_INT_BOUND, IntVar.MAX_INT_BOUND);
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

  public Optional<ConcreteSolution> solve() {
    model.getSolver().reset();
    boolean solved = model.getSolver().solve();
    if (solved) {
      return Optional.of(buildSolution());
    } else {
      return Optional.empty();
    }
  }

  public void clearAssignment() {
    assignment.forEach(constraint -> model.unpost(constraint));
    assignment.clear();
  }

  public Optional<ConcreteSolution> solve(Map<String, Value> values) {
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

  private ConcreteSolution buildSolution() {
    Map<String, ValueBool> boolMap = bools.entrySet().stream()
        .collect(Collectors.toMap(
            entry -> entry.getKey(),
            entry -> ValueBool.of(entry.getValue().getValue() == 1)
        ));
    Map<String, ValueInt> intMap = ints.entrySet().stream()
        .collect(Collectors.toMap(
            entry -> entry.getKey(),
            entry -> new ValueInt(entry.getValue().getValue())
        ));
    Map<String, ValueEnum> enumMap = enums.entrySet().stream()
        .collect(Collectors.toMap(
            entry -> entry.getKey(),
            entry ->{
              List<String> enumValues = orderedEnumTypes.get(
                  enumTypes.get(entry.getKey()).getTypeName()
              );
              String enumValueString = enumValues.get(entry.getValue().getValue());
              TypeEnum type = enumTypes.get(entry.getKey());
              return new ValueEnum(enumValueString, type);
            }
        ));
    return new ConcreteSolution(intMap, boolMap, enumMap);
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
