package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.Observable;
import javafx.beans.property.*;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Created by philipp on 09.02.17.
 *
 * @author Philipp
 */
public class FreeVariableListValidator {

  private final ObjectProperty<List<Type>> typeContext;
  private final FreeVariableList freeVariables;

  private final ObjectProperty<Map<FreeVariable, List<FreeVariableProblem>>> problems;
  private final ObjectProperty<List<ValidFreeVariable>> validVars;
  private final BooleanProperty valid;


  public FreeVariableListValidator(ObjectProperty<List<Type>> typeContext, FreeVariableList freeVariables) {
    this.typeContext = typeContext;
    this.freeVariables = freeVariables;

    this.problems = new SimpleObjectProperty<>(new HashMap<>());
    this.validVars = new SimpleObjectProperty<>(new ArrayList<>());
    this.valid = new SimpleBooleanProperty(false);

    freeVariables.getVariables().addListener((Observable o) -> revalidate());
    typeContext.addListener((Observable o) -> revalidate());
    revalidate();
  }

  public void revalidate() {
    Map<String, Type> typesByName = typeContext.get().stream()
        .collect(Collectors.toMap(Type::getTypeName, Function.identity()));

    Map<FreeVariable, List<FreeVariableProblem>> problems = new HashMap<>();

    List<ValidFreeVariable> validated = new ArrayList<>();

    freeVariables.getVariables().forEach(freeVariable -> {
      Optional<DuplicateFreeVariableProblem> optionalDuplicateProblem =
          DuplicateFreeVariableProblem.checkForDuplicates(freeVariable, freeVariables.getVariables());
      optionalDuplicateProblem.ifPresent(problem -> insertProblem(problems, freeVariable, problem));
      if (!optionalDuplicateProblem.isPresent()) {
        try {
          validated.add(InvalidFreeVariableProblem.tryToConvertToValid(freeVariable, typesByName));
        } catch (InvalidFreeVariableProblem problem) {
          insertProblem(problems, freeVariable, problem);
        }
      }
    });

    validVars.set(validated);
    this.problems.set(problems);
    valid.set(problems.size() == 0);
  }

  private <K, V> void insertProblem(Map<K, List<V>> map, K key, V item) {
    List<V> items = map.get(key);
    if (items == null) {
      List<V> newItemsList = new ArrayList<>();
      newItemsList.add(item);
      map.put(key, newItemsList);
    } else {
      items.add(item);
    }
  }

  public ReadOnlyBooleanProperty validProperty() {
    return valid;
  }

  public ReadOnlyObjectProperty<Map<FreeVariable, List<FreeVariableProblem>>> problemsProperty() {
    return problems;
  }

  public ReadOnlyObjectProperty<List<ValidFreeVariable>> validFreeVariablesProperty() {
    return validVars;
  }
}
