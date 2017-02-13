package edu.kit.iti.formal.stvs.model.table;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.problems.InvalidIoVarProblem;
import edu.kit.iti.formal.stvs.util.MapUtil;
import javafx.beans.Observable;
import org.apache.commons.io.IOUtils;

import java.io.IOException;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 04.02.2017.
 */
public class JsonTableParser {

  public static final Gson GSON = new Gson();

  public static class JsonExpectedProblems {
    List<String> expected_problems;
  }

  public static class JsonFreeVarSet {
    public List<JsonFreeVar> freevariables;
  }

  public static class JsonCodeIoVar {
    public String name;
    public String type;
    public String kind;
  }

  public static class JsonCodeIoVars {
    public List<JsonCodeIoVar> codeiovars;
  }

  public static class JsonFreeVar {
    public String name;
    public String type;
  }

  public static class JsonTable {
    public List<JsonIoVariable> variables;
    public List<String> rows;
    public List<String> durations;
  }

  public static class JsonIoVariable {
    public VariableCategory iotype;
    public String name;
    public String type;
  }

  public static JsonElement jsonFromResource(String resource, Class<?> clazz) {
    return GSON.fromJson(stringFromResource(resource, clazz), JsonElement.class);
  }

  public static String stringFromResource(String resource, Class<?> clazz) {
    try {
      return IOUtils.toString(clazz.getResourceAsStream(resource), "UTF-8");
    } catch (IOException cause) {
      throw new RuntimeException(cause);
    }
  }

  public static List<Class<?>> expectedSpecProblemsFromJson(JsonElement elem) {
    JsonExpectedProblems expectedProblems = GSON.fromJson(elem, JsonExpectedProblems.class);
    return expectedProblems.expected_problems.stream()
        .map(s -> {
          try {
            return Class.forName("edu.kit.iti.formal.stvs.model.table.problems." + s);
          } catch (ClassNotFoundException e) {
            throw new RuntimeException(e);
          }
        })
        .collect(Collectors.toList());
  }

  public static List<CodeIoVariable> codeIoVariablesFromJson(JsonElement elem) {
    JsonCodeIoVars ioVars = GSON.fromJson(elem, JsonCodeIoVars.class);
    return ioVars.codeiovars.stream()
        .map(ioVar -> new CodeIoVariable(VariableCategory.valueOf(ioVar.kind), ioVar.type, ioVar.name))
        .collect(Collectors.toList());
  }

  public static ConcreteSpecification concreteTableFromJson(List<Type> types, boolean isCounterExample, JsonElement element) {
    SpecificationTable<SpecIoVariable, String, String> parsedTable = specificationTableFromJson(element);

    ConcreteSpecification concreteSpec = new ConcreteSpecification(isCounterExample);

    List<Type> typeContext = new ArrayList<>();
    typeContext.add(TypeInt.INT);
    typeContext.add(TypeBool.BOOL);
    typeContext.addAll(types);
    Map<String, Type> typesByName = typeContext.stream()
        .collect(Collectors.toMap(Type::getTypeName, Function.identity()));

    for (SpecIoVariable specIoVariable : parsedTable.getColumnHeaders()) {
      try {
        ValidIoVariable validIoVariable = InvalidIoVarProblem.tryGetValidIoVariable(
            specIoVariable,
            Collections.emptyList(),
            typesByName,
            problem -> {} // ignore insignificant problems
        );
        concreteSpec.getColumnHeaders().add(validIoVariable);
      } catch (InvalidIoVarProblem problem) {
        throw new RuntimeException(problem);
      }
    }

    for (int rowIndex = 0; rowIndex < parsedTable.getRows().size(); rowIndex++) {
      SpecificationRow<String> row = parsedTable.getRows().get(rowIndex);
      Map<String, ConcreteCell> cells = MapUtil.mapValuesWithKey(row.getCells(),
          (columnId, cellString) -> new ConcreteCell(
              concreteSpec.getColumnHeaderByName(columnId).getValidType().parseLiteral(cellString.trim())
          .orElseThrow(() -> new RuntimeException("Couldnt parse: "
              + cellString + " of type "
              + concreteSpec.getColumnHeaderByName(columnId).getValidType().getTypeName()
              + " in column " + columnId))));
      concreteSpec.getRows().add(SpecificationRow.createUnobservableRow(cells));
    }

    int beginCycle = 0;
    for (String durString : parsedTable.getDurations()) {
      int duration = Integer.parseInt(durString);
      concreteSpec.getDurations().add(new ConcreteDuration(beginCycle, duration));
      beginCycle += duration;
    }

    return concreteSpec;
  }

  public static ConstraintSpecification constraintTableFromJson(JsonElement element) {
    FreeVariableList freeVarSet = freeVariableSetFromJson(element);
    SpecificationTable<SpecIoVariable, String, String> parsedTable = specificationTableFromJson(element);

    ConstraintSpecification spec = new ConstraintSpecification(freeVarSet);

    spec.getColumnHeaders().addAll(parsedTable.getColumnHeaders());

    for (SpecificationRow<String> row : parsedTable.getRows()) {
      Map<String, ConstraintCell> cells = new HashMap<>();

      row.getCells().forEach((columnId, cellString) ->
        cells.put(columnId, new ConstraintCell(cellString)));

      spec.getRows().add(ConstraintSpecification.createRow(cells));
    }

    spec.getDurations().addAll(
        parsedTable.getDurations().stream()
            .map(ConstraintDuration::new)
            .collect(Collectors.toList()));

    return spec;
  }

  public static FreeVariableList freeVariableSetFromJson(JsonElement element) {
    FreeVariableList freeVariableList = new FreeVariableList(new ArrayList<>());
    GSON.fromJson(element, JsonFreeVarSet.class).freevariables.stream()
      .map(JsonTableParser::toFreeVariable)
    .forEach(freeVar -> freeVariableList.getVariables().add(freeVar));

    return freeVariableList;
  }

  private static FreeVariable toFreeVariable(JsonFreeVar jsonFreeVar) {
    return new FreeVariable(jsonFreeVar.name, jsonFreeVar.type);
  }

  public static SpecificationTable<SpecIoVariable, String, String> specificationTableFromJson(JsonElement element) {
    return specificationTableFromJsonTable(GSON.fromJson(element, JsonTable.class));
  }

  private static SpecificationTable<SpecIoVariable, String, String> specificationTableFromJsonTable(JsonTable table) {
    SpecificationTable<SpecIoVariable, String, String> spec = new SpecificationTable<>(p -> new Observable[0], p -> new Observable[0]);
    table.variables.stream().map(JsonTableParser::toSpecIoVariable).forEach(r ->
        spec.getColumnHeaders().add(r));

    table.rows.forEach(row ->
        spec.getRows().add(toSpecificationRow(row, spec.getColumnHeaders())));

    spec.getDurations().addAll(table.durations);
    return spec;
  }

  private static SpecificationRow<String> toSpecificationRow(String s, List<SpecIoVariable> ioVars) {
    String[] split = s.split("\\s*\\|\\s*");
    Map<String, String> elems = new HashMap<>();
    for (int i = 0; i < split.length; i++) {
      elems.put(ioVars.get(i).getName(), split[i]);
    }
    return SpecificationRow.createUnobservableRow(elems);
  }

  private static SpecIoVariable toSpecIoVariable(JsonIoVariable iovar) {
    return new SpecIoVariable(iovar.iotype, iovar.type, iovar.name);
  }

  private static Type typeFromString(String input) {
    switch (input) {
      case "INT": return TypeInt.INT;
      case "BOOL": return TypeBool.BOOL;
      default: return new TypeEnum(input, Collections.emptyList());
    }
  }
}
