package edu.kit.iti.formal.stvs.model.table;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableSet;
import org.apache.commons.io.IOUtils;

import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 04.02.2017.
 */
public class TableUtil {

  public static final Gson GSON = new Gson();

  public static class JsonExpectedProblems {
    List<String> expected_problems;
  }

  public static class JsonFreeVarSet {
    public List<JsonFreeVar> freevariables;
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

  public static ConstraintSpecification constraintTableFromJson(
      ObjectProperty<List<Type>> typeContext,
      ObjectProperty<List<CodeIoVariable>> codeIoVars,
      JsonElement element) {
    FreeVariableSet freeVarSet = freeVariableSetFromJson(element);
    SpecificationTable<String, String> parsedTable = specificationTableFromJson(element);

    ConstraintSpecification spec = new ConstraintSpecification(typeContext, codeIoVars, freeVarSet);

    spec.getSpecIoVariables().addAll(parsedTable.getSpecIoVariables());

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

  public static FreeVariableSet freeVariableSetFromJson(JsonElement element) {
    FreeVariableSet freeVariableSet = new FreeVariableSet();
    GSON.fromJson(element, JsonFreeVarSet.class).freevariables.stream()
      .map(TableUtil::toFreeVariable)
    .forEach(freeVar -> freeVariableSet.getVariableSet().add(freeVar));

    return freeVariableSet;
  }

  private static FreeVariable toFreeVariable(JsonFreeVar jsonFreeVar) {
    return new FreeVariable(jsonFreeVar.name, typeFromString(jsonFreeVar.type));
  }

  public static SpecificationTable<String, String> specificationTableFromJson(JsonElement element) {
    return specificationTableFromJsonTable(GSON.fromJson(element, JsonTable.class));
  }

  private static SpecificationTable<String, String> specificationTableFromJsonTable(JsonTable table) {
    SpecificationTable<String, String> spec = new SpecificationTable<>(p -> new Observable[0]);
    table.variables.stream().map(TableUtil::toSpecIoVariable).forEach(r ->
        spec.getSpecIoVariables().add(r));

    table.rows.forEach(row ->
        spec.getRows().add(toSpecificationRow(row, spec.getSpecIoVariables())));

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
    return new SpecIoVariable(iovar.iotype, typeFromString(iovar.type), iovar.name);
  }

  private static Type typeFromString(String input) {
    switch (input) {
      case "INT": return TypeInt.INT;
      case "BOOL": return TypeBool.BOOL;
      default: return new TypeEnum(input, Collections.emptyList());
    }
  }
}
