package edu.kit.iti.formal.stvs.view.spec.variables.clipboard;

import com.google.gson.Gson;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import org.apache.commons.lang3.StringEscapeUtils;

import java.lang.management.ManagementFactory;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 05.02.2017.
 */
public class Json {

  private static final Gson GSON = new Gson();

  private Json() {
  }

  public static class FreeVarSelection {
    public List<FreeVar> selected;
    public String source =
        ManagementFactory.getRuntimeMXBean().getName();
  }

  public static class FreeVar {
    public String name;
    public String type;
  }

  public static String stringFromRealFreeVariables(List<FreeVariable> freeVariables) {
    return GSON.toJson(fromRealFreeVariables(freeVariables), FreeVarSelection.class);
  }

  public static List<FreeVariable> stringToRealFreeVariables(
      Collection<Type> typeContext, String input) {
    return toRealFreeVariables(typeContext, GSON.fromJson(input, FreeVarSelection.class));
  }

  public static String stringToSource(String input) {
    return GSON.fromJson(input, FreeVarSelection.class).source;
  }

  public static FreeVarSelection fromRealFreeVariables(List<FreeVariable> freeVariables) {
    List<FreeVar> vars = freeVariables.stream()
        .map(freeVariable -> {
          FreeVar var = new FreeVar();
          var.name = freeVariable.getName();
          var.type = freeVariable.getType().getTypeName();
          return var;
        })
        .collect(Collectors.toList());
    FreeVarSelection selection = new FreeVarSelection();
    selection.selected = vars;
    return selection;
  }

  public static List<FreeVariable> toRealFreeVariables(Collection<Type> typeContext, FreeVarSelection selection)
      throws IllegalArgumentException {
    return selection.selected.stream()
        .map(freeVar -> new FreeVariable(freeVar.name, typeFromString(typeContext, freeVar.type)))
        .collect(Collectors.toList());
  }

  public static Type typeFromString(Collection<Type> typeContext, String typeString)
      throws IllegalArgumentException {
    return typeContext.stream()
        .filter(type -> type.getTypeName().equals(typeString))
        .findAny()
        .orElseThrow(() ->
            new IllegalArgumentException("Can't paste free variable with unkown type: "
              + StringEscapeUtils.escapeJava(typeString)));
  }
}
