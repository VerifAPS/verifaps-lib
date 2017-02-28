package edu.kit.iti.formal.stvs.view.spec.variables.clipboard;

import com.google.gson.Gson;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 05.02.2017.
 *
 * @author Philipp
 */
public class Json {
  private static final Gson GSON = new Gson();

  private Json() {}

  public static class FreeVarSelection {
    public List<FreeVar> selected;
  }

  public static class FreeVar {
    public String name;
    public String type;
    public String defaultval;
  }

  public static String stringFromRealFreeVariables(List<FreeVariable> freeVariables) {
    return GSON.toJson(fromRealFreeVariables(freeVariables), FreeVarSelection.class);
  }

  public static List<FreeVariable> stringToRealFreeVariables(String input) {
    return toRealFreeVariables(GSON.fromJson(input, FreeVarSelection.class));
  }

  public static FreeVarSelection fromRealFreeVariables(List<FreeVariable> freeVariables) {
    List<FreeVar> vars = freeVariables.stream().map(freeVariable -> {
      FreeVar var = new FreeVar();
      var.name = freeVariable.getName();
      var.type = freeVariable.getType();
      var.defaultval = freeVariable.getDefaultValue();
      return var;
    }).collect(Collectors.toList());
    FreeVarSelection selection = new FreeVarSelection();
    selection.selected = vars;
    return selection;
  }

  public static List<FreeVariable> toRealFreeVariables(FreeVarSelection selection)
      throws IllegalArgumentException {
    return selection.selected.stream()
        .map(freeVar -> new FreeVariable(freeVar.name, freeVar.type, freeVar.defaultval))
        .collect(Collectors.toList());
  }
}
