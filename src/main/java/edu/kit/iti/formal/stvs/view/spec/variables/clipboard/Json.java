package edu.kit.iti.formal.stvs.view.spec.variables.clipboard;

import com.google.gson.Gson;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;

import java.util.List;
import java.util.stream.Collectors;

/**
 * This class handles the conversion from a lis of {@link FreeVariable} to JSON and vice versa.
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

  /**
   * Generates JSON from variables.
   * @param freeVariables variables to convert
   * @return Stringified JSON version of variables
   */
  public static String stringFromRealFreeVariables(List<FreeVariable> freeVariables) {
    return GSON.toJson(fromRealFreeVariables(freeVariables), FreeVarSelection.class);
  }

  /**
   * Generates variables from JSON.
   * @param input Stringified JSON version of variables
   * @return restored variables
   */
  public static List<FreeVariable> stringToRealFreeVariables(String input) {
    return toRealFreeVariables(GSON.fromJson(input, FreeVarSelection.class));
  }

  /**
   * Generates a stringifyable {@link FreeVarSelection} from a list of {@link FreeVariable}.
   * @param freeVariables variables to convert
   * @return converted selection
   */
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

  /**
   * Generates a list of {@link FreeVariable} from the stringifyable class {@link FreeVarSelection}.
   *
   * @param selection stringifyable selection
   * @return list of variables
   */
  public static List<FreeVariable> toRealFreeVariables(FreeVarSelection selection) {
    return selection.selected.stream()
        .map(freeVar -> new FreeVariable(freeVar.name, freeVar.type, freeVar.defaultval))
        .collect(Collectors.toList());
  }
}
