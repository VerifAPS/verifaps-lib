package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.util.AsyncTaskCompletedHandler;
import edu.kit.iti.formal.stvs.util.ProcessOutputAsyncTask;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * This class prepares a given SmtString to be solved with z3 and interprets the output.
 *
 * @author Leon Kaucher
 */
public class Z3Solver {

  private final int timeout;
  private String z3Path;

  /**
   * Creates an instance that can later be used for solving.
   *
   * @param config config that should be used for timeout and path to z3
   */
  public Z3Solver(GlobalConfig config) {
    this.z3Path = config.getZ3Path();
    this.timeout = config.getSimulationTimeout();
  }

  /**
   * Converts a {@link Sexp} (already parsed output of the solver)
   * to a {@link ConcreteSpecification}.
   *
   * @param sexpr            expression that should be converted
   * @param validIoVariables variables that were used in the specification
   *                         to resolve variables in the solver output
   * @return converted specification
   */
  private static ConcreteSpecification buildConcreteSpecFromSExp(
      Sexp sexpr,
      List<ValidIoVariable> validIoVariables
  ) {
    Map<Integer, Integer> rawDurations = extractRawDurations(sexpr);
    //convert raw durations into duration list
    List<ConcreteDuration> durations = buildConcreteDurations(rawDurations);
    Map<Integer, Map<String, String>> rawRows = extractRawRows(sexpr, durations);
    //convert raw rows into specificationRows
    List<SpecificationRow<ConcreteCell>> specificationRows =
        buildSpecificationRows(validIoVariables, durations, rawRows);
    return new ConcreteSpecification(validIoVariables, specificationRows, durations, false);
  }

  /**
   * Creates {@link SpecificationRow SpecificationRows} from raw rows.
   *
   * @param validIoVariables variables that might appear in the specification
   * @param durations        list of duration for each row
   * @param rawRows          Mapping from cycle number x variable name to cell expression as string
   * @return list of specification rows
   */
  private static List<SpecificationRow<ConcreteCell>> buildSpecificationRows(
      List<ValidIoVariable> validIoVariables,
      List<ConcreteDuration> durations,
      Map<Integer, Map<String, String>> rawRows) {
    List<SpecificationRow<ConcreteCell>> specificationRows = new ArrayList<>();
    durations.forEach(duration ->
        buildSpecificationRow(validIoVariables, rawRows, specificationRows, duration));
    return specificationRows;
  }

  /**
   * Adds {@link SpecificationRow SpecificationRows} to the map for one {@code duration}.
   * This will add a {@link SpecificationRow} for each cycle in the given duration.
   * This method uses {@code validIoVariables} to determine the {@link Type} of the variable
   * and convert the cell in the raw row accordingly.
   *
   * @param validIoVariables  variables that might appear in the specification
   * @param rawRows           Mapping from cycle number x variable name to cell expression as string
   * @param specificationRows map of specification rows (aggregator)
   * @param duration          duration containing multiple cycles
   */
  private static void buildSpecificationRow(
      List<ValidIoVariable> validIoVariables,
      Map<Integer, Map<String, String>> rawRows,
      List<SpecificationRow<ConcreteCell>> specificationRows,
      ConcreteDuration duration
  ) {
    for (int cycle = 0; cycle < duration.getDuration(); cycle++) {
      Map<String, String> rawRow = rawRows.get(duration.getBeginCycle() + cycle);
      Map<String, ConcreteCell> newRow = new HashMap<>();
      validIoVariables.forEach(validIoVariable -> {
        if (rawRow == null) {
          newRow.put(validIoVariable.getName(),
              new ConcreteCell(validIoVariable.getValidType().generateDefaultValue()));
          return;
        }
        String solvedValue = rawRow.get(validIoVariable.getName());
        if (solvedValue == null) {
          newRow.put(validIoVariable.getName(),
              new ConcreteCell(validIoVariable.getValidType().generateDefaultValue()));
          return;
        }
        Value value = validIoVariable.getValidType().match(
            () -> new ValueInt(BitvectorUtils.intFromHex(solvedValue, true)),
            () -> solvedValue.equals("true") ? ValueBool.TRUE : ValueBool.FALSE,
            typeEnum -> typeEnum.getValues().get(BitvectorUtils.intFromHex(solvedValue, false))
        );
        newRow.put(validIoVariable.getName(), new ConcreteCell(value));
      });
      specificationRows.add(SpecificationRow.createUnobservableRow(newRow));
    }
  }

  /**
   * Creates a list of concrete durations.
   *
   * @param rawDurations Mapping from row number to duration
   * @return list of concrete durations
   */
  private static List<ConcreteDuration> buildConcreteDurations(Map<Integer, Integer> rawDurations) {
    List<ConcreteDuration> durations = new ArrayList<>();
    int aggregator = 0;
    for (int i = 0; i < rawDurations.size(); i++) {
      Integer duration = rawDurations.get(i);
      durations.add(i, new ConcreteDuration(aggregator, duration));
      aggregator += duration;
    }
    return durations;
  }

  /**
   * Extracts a Mapping (cycle number x variable name to cell expression as string) from
   * parsed solver output.
   *
   * @param sexpr     parsed solver output
   * @param durations concrete durations for each row
   * @return mapping
   */
  private static Map<Integer, Map<String, String>> extractRawRows(
      Sexp sexpr,
      List<ConcreteDuration> durations
  ) {
    Map<Integer, Map<String, String>> rawRows = new HashMap<>();
    sexpr.forEach(varAsign -> addRowToMap(durations, rawRows, varAsign));
    return rawRows;
  }

  /**
   * Adds a raw row (mapping from cycle number x variable name to cell expression as string)
   * to the map for a given assignment from the solver that has the format
   * (define-fun VarName_row_cycle () SolverType SolverValue).
   *
   * @param durations list of concrete durations
   * @param rawRows   mapping from cycle number x variable name to cell expression as string
   * @param varAsign  solver assignment
   */
  private static void addRowToMap(
      List<ConcreteDuration> durations,
      Map<Integer, Map<String, String>> rawRows,
      Sexp varAsign
  ) {
    if (varAsign.getLength() == 0 || !varAsign.get(0).toIndentedString().equals("define-fun")) {
      return;
    }
    String[] varSplit = varAsign.get(1).toIndentedString().split("_");
    if (varAsign.get(1).toIndentedString().matches(".*?_\\d+_\\d+")) {
      //is variable
      int cycleCount = Integer.valueOf(varSplit[2]);
      //ignore variables if iteration > n_z
      int nz = Integer.valueOf(varSplit[1]);
      ConcreteDuration concreteDuration = durations.get(nz);
      if (cycleCount >= concreteDuration.getDuration()) {
        return;
      }
      int absoluteIndex = concreteDuration.getBeginCycle() + cycleCount;
      rawRows.putIfAbsent(absoluteIndex, new HashMap<>());
      rawRows.get(absoluteIndex).put(varSplit[0], varAsign.get(4).toIndentedString());
    }
  }

  /**
   * Extracts Durations from parsed solver output.
   * This is the foundation for building a {@link ConcreteSpecification}.
   * After the concrete durations are known, variables that depend on unrollings
   * can be extracted from solver output.
   *
   * @param sexpr parsed solver output
   * @return Map from row to duration
   */
  private static Map<Integer, Integer> extractRawDurations(Sexp sexpr) {
    Map<Integer, Integer> rawDurations = new HashMap<>();
    sexpr.forEach(varAsign -> addDurationToMap(rawDurations, varAsign));
    return rawDurations;
  }

  /**
   * Adds a duration from solver output to map if {@code varAsign} has the following format
   * (define-fun n_z () (_ BitVec 16) #xXXXX).
   *
   * @param rawDurations raw durations (mapping from ro to duration)
   * @param varAsign     solver assignment
   */
  private static void addDurationToMap(Map<Integer, Integer> rawDurations, Sexp varAsign) {
    if (varAsign.getLength() == 0 || !varAsign.get(0).toIndentedString().equals("define-fun")) {
      return;
    }
    String[] varSplit = varAsign.get(1).toIndentedString().split("_");
    if (varAsign.get(1).toIndentedString().matches("n_\\d+")) {
      //is duration
      rawDurations.put(Integer.valueOf(varSplit[1]),
          BitvectorUtils.intFromHex(varAsign.get(4).toIndentedString(), false));
    }
  }

  public String getZ3Path() {
    return z3Path;
  }

  public void setZ3Path(String z3Path) {
    this.z3Path = z3Path;
  }

  /**
   * Concretizes {@code smtString} using Z3 in an {@link edu.kit.iti.formal.stvs.util.AsyncTask}.
   * After the task has ended {@code handler} is called with the output string (if present).
   * Returns {@link ProcessOutputAsyncTask} to provide a possibility to terminate the Z3 process.
   *
   * @param smtString string to be solved
   * @param handler   handles the output string of the solver
   * @return task that can be terminated
   */
  private ProcessOutputAsyncTask concretize(
      String smtString,
      AsyncTaskCompletedHandler<Optional<String>> handler
  ) {
    ProcessBuilder processBuilder = new ProcessBuilder(z3Path, "-in", "-smt2", "-T:" + timeout);
    return new ProcessOutputAsyncTask(processBuilder, smtString, handler);
  }

  /**
   * Concretizes {@code smtString} using Z3 in an {@link edu.kit.iti.formal.stvs.util.AsyncTask}.
   * After the task has ended {@code handler} is called with a parsed {@link SExpr} (if present).
   * Returns {@link ProcessOutputAsyncTask} to provide a possibility to terminate the Z3 process.
   *
   * @param smtString string to be solved
   * @param handler   handles the expression that represents the solver output
   * @return task that can be terminated
   */
  private ProcessOutputAsyncTask concretizeSExpr(
      String smtString,
      Consumer<Optional<SExpr>> handler
  ) {
    return concretize(smtString, stringOptional ->
        handler.accept(optionalSolverOutputToSexp(stringOptional)));
  }

  /**
   * Concretizes {@code smtString} using Z3 in an {@link edu.kit.iti.formal.stvs.util.AsyncTask}.
   * After the task has ended {@code handler} is called with a
   * {@link ConcreteSpecification} (if present).
   * Returns {@link ProcessOutputAsyncTask} to provide a possibility to terminate the Z3 process.
   *
   * @param smtString        string to be solved
   * @param validIoVariables variables that might appear in the solver output
   * @param handler          handles the specification that represents the solver output
   * @return task that can be terminated
   */
  private ProcessOutputAsyncTask concretizeSmtString(
      String smtString,
      List<ValidIoVariable> validIoVariables,
      OptionalConcreteSpecificationHandler handler
  ) {
    return concretizeSExpr(smtString, sexpOptional ->
        handler.accept(optionalSpecFromOptionalSExp(validIoVariables, sexpOptional)));
  }

  /**
   * This method first generates a {@code smtString} from {@link SConstraint} and adds commands
   * to tell Z3 to solve the model.
   *
   * @param sconstraint      constraint hat holds all information to generate a smtString
   * @param validIoVariables variables that might appear in the solver output
   * @param handler          handles the specification that represents the solver output
   * @return task that can be terminated
   * @see Z3Solver#concretizeSmtString(String, List, OptionalConcreteSpecificationHandler)
   */
  public ProcessOutputAsyncTask concretizeSConstraint(
      SConstraint sconstraint,
      List<ValidIoVariable> validIoVariables,
      OptionalConcreteSpecificationHandler handler
  ) {
    String constraintString = sconstraint.globalConstraintsToText();
    String headerString = sconstraint.headerToText();
    String commands = "(check-sat)\n(get-model)";
    String z3Input = headerString + "\n" + constraintString + "\n" + commands;
    return concretizeSmtString(z3Input, validIoVariables, handler);
  }

  private Optional<SExpr> optionalSolverOutputToSexp(Optional<String> stringOptional) {
    if (stringOptional.isPresent() && stringOptional.get().startsWith("sat")) {
      String output = stringOptional.get();
      output = output.substring(output.indexOf('\n') + 1);
      return (Optional.of(SExpr.fromString(output)));
    }
    return Optional.empty();
  }

  private Optional<ConcreteSpecification> optionalSpecFromOptionalSExp(
      List<ValidIoVariable> validIoVariables,
      Optional<SExpr> sexpOptional
  ) {
    if (sexpOptional.isPresent()) {
      return Optional.of(buildConcreteSpecFromSExp(sexpOptional.get().toSexpr(), validIoVariables));
    }
    return Optional.empty();
  }
}
