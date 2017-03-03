package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import de.tudresden.inf.lat.jsexp.SexpParserException;
import edu.kit.iti.formal.stvs.logic.specification.ConcretizationException;
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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.io.IOUtils;

/**
 * This class prepares a given SmtString to be solved with z3 and interprets the output.
 *
 * @author Leon Kaucher
 */
public class Z3Solver {

  private static final Pattern VAR_PATTERN =
      Pattern.compile("(?<name>[$a-zA-Z0-9_]+)_(?<row>\\d+)_(?<cycle>\\d+)");
  private static final Pattern DURATION_PATTERN = Pattern.compile("n_(?<cycleCount>\\d+)");
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
   * Converts a {@link Sexp} (already parsed output of the solver) to a
   * {@link ConcreteSpecification}.
   *
   * @param sexpr expression that should be converted
   * @param validIoVariables variables that were used in the specification to resolve variables in
   *        the solver output
   * @return converted specification
   */
  private static ConcreteSpecification buildConcreteSpecFromSExp(Sexp sexpr,
      List<ValidIoVariable> validIoVariables) {
    Map<Integer, Integer> rawDurations = extractRawDurations(sexpr);
    // convert raw durations into duration list
    List<ConcreteDuration> durations = buildConcreteDurations(rawDurations);
    Map<Integer, Map<String, String>> rawRows = extractRawRows(sexpr, durations);
    // convert raw rows into specificationRows
    List<SpecificationRow<ConcreteCell>> specificationRows =
        buildSpecificationRows(validIoVariables, durations, rawRows);
    return new ConcreteSpecification(validIoVariables, specificationRows, durations, false);
  }

  /**
   * Creates {@link SpecificationRow SpecificationRows} from raw rows.
   *
   * @param validIoVariables variables that might appear in the specification
   * @param durations list of duration for each row
   * @param rawRows Mapping from cycle number x variable name to cell expression as string
   * @return list of specification rows
   */
  private static List<SpecificationRow<ConcreteCell>> buildSpecificationRows(
      List<ValidIoVariable> validIoVariables, List<ConcreteDuration> durations,
      Map<Integer, Map<String, String>> rawRows) {
    List<SpecificationRow<ConcreteCell>> specificationRows = new ArrayList<>();
    durations.forEach(
        duration -> buildSpecificationRow(validIoVariables, rawRows, specificationRows, duration));
    return specificationRows;
  }

  /**
   * Adds {@link SpecificationRow SpecificationRows} to the map for one {@code duration}. This will
   * add a {@link SpecificationRow} for each cycle in the given duration. This method uses
   * {@code validIoVariables} to determine the {@link Type} of the variable and convert the cell in
   * the raw row accordingly.
   *
   * @param validIoVariables variables that might appear in the specification
   * @param rawRows Mapping from cycle number x variable name to cell expression as string
   * @param specificationRows map of specification rows (aggregator)
   * @param duration duration containing multiple cycles
   */
  private static void buildSpecificationRow(List<ValidIoVariable> validIoVariables,
      Map<Integer, Map<String, String>> rawRows,
      List<SpecificationRow<ConcreteCell>> specificationRows, ConcreteDuration duration) {
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
            typeEnum -> typeEnum.getValues().get(BitvectorUtils.intFromHex(solvedValue, false)));
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
   * Extracts a Mapping (cycle number x variable name to cell expression as string) from parsed
   * solver output.
   *
   * @param sexpr parsed solver output
   * @param durations concrete durations for each row
   * @return mapping
   */
  private static Map<Integer, Map<String, String>> extractRawRows(Sexp sexpr,
      List<ConcreteDuration> durations) {
    Map<Integer, Map<String, String>> rawRows = new HashMap<>();
    sexpr.forEach(varAssign -> addRowToMap(durations, rawRows, varAssign));
    return rawRows;
  }

  /**
   * Adds a raw row (mapping from cycle number x variable name to cell expression as string) to the
   * map for a given assignment from the solver that has the format (define-fun VarName_row_cycle ()
   * SolverType SolverValue).
   *
   * @param durations list of concrete durations
   * @param rawRows mapping from cycle number x variable name to cell expression as string
   * @param varAssign solver assignment
   */
  private static void addRowToMap(List<ConcreteDuration> durations,
      Map<Integer, Map<String, String>> rawRows, Sexp varAssign) {
    if (varAssign.getLength() == 0 || !varAssign.get(0).toIndentedString().equals("define-fun")) {
      return;
    }
    Matcher identifierMatcher = VAR_PATTERN.matcher(varAssign.get(1).toIndentedString());
    if (identifierMatcher.matches()) {
      String varName = identifierMatcher.group("name");
      String row = identifierMatcher.group("row");
      String cycle = identifierMatcher.group("cycle");
      // is variable
      int cycleCount = Integer.valueOf(cycle);
      // ignore variables if iteration > n_z
      int nz = Integer.valueOf(row);
      ConcreteDuration concreteDuration = durations.get(nz);
      if (cycleCount >= concreteDuration.getDuration()) {
        return;
      }
      int absoluteIndex = concreteDuration.getBeginCycle() + cycleCount;
      rawRows.putIfAbsent(absoluteIndex, new HashMap<>());
      rawRows.get(absoluteIndex).put(varName, varAssign.get(4).toIndentedString());
    }
  }

  /**
   * Extracts Durations from parsed solver output. This is the foundation for building a
   * {@link ConcreteSpecification}. After the concrete durations are known, variables that depend on
   * unrollings can be extracted from solver output.
   *
   * @param sexpr parsed solver output
   * @return Map from row to duration
   */
  private static Map<Integer, Integer> extractRawDurations(Sexp sexpr) {
    Map<Integer, Integer> rawDurations = new HashMap<>();
    sexpr.forEach(varAssign -> addDurationToMap(rawDurations, varAssign));
    return rawDurations;
  }

  /**
   * Adds a duration from solver output to map if {@code varAssign} has the following format
   * (define-fun n_z () (_ BitVec 16) #xXXXX).
   *
   * @param rawDurations raw durations (mapping from ro to duration)
   * @param varAssign solver assignment
   */
  private static void addDurationToMap(Map<Integer, Integer> rawDurations, Sexp varAssign) {
    if (varAssign.getLength() == 0 || !varAssign.get(0).toIndentedString().equals("define-fun")) {
      return;
    }
    Matcher durationMatcher = DURATION_PATTERN.matcher(varAssign.get(1).toIndentedString());
    if (durationMatcher.matches()) {
      // is duration
      int cycleCount = Integer.parseInt(durationMatcher.group("cycleCount"));
      rawDurations.put(cycleCount,
          BitvectorUtils.intFromHex(varAssign.get(4).toIndentedString(), false));
    }
  }

  public String getZ3Path() {
    return z3Path;
  }

  public void setZ3Path(String z3Path) {
    this.z3Path = z3Path;
  }

  /**
   * Concretizes {@code smtString} using Z3. After the concretization has ended a
   * {@link ConcreteSpecification} is returned. If the timeout is reached before the z3 process has
   * terminated, an Exception is thrown.
   *
   * @param smtString string to be solved
   * @param ioVariables list of {@link ValidIoVariable} used in the specification.
   * @return concretized concrete specification
   * @throws ConcretizationException general concretization problem.
   */
  private ConcreteSpecification concretize(String smtString, List<ValidIoVariable> ioVariables)
      throws ConcretizationException {
    ProcessBuilder processBuilder = new ProcessBuilder(z3Path, "-in", "-smt2");
    AtomicBoolean wasAborted = new AtomicBoolean(false);
    try {
      Process process = processBuilder.start();
      IOUtils.write(smtString, process.getOutputStream(), "utf-8");
      process.getOutputStream().close();
      /*
       * Cannot be used due to buffering problems.
       * 
       * boolean wasAborted = !process.waitFor(timeout, TimeUnit.SECONDS);
       * 
       * if (wasAborted) { process.destroy(); throw new ConcretizationException( "Timeout (" +
       * timeout + "s)" + "reached before concretization ended."); } String z3Result =
       * IOUtils.toString(process.getInputStream(), "utf-8");
       */
      Timer processKillerTimer = new Timer();
      TimerTask processKiller = new TimerTask() {
        @Override
        public void run() {
          try {
            process.getInputStream().close();
          } catch (IOException e) {
            e.printStackTrace();
          }
          wasAborted.set(true);
        }
      };
      processKillerTimer.schedule(processKiller, 1000 * timeout);
      final BufferedReader reader =
          new BufferedReader(new InputStreamReader(process.getInputStream()));
      String line;
      String z3Result = "";
      while ((line = reader.readLine()) != null && !Thread.currentThread().isInterrupted()) {
        z3Result += line + "\n";
      }
      processKillerTimer.cancel();
      processKillerTimer.purge();
      Sexp expression = solverStringToSexp(z3Result);
      return buildConcreteSpecFromSExp(expression, ioVariables);

    } catch (IOException e) {
      if (wasAborted.get()) {
        throw new ConcretizationException("Timeout (" + timeout + "s) reached for concretization!");
      }
      throw new ConcretizationException(e);
    } catch (SexpParserException e) {
      throw new ConcretizationException(e);
    }
  }

  /**
   * This method first generates a {@code smtString} from {@link SmtModel} and adds commands to tell
   * Z3 to solve the model. Then it calls {@link Z3Solver#concretize(String, List)}.
   *
   * @param smtModel constraint hat holds all information to generate a smtString
   * @param validIoVariables variables that might appear in the solver output
   * @return concretized concrete specification
   * @see Z3Solver#concretize(String, List)
   * @throws ConcretizationException general concretization problem
   */
  public ConcreteSpecification concretizeSmtModel(SmtModel smtModel,
      List<ValidIoVariable> validIoVariables) throws ConcretizationException {
    String constraintString = smtModel.globalConstraintsToText();
    String headerString = smtModel.headerToText();
    String commands = "(check-sat)\n(get-model)\n(exit)";
    String z3Input = headerString + "\n" + constraintString + "\n" + commands;
    return concretize(z3Input, validIoVariables);
  }

  private Sexp solverStringToSexp(String z3String)
      throws ConcretizationException, SexpParserException {
    if (!z3String.startsWith("sat")) {
      throw new ConcretizationException("Solver returned status: Unsatisfiable");
    }
    z3String = z3String.substring(z3String.indexOf('\n') + 1);
    return (SexpFactory.parse(z3String));
  }
}
