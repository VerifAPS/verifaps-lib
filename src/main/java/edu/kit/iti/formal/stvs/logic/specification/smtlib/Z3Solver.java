package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.util.ProcessOutputHandler;

import java.io.IOException;
import java.io.PrintStream;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Created by leonk on 09.02.2017.
 */
public class Z3Solver {
  //TODO: Better way to call z3 than forcing it to be in PATH
  private static String z3PATH = "z3";

  public static Optional<String> concretize(String smtString) throws IOException {
    Process process = new ProcessBuilder(z3PATH, "-in").start();
    PrintStream printStream = new PrintStream(process.getOutputStream());
    printStream.print(smtString);
    printStream.close();
    return ProcessOutputHandler.handle(process);
  }

  public static Optional<SExpr> concretizeSExpr(String smtString) throws IOException {
    Optional<String> stringOptional = concretize(smtString);
    if (stringOptional.isPresent()) {
      String output = stringOptional.get();
      if (output.startsWith("sat")) {
        output = output.substring(output.indexOf('\n') + 1);
        return Optional.of(SExpr.fromString(output));
      }
    }
    return Optional.empty();
  }

  /*
    expects a smt string with get-value for each variable at the end
    e.g.
    (declare-const A_0_0 Int)
    (declare-const B_0_0 Int)
    (assert (= A_0_0 10))
    (check-sat)
    (get-value (A_0_0 B_0_0))
   */
  public static Optional<ConcreteSpecification> concretizeVarAssignment(String smtString, List<ValidIoVariable> validIoVariables)
      throws IOException {
    Optional<SExpr> sexpOptional = concretizeSExpr(smtString);
    Map<Integer, Map<String, String>> rawRows = new HashMap<>();
    Map<Integer, Integer> rawDurations = new HashMap<>();
    Map<String, Type> typeContext = validIoVariables.stream().collect(Collectors.toMap(
        ValidIoVariable::getName, ValidIoVariable::getValidType
    ));
    if (sexpOptional.isPresent()) {
      Sexp sExpr = sexpOptional.get().toSexpr();
      sExpr.forEach(varAsign -> {
        String[] varSplit = varAsign.get(0).toIndentedString().split("_");
        if (varAsign.get(0).toIndentedString().matches("n_\\d+")) {
          //is duration
          rawDurations.put(Integer.valueOf(varSplit[1]), Integer.valueOf(varAsign.get(1).toIndentedString()));
        }
      });

      //convert raw durations into duration list
      List<ConcreteDuration> durations = new ArrayList<>();
      int aggregator = 0;
      for (int i = 0; i < rawDurations.size(); i++) {
        Integer duration = rawDurations.get(i);
        durations.add(i, new ConcreteDuration(aggregator, duration));
        aggregator += duration;
      }

      sExpr.forEach(varAsign -> {
        String[] varSplit = varAsign.get(0).toIndentedString().split("_");
        if (varAsign.get(0).toIndentedString().matches(".*?_\\d+_\\d+")) {
          //is variable
          int rowNumber = Integer.valueOf(varSplit[1]) + Integer.valueOf(varSplit[2]);
          //ignore variables if iteration > n_z
          if (rowNumber > durations.get(Integer.valueOf(varSplit[1])).getEndCycle()) {
            return;
          }
          rawRows.putIfAbsent(rowNumber, new HashMap<>());
          rawRows.get(rowNumber).put(varSplit[0], varAsign.get(1).toIndentedString());
        }
      });

      //convert raw rows into specificationRows
      List<SpecificationRow<ConcreteCell>> specificationRows = new ArrayList<>();
      for (int i = 0; i < rawRows.size(); i++) {
        Map<String, ConcreteCell> concreteCellMap = rawRows.get(i).entrySet().stream()
            .map(rowEntry -> {
              String varName = rowEntry.getKey();
              String valueString = rowEntry.getValue();
              Type type = typeContext.get(varName);
              Value value = type.match(
                  () -> new ValueInt(Integer.valueOf(valueString)), //Integer
                  () -> valueString.equals("true") ? ValueBool.TRUE : ValueBool.FALSE, //Boolean
                  (typeEnum) -> typeEnum.valueOf(valueString) //Enum TODO: Check if this is correct
              );
              return new AbstractMap.SimpleEntry<>(varName, new ConcreteCell(value));
            })
            .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
        specificationRows.add(i, SpecificationRow.createUnobservableRow(concreteCellMap));
      }
       return Optional.of(
          new ConcreteSpecification(validIoVariables, specificationRows, durations, false));
    }
    return Optional.empty();
  }
}
