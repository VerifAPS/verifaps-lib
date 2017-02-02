package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import org.junit.Before;

import java.util.*;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 */
public class HybridSpecificationTest {
/*
  private HybridSpecification hybridSpec;
  private ValidSpecification validSpec;

  @Before
  public void setUp() throws IllegalValueTypeException {
    HashMap<String, SpecificationColumn<ConstraintCell>> columns = new HashMap<>();
    List<ConstraintCell> cellsA = Arrays.asList(new ConstraintCell("-"), new ConstraintCell("3"), new ConstraintCell("<5"));
    List<ConstraintCell> cellsB = Arrays.asList(new ConstraintCell("<3+2"), new ConstraintCell("2"), new ConstraintCell("-"));
    List<ConstraintCell> cellsC = Arrays.asList(new ConstraintCell("-"), new ConstraintCell("3"), new ConstraintCell("<5"));
    List<ConstraintCell> cellsD = Arrays.asList(new ConstraintCell("-"), new ConstraintCell("<=2"), new ConstraintCell("20"));
    SpecIoVariable variableA = new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA");
    SpecIoVariable variableB = new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB");
    SpecIoVariable variableC = new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableC");
    SpecIoVariable variableD = new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableD");
    columns.put("VariableA", new SpecificationColumn<>(variableA, cellsA, new ColumnConfig()));
    columns.put("VariableB", new SpecificationColumn<>(variableB, cellsB, new ColumnConfig(20)));
    columns.put("VariableC", new SpecificationColumn<>(variableC, cellsC, new ColumnConfig()));
    columns.put("VariableD", new SpecificationColumn<>(variableD, cellsD, new ColumnConfig(55)));
    List<ConstraintDuration> durations = Arrays.asList(new ConstraintDuration("1"),
        new ConstraintDuration("4"), new ConstraintDuration("5"));

    Set<Type> typeContext = new HashSet<Type>();
    typeContext.add(TypeInt.INT);
    typeContext.add(TypeBool.BOOL);

    List<FreeVariable> freeVariables = Arrays.asList(new FreeVariable("p", TypeInt.INT, new ValueInt(3)),
        new FreeVariable("q", TypeInt.INT, new ValueInt(5)));
    FreeVariableSet freeVariableSet = new FreeVariableSet(freeVariables);

    Set<CodeIoVariable> codeIoVariables = new HashSet<>();
    codeIoVariables.add(new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"));
    codeIoVariables.add(new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB"));
    codeIoVariables.add(new CodeIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableC"));
    codeIoVariables.add(new CodeIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableD"));
    hybridSpec = new HybridSpecification(columns, durations, typeContext, codeIoVariables, freeVariableSet, true);
    validSpec = hybridSpec.getValidSpecification();
    setValidSpecListener(hybridSpec);

    List<ConcreteCell> concreteCellsA = Arrays.asList(new ConcreteCell(new ValueInt(3)), new ConcreteCell(new ValueInt(2)), new ConcreteCell(new ValueInt(4)), new ConcreteCell(new ValueInt(5)));
    List<ConcreteCell> concreteCellsB = Arrays.asList(new ConcreteCell(new ValueInt(-2)), new ConcreteCell(new ValueInt(3)), new ConcreteCell(new ValueInt(5)), new ConcreteCell(new ValueInt(1)));
    List<ConcreteCell> concreteCellsC = Arrays.asList(new ConcreteCell(new ValueInt(-10)), new ConcreteCell(new ValueInt(1)), new ConcreteCell(new ValueInt(100)), new ConcreteCell(new ValueInt(4)));
    List<ConcreteCell> concreteCellsD = Arrays.asList(new ConcreteCell(new ValueInt(20)), new ConcreteCell(new ValueInt(1)), new ConcreteCell(new ValueInt(-3)), new ConcreteCell(new ValueInt(3)));
    HashMap<String, SpecificationColumn<ConcreteCell>> counterexampleColumns = new HashMap<>();
    counterexampleColumns.put("VariableA", new SpecificationColumn<>(variableA, concreteCellsA, new ColumnConfig()));
    counterexampleColumns.put("VariableB", new SpecificationColumn<>(variableB, concreteCellsB, new ColumnConfig()));
    counterexampleColumns.put("VariableC", new SpecificationColumn<>(variableC, concreteCellsC, new ColumnConfig()));
    counterexampleColumns.put("VariableD", new SpecificationColumn<>(variableD, concreteCellsD, new ColumnConfig()));
    List<ConcreteDuration> counterexampleDurations = Arrays.asList(new ConcreteDuration(0, 1),
        new ConcreteDuration(1, 2), new ConcreteDuration(3, 1));
    ConcreteSpecification counterexample = new ConcreteSpecification(counterexampleColumns, counterexampleDurations, true);
    hybridSpec.setCounterExample(counterexample);
  }


  private void setValidSpecListener(ConstraintSpecification theSpec) {
    theSpec.validSpecificationProperty().addListener(new ChangeListener<ValidSpecification>() {
      @Override
      public void changed(ObservableValue<? extends ValidSpecification> observableValue, ValidSpecification oldValue, ValidSpecification newValue) {
        validSpec = newValue;
      }
    });
  }*/
}
