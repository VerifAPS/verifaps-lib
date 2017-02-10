package edu.kit.iti.formal.stvs.model.table;

/**
 * @author Benjamin Alt
 */
public class HybridSpecificationTest {
  private HybridSpecification hybridSpec;
  private ValidSpecification validSpec;

  /* TODO: Write test

  @Before
  public void setUp() throws IllegalValueTypeException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);

    List<CodeIoVariable> codeIoVariables = Arrays.asList(
        new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "A"),
        new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "B"),
        new CodeIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "C"),
        new CodeIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "D"));

    JsonElement json = JsonTableParser.jsonFromResource("hybrid_spec.json", HybridSpecificationTest.class);
    ConstraintSpecification cspec = JsonTableParser.constraintTableFromJson(
        new SimpleObjectProperty<>(typeContext),
        new SimpleObjectProperty<>(codeIoVariables),
        json);

    hybridSpec = new HybridSpecification(cspec, true);
    validSpec = hybridSpec.getValidSpecification();
    setValidSpecListener(hybridSpec);

    /*
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
    theSpec.validSpecificationProperty().addListener(
        (observableValue, oldValue, newValue) -> validSpec = newValue);
  }
  */
}
