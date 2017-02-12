package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * Created by leonk on 09.02.2017.
 */
public class Z3SolverTest {

  private static String TEST2 = "(declare-const A_0_0 Int)\n" +
      "(declare-const B_0_0 Bool)\n" +
      "(declare-const n_0 Int)\n" +
      "(assert (= A_0_0 10))\n" +
      "(assert (= n_0 1))\n" +
      "(check-sat)\n" +
      "(get-value (A_0_0 B_0_0 n_0))";

  @Test
  public void testSimpleConcretize() throws IOException {
    List<ValidIoVariable> validIoVariables = new ArrayList<>();
    validIoVariables.add(new ValidIoVariable(VariableCategory.INPUT, "A", TypeInt.INT));
    validIoVariables.add(new ValidIoVariable(VariableCategory.OUTPUT, "B", TypeBool.BOOL));
    Optional<ConcreteSpecification> concreteSpecificationOptional = Z3Solver.concretizeVarAssignment(TEST2, validIoVariables);
    System.out.println(concreteSpecificationOptional);
    assertTrue(concreteSpecificationOptional.isPresent());
    ConcreteSpecification concreteSpecification = concreteSpecificationOptional.get();
    assertEquals(1,concreteSpecification.getDurations().get(0).getDuration());
    assertEquals(10, ((ValueInt)concreteSpecification.getColumnByName("A").getCells().get(0).getValue()).getValue());
    assertNotNull(concreteSpecification.getColumnByName("B").getCells().get(0));
  }
}