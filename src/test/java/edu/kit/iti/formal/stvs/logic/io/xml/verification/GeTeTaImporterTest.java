package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import org.junit.Before;
import org.junit.Test;

import java.io.FileInputStream;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * @author Benjamin Alt
 */
public class GeTeTaImporterTest {
  @Test
  public void testDoImport() throws Exception {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    GeTeTaImporter importer = new GeTeTaImporter(typeContext);
    VerificationResult result = importer.doImport(this.getClass().getResourceAsStream
        ("report_counterexample_ints_1.xml"));
    assertFalse(result.isSuccessful());
    ConcreteSpecification counterexample = result.getCounterExample();
    assertEquals(1, counterexample.getDurations().size());
    assertEquals(1, counterexample.getRows().size());
    assertEquals(new ConcreteDuration(0, 1), counterexample.getDurations().get(0));
    Map<String,ConcreteCell> expectedRowCells = new HashMap<>();
    expectedRowCells.put("i", new ConcreteCell(new ValueInt(0)));
    expectedRowCells.put("o", new ConcreteCell(new ValueInt(0)));
    expectedRowCells.put("c", new ConcreteCell(new ValueInt(43)));
    SpecificationRow<ConcreteCell> expectedRow = SpecificationRow.createUnobservableRow
        (expectedRowCells);
    assertEquals(expectedRow, counterexample.getRows().get(0));
    assertTrue(counterexample.isCounterExample());
  }

}