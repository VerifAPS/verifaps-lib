package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecificationTest;
import edu.kit.iti.formal.stvs.model.table.TableUtil;
import javafx.collections.FXCollections;
import javafx.collections.ObservableSet;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;

import static junit.framework.TestCase.assertEquals;

/**
 * Created by bal on 05.02.17.
 */
public class XmlConstraintSpecImporterTest {

  private XmlConstraintSpecImporter importer;

  @Before
  public void setUp() throws ImportException {
    importer = new XmlConstraintSpecImporter();
  }
  
  @Test
  public void testDoImportValid1() throws Exception {
    FileInputStream inputStream = new FileInputStream(new File
        (this.getClass().getResource("spec_constraint_valid_1.xml").toURI()));
    ConstraintSpecification importedSpec = importer.doImport(inputStream);
    JsonElement testjson = TableUtil.jsonFromResource("valid_table.json",
        ConstraintSpecificationTest.class);

    ObservableSet<CodeIoVariable> codeIoVariables = FXCollections.observableSet(
        new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "Counter"),
        new CodeIoVariable(VariableCategory.OUTPUT, TypeBool.BOOL, "Active")
    );

    ObservableSet<Type> typeContext = FXCollections.observableSet(TypeInt.INT, TypeBool.BOOL);

    ConstraintSpecification expectedSpec =
        TableUtil.constraintTableFromJson(typeContext, codeIoVariables, testjson);
    assertEquals(expectedSpec, importedSpec);

  }

}