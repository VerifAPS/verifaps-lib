package edu.kit.iti.formal.automation.testtables;

import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.testtables.builder.TableTransformation;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SMVType;
import org.apache.commons.io.FileUtils;
import org.junit.Assert;
import org.junit.Test;

import javax.xml.bind.JAXBException;
import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
public class SMVModuleBuilderTest {
    @Test
    public void testDetWait1() throws JAXBException, IOException {
        test("src/test/resources/detwait/detwait1.xml",
                "src/test/resources/detwait/detwait1.smv");
    }

    @Test
    public void testDetWait2() throws JAXBException, IOException {
        test("src/test/resources/detwait/detwait2.xml",
                "src/test/resources/detwait/detwait2.smv");
    }

    @Test
    public void testDetWait3() throws JAXBException, IOException {
        test("src/test/resources/detwait/detwait3.xml",
                "src/test/resources/detwait/detwait1.smv");
    }

    public void test(String table, String expectedSMVFile) throws JAXBException, IOException {
        GeneralizedTestTable gtt = Facade.readTable(table);
        String expected = FileUtils.readFileToString(new java.io.File(expectedSMVFile), "utf-8");
        SMVType enumType = Facade.createSuperEnum(new TopLevelElements());
        TableTransformation tt = new TableTransformation(gtt, enumType);
        SMVModule module = tt.transform();
        String output = module.toString();
        Assert.assertEquals(expected, output);
    }
}
