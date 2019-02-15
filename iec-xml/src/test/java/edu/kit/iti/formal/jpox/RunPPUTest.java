package edu.kit.iti.formal.jpox;

import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade;
import org.jdom2.JDOMException;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * @author Alexander Weigl
 * @version 1 (30.05.17)
 */
public class RunPPUTest {
    @Test
    public void test() throws URISyntaxException, IOException { test("src/test/resources/test.xml");
    }

    @Test
    public void testPPUNew() throws JDOMException, IOException, URISyntaxException {
        test("/edu/kit/iti/formal/automation/ppu.xml");
    }

    private void test(String location) throws URISyntaxException, IOException {
        URL res = getClass().getResource(location);
        Assumptions.assumeTrue(res != null);
        String out = IECXMLFacade.INSTANCE.extractPLCOpenXml(res);
        System.out.println(out);
    }
}
