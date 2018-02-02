package edu.kit.iti.formal.automation.testtables;

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.State;
import org.junit.Assert;
import org.junit.Test;

import javax.xml.bind.JAXBException;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
public class OmegaSimplifierTest {
    @Test
    public void run_omga_simplify1() throws Exception {
        List<Integer> ignored = test("simplify1.xml");
        Assert.assertEquals(Arrays.asList(5, 6, 7, 8), ignored);
    }


    private List<Integer> test(String filename) throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/omega/" + filename);
        OmegaSimplifier os = new OmegaSimplifier(gtt);
        os.run();
        return os.getIgnored().stream().map(State::getId).collect(Collectors.toList());
    }

    @Test
    public void run_omga_simplify2() throws Exception {
        List<Integer> ignored = test("simplify2.xml");
        Assert.assertEquals(Arrays.asList(6, 7, 8, 9), ignored);
    }

    @Test
    public void run_omga_simplify3() throws Exception {
        List<Integer> ignored = test("simplify3.xml");
        Assert.assertEquals(Arrays.asList(22, 23, 24), ignored);
    }

}