package edu.kit.iti.formal.automation.testtables;

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.State;
import org.junit.After;
import org.junit.Assert;
import org.junit.Test;

import javax.xml.bind.JAXBException;

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
public class StateReachabilityTest {
    @After
    public void reporting() {
        /*Report.XML_MODE = false;
        Report.close();*/
    }

    @Test
    public void testReachabilityDetWait1() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/detwait/detwait1.xml");
        String out = getReachabilityString(gtt);
        Assert.assertEquals("1#(2)\n" +
                "2#(-1)", out);
    }

    @Test
    public void testReachabilityDetWait2() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/detwait/detwait2.xml");
        String out = getReachabilityString(gtt);
        System.out.println(out);
        Assert.assertEquals("1#(2)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#()", out);
    }

    @Test
    public void testReachabilityDetWait3() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/detwait/detwait3.xml");
        String out = getReachabilityString(gtt);
        System.out.println(out);
        Assert.assertEquals("1#(2)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#()", out);
    }


    @Test
    public void testReachabilityOmega1() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/omega/reachability1.xml");
        String out = getReachabilityString(gtt);
        System.out.println(out);
        Assert.assertEquals("1#(2)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#()", out);
    }

    @Test
    public void testReachability1() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/reachability/reachability1.xml");
        String out = getReachabilityString(gtt);
        System.out.println(out);
        Assert.assertEquals("1#(2)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#(-1)", out);
    }

    @Test
    public void testReachability4() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/reachability/reachability4.xml");
        String out = getReachabilityString(gtt);
        System.out.println(out);
        Assert.assertEquals("1#(3)\n" +
                "3#(5)\n" +
                "5#(3,7)\n" +
                "7#(5,9)\n" +
                "9#(7,9,10)\n" +
                "10#(11,12)\n" +
                "11#(12)\n" +
                "12#(-1)", out);
    }

    @Test
    public void testReachability2() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/reachability/reachability2.xml");
        String out = getReachabilityString(gtt);
        System.out.println(out);
        Assert.assertEquals("1#(2,3,4)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#(-1)", out);
    }

    @Test
    public void testReachability3() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/reachability/reachability3.xml");
        String out = getReachabilityString(gtt);
        System.out.println(out);
        Assert.assertEquals("1#(7)\n" +
                "7#(7,8)\n" +
                "8#(9,10)\n" +
                "9#(10)\n" +
                "10#(-1)", out);
    }


    @Test
    public void testReachability5() throws JAXBException {
        GeneralizedTestTable gtt = Facade.readTable("src/test/resources/reachability/reachability5.xml");
        String out = getReachabilityString(gtt);
        System.out.println(out);
        Assert.assertEquals("1#(3)\n" +
                "3#(3,4)\n" +
                "4#(-1)", out);
    }


    public String getReachabilityString(GeneralizedTestTable gtt) {
        gtt.calculateReachability();
        String r = gtt.getRegion().flat().stream().map(s ->
                s.getId() + "#(" +
                        s.getOutgoing().stream()
                                .map(State::getId)
                                .map(String::valueOf)
                                .reduce((a, b) -> a + "," + b)
                                .orElse("") + ")"
        ).reduce((a, b) -> a + "\n" + b)
                .orElse("");
        return r;
    }
}