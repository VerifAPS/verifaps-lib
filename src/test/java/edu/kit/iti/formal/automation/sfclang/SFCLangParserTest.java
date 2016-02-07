package edu.kit.iti.formal.automation.sfclang;


import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

/**
 * Created by weigl on 07.02.16.
 */
@RunWith(Parameterized.class)
public class SFCLangParserTest {

    @Parameterized.Parameters
    public static Collection<String> data() {
        return Arrays.asList(new String[]{
                "data/Algo1_left.sfc",
                "data/Algo1_right.sfc",
                "data/Delay1_left.sfc",
                "data/Delay1_right.sfc",
                "data/EmptyStep1_left.sfc",
                "data/EmptyStep1_right.sfc",
                "data/Idempotence1_left.sfc",
                "data/Idempotence1_right.sfc",
                "data/Input1_left.sfc",
                "data/Input1_right.sfc",
                "data/LoopUnwinding1_left.sfc",
                "data/LoopUnwinding1_right.sfc",
                "data/Transition1_left.sfc",
                "data/Transition1_right.sfc",
                "data/Transition2_left.sfc",
                "data/Transition2_right.sfc",
                "data/Types1_left.sfc",
                "data/Types1_right.sfc"
        });
    }

    private String inputFilename;


    public SFCLangParserTest(String inputFilename) {
        this.inputFilename = inputFilename;
    }


    @Test
    public void read() throws ClassNotFoundException, IOException {
        System.out.println("Test: " + inputFilename);
        SFCLangFactory.parse(getClass()
                .getResourceAsStream(inputFilename));
    }
}
