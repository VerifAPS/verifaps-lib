package edu.kit.iti.formal.automation.testtables;

import org.apache.commons.io.IOUtils;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
@RunWith(Parameterized.class)
public class FullStackTest {
    private static Collection<Object[]> CASES = new ArrayList<>();
    public static String NUXMV;

    static {
        addCase("examples/constantprogram", "verified",
                "-t constantprogram.xml -c constantprogram.st");

        addCase("examples/constantprogram", "not-verified",
                "-t constantprogram_broken.xml -c constantprogram.st");

        addCase("examples/constantprogram", "not-verified",
                "-t constantprogram_concrete.xml -c constantprogram.st");

        addCase("examples/cycles", "verified",
                "-t cycles.xml -c cycles.st");

        addCase("examples/cycles", "not-verified",
                "-t cycles_wrong.xml -c cycles.st");




        NUXMV = System.getenv().getOrDefault("NUXMV", "nuXmv");
    }

    @Parameterized.Parameter(0)
    public String workingDir;
    @Parameterized.Parameter(1)
    public String args[];
    @Parameterized.Parameter(2)
    public String status;

    private static void addCase(String wd, String status, String args) {
        CASES.add(new Object[]{wd, args.split(" "), status});
    }

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> args() {
        return CASES;
    }


    @Test
    public void testExtern() throws IOException, InterruptedException {
        String javaHome = System.getProperty("java.home");
        String javaBin = javaHome +
                File.separator + "bin" +
                File.separator + "java";
        String classpath = System.getProperty("java.class.path");
        String className = ExTeTa.class.getCanonicalName();


        List<String> commands = new ArrayList<>();
        commands.add(javaBin);
        commands.add("-cp");
        commands.add(classpath);
        commands.add(className);
        commands.addAll(Arrays.asList(args));

        System.out.println(commands.stream().reduce((a, b) -> a + " " + b).get());

        ProcessBuilder builder = new ProcessBuilder(commands)
                .directory(new File(workingDir).getAbsoluteFile());
        builder.environment().put("NUXMV", NUXMV);
        Process process = builder.start();
        process.waitFor();

        String output = IOUtils.toString(process.getInputStream(), "utf-8");
        System.out.println(output);
        IOUtils.copy(process.getErrorStream(), System.err);

        Assert.assertEquals(0, process.exitValue());
        String[] lines = output.split("\n");
        Assert.assertEquals("STATUS: " + status, lines[lines.length - 1]);
    }


}
