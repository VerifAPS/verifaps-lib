package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import edu.kit.iti.formal.automation.Console;
import edu.kit.iti.formal.automation.st.fiphi.BuildTwinStateGraph;
import edu.kit.iti.formal.automation.st.fiphi.DotTwinGraphPrinter;
import edu.kit.iti.formal.automation.st.fiphi.FindFiLocalStrategy;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCFactory;
import edu.kit.iti.formal.automation.st.plcopenxml.model.SFCGraph;
import org.apache.commons.io.FileUtils;

import java.io.File;
import java.io.IOException;
import java.util.List;

/**
 * Created by weigl on 07/10/14.
 */
@Parameters(separators = "=", commandNames = "fiphi", commandDescription = "calculate differences between all equal-named SFC in two pclopenxml files")
public class FiPhi extends App {

    @Parameter(names = "-a", required = true,
            description = "PCLOpen Xml, the older revision")
    private String inputA;

    @Parameter(names = "-b", required = true,
            description = "PCLOpen Xml, the younger revision")
    private String inputB;

    @Parameter(names = "-o", required = true, help = true,
            description = "output prefix, like /tmp/12_")
    private String output;


    public void execute() throws IOException {
        Console.info("Find PHI started");
        Console.info("Input file %s ./. %s", inputA, inputB);
        Console.info("Output will written to %s", output);

        List<SFCGraph> sfcA = SFCFactory.sfcToGraph(new File(inputA));
        List<SFCGraph> sfcB = SFCFactory.sfcToGraph(new File(inputB));

        Console.info("%s SFC found in A", sfcA.size());
        Console.info("%s SFC found in B", sfcB.size());

        for (SFCGraph sfcGraph : sfcA) {
            String nameA = sfcGraph.getName();
            for (SFCGraph graph : sfcB) {
                if (nameA.equals(graph.getName())) {
                    processGraph(sfcGraph, graph);
                }
            }
        }
    }

    private void processGraph(SFCGraph sfcA, SFCGraph sfcB) throws IOException {
        Console.info("Processing graphs: %s", sfcA.getName());
        BuildTwinStateGraph fpis = new BuildTwinStateGraph(sfcA, sfcB);
        fpis.run();

        FileUtils.writeStringToFile(
                new File(output + "_" + sfcA.getName() + ".dot"),
                DotTwinGraphPrinter.print(fpis.root));

        FindFiLocalStrategy ffls = new FindFiLocalStrategy(fpis.root);
        ffls.run();
        Console.info("---------------------------------------");

    }


}
