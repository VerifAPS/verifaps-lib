package edu.kit.iti.formal.automation.apps;

import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCFactory;
import edu.kit.iti.formal.automation.symbex.SymbexFactory;
import edu.kit.iti.formal.automation.st.plcopenxml.model.SFCGraph;
import edu.kit.iti.formal.automation.st.visitors.VFactory;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.*;

/**
 * Created by weigl on 10/08/14.
 */
public class SFC2Tex {
    public static void main(String[] args) {
        if (args.length == 0) {
            return;
        }

        for (String s : args) {
            processFile(new File(s));
        }

    }

    private static void processFile(File file) {
        List<SFCGraph> graph = SFCFactory.sfcToGraph(file);

        String baseName = file.getName().replace(".xml", "");

        for (SFCGraph sfcGraph : graph) {
            processGraph(sfcGraph, file.getParentFile(), baseName);
        }
    }

    private static void processGraph(SFCGraph graph, File dir, String baseName) {
        File output = new File(dir, baseName + "_" + graph.getName() + ".tex");
        try {
            FileWriter fw = new FileWriter(output);
            writeTex(graph, fw);
        } catch (IOException e) {
            e.printStackTrace();
        }


    }

    private static void writeTex(SFCGraph graph, Writer fw) throws IOException {
        fw.write("\\documentclass{article}\n" +
                "\\usepackage[utf8]{inputenc}\n\\usepackage{tikz}\n\\usepackage{grafcet}\n\\usetikzlibrary{shapes,arrows,positioning}\n" +
                "\\begin{document}\\begin{tikzpicture}");

        Queue<SFCGraph.Step> queue = new LinkedList<>();

        for (SFCGraph.Node node : graph.getNodes()) {
            if (node instanceof SFCGraph.Step) {
                SFCGraph.Step step = (SFCGraph.Step) node;
                if (step.initial) {
                    queue.add(step);
                }
            }
        }

        NameGiver name = new NameGiver();
        Set<SFCGraph.Step> visited = new HashSet<>();


        while (!queue.isEmpty()) {
            SFCGraph.Step step = queue.poll();
            String n = step.name.replace("_", "-");
            int number = name.get(step.name);

            if (step.initial) {
                fw.write("\\EtapeInit{" + n + "}\n");
            } else {
                fw.write("\\Etape{" + n + "}\n");
            }

            for (SFCGraph.Transition t : step.outgoing) {
                fw.write("\\Transition{" + number + "}\\Recept{T" + number + "}{" + guardString(t.conditions) + "}\n");
                if (!visited.contains(t.to)) {
                    queue.add((SFCGraph.Step) t.to);
                    visited.add((SFCGraph.Step) t.to);
                } else {
                    fw.write("\\LienRetour{T" + number + "}{X" + t.to.name.replace("_", "-") + "}\n");

                }
            }
        }


        fw.write("\\end{tikzpicture}\\end{document}");

        fw.flush();
        fw.close();


    }

    private static String guardString(List<Expression> conditions) {
        Expression expr = SymbexFactory.makeAND(conditions);
        return VFactory.ast2St(expr).replace("_", "-");
    }
}


class NameGiver {
    int current = 000;
    private Map<String, Integer> map = new TreeMap<>();

    public int get(String name) {
        current += 100;
        map.put(name, current);
        return current;
    }
}