package edu.kit.iti.formal.stvs.logic.examples;

import edu.kit.iti.formal.stvs.model.examples.Example;
import org.apache.commons.io.IOUtils;

import java.util.ArrayList;
import java.util.List;
import java.util.ServiceLoader;

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
public class ExamplesFacade {
    public static List<Example> getExamples() {
        ServiceLoader<Example> loader = ServiceLoader.load(Example.class);
        ArrayList<Example> list = new ArrayList<>();
        loader.iterator().forEachRemaining(list::add);
        return list;
    }
}
