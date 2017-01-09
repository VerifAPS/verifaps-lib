package edu.kit.iti.formal.stvs.view.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import javafx.collections.ObservableList;

import java.util.function.Predicate;

/**
 * Controller for the set of either InputVariables TimingDiagrams or OutputVariables TimingDiagrams
 * Created by csicar on 09.01.17.
 */
public abstract class CategoryTimingDiagrams {

    public CategoryTimingDiagrams(ConcreteSpecification concreteSpecification, ObservableList<IOVariable> ioVariables, Selection selection) {

    };
}
