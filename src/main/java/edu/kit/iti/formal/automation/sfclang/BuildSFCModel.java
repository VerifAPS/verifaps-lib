package edu.kit.iti.formal.automation.sfclang;


import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.model.SFCAction;
import edu.kit.iti.formal.automation.sfclang.model.SFCStep;
import edu.kit.iti.formal.automation.sfclang.model.SFCTransition;
import edu.kit.iti.formal.automation.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;
import edu.kit.iti.formal.automation.sfclang.model.SFC;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Created by weigl on 22.01.16.
 */
public class BuildSFCModel {
    private final SFCDeclaration sfcdecl;
    SFC model = new SFC();

    public BuildSFCModel(SFCDeclaration decl) {
        sfcdecl = decl;
        model.name = decl.getName();

        for (FunctionBlockDeclaration adecl :
                decl.getActions()) {
            SFCAction action = new SFCAction();
            action.name = adecl.getFunctionBlockName();
            action.statements = adecl.getFunctionBody();
            model.addAction(action);
        }

        for (StepDeclaration sdecl :
                decl.getSteps()) {
            model.steps.add(transform(sdecl));
        }


        for (TransitionDeclaration td : decl.getTransitions()) {
            SFCTransition transition = new SFCTransition();

            transition.from.addAll(
                    td.getFrom().stream()
                            .map(model::getStep)
                            .collect(Collectors.toList()));


            transition.to.addAll(
                    td.getTo().stream()
                            .map(model::getStep)
                            .collect(Collectors.toList()));

            transition.guard = td.getGuard();
        }
    }

    public SFC getModel() {
        return model;
    }

    private SFCStep transform(StepDeclaration sdecl) {
        SFCStep s = new SFCStep();
        s.name = sdecl.getName();

        for (Map.Entry<String, List<String>> a :
                sdecl.getEvents().entrySet()) {
            s.events.put(a.getKey(), transform(a.getValue()));
        }

        return s;
    }

    private List<SFCAction> transform(List<String> value) {
        return value.stream().map(model::getAction).collect(Collectors.toList());
    }
}
