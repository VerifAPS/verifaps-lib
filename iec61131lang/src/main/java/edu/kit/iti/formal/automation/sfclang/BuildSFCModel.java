package edu.kit.iti.formal.automation.sfclang;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;
import edu.kit.iti.formal.automation.sfclang.model.SFC;
import edu.kit.iti.formal.automation.sfclang.model.SFCAction;
import edu.kit.iti.formal.automation.sfclang.model.SFCStep;
import edu.kit.iti.formal.automation.sfclang.model.SFCTransition;
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Created by weigl on 22.01.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class BuildSFCModel {
    private final SFCDeclaration sfcdecl;
    SFC model = new SFC();

    /**
     * <p>Constructor for BuildSFCModel.</p>
     *
     * @param decl a {@link edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration} object.
     */
    public BuildSFCModel(SFCDeclaration decl) {
        sfcdecl = decl;
        model.name = decl.getIdentifier();

        for (FunctionBlockDeclaration adecl :
                decl.getActions()) {
            SFCAction action = new SFCAction();
            action.name = adecl.getName();
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

    /**
     * <p>Getter for the field <code>model</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.sfclang.model.SFC} object.
     */
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
