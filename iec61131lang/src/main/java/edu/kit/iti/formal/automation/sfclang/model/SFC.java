package edu.kit.iti.formal.automation.sfclang.model;

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

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 22.01.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class SFC {
    public String name;
    public List<SFCStep> steps = new ArrayList<>();
    public List<SFCAction> actions = new ArrayList<>();

    /**
     * <p>getStep.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.sfclang.model.SFCStep} object.
     */
    public SFCStep getStep(String name) {
        return steps.stream().filter(
                (SFCStep step) -> step.name.equals(name)).findFirst().orElse(null);
    }

    /**
     * <p>getAction.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.sfclang.model.SFCAction} object.
     */
    public SFCAction getAction(String name) {
        return actions.stream().filter(
                (SFCAction a) -> a.name.equals(name)).findFirst().orElse(null);
    }

    /**
     * <p>addAction.</p>
     *
     * @param action a {@link edu.kit.iti.formal.automation.sfclang.model.SFCAction} object.
     */
    public void addAction(SFCAction action) {
        actions.add(action);
    }
}
