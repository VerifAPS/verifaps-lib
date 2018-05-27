package edu.kit.iti.formal.automation.sfclang

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

/**
 * Created by weigl on 11.09.15.
 *
 * @author weigl
 * @version $Id: $Id
 */
class SFCLayouter/*
    static class LayoutMetaData {
        int childBranching = 0;
        double width, height, x, y;
    }

    HashMap<String, LayoutMetaData> meta = new HashMap<>();

    private final SFCImplementation sfcDeclaration;

    public SFCLayouter(SFCImplementation declaration) {
        sfcDeclaration = declaration;
    }

    public void widthOfSubSfc(StepDeclaration step) {
        Queue<StepDeclaration> steps = new LinkedList<>();
        Set<String> visited = new HashSet<>();

        while (!steps.isEmpty()) {
            step = steps.poll();
            visited.add(step.getName());

            for (TransitionDeclaration successor : getSuccessors(step)) {
                for (String childName : successor.getTo()) {
                    if (visited.contains(childName))
                        continue;
                }
            }
        }
    }


    public int widthOfSubSfc(Set<String> visited, StepDeclaration step) {
        visited.add(step.getName());
        int sum = 0;

        for (TransitionDeclaration successor : getSuccessors(step)) {

            for (String childName : successor.getTo()) {

                if (visited.contains(childName))
                    continue;

                sum += widthOfSubSfc(visited, sfcDeclaration.getStep(childName));
            }
        }
        getMetaData(step.getName()).childBranching = sum;
        return sum;
    }

    private LayoutMetaData getMetaData(String name) {
        return meta.get(name);
    }


    public void layout() {
        StepDeclaration init = null;
        for (StepDeclaration s : sfcDeclaration.getSteps()) {
            if (s.isInitialStep()) {
                init = s;
                break;
            }
        }
        placeIn(init, 0, 0);
        List<TransitionDeclaration> transitions = getSuccessors(init);

        int[] size = new int[transitions.size()];

        for (TransitionDeclaration t : transitions) {


        }
    }

    private void placeIn(StepDeclaration s, int x, int y) {


    }

    public List<TransitionDeclaration> getSuccessors(StepDeclaration sd) {
        List<TransitionDeclaration> list = new ArrayList<>();
        for (TransitionDeclaration t : sfcDeclaration.getTransitions()) {
            if (t.getFrom().contains(sd.getName())) {
                list.add(t);
            }
        }
        return list;
    }
*/
