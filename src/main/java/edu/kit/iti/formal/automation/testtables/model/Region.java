package edu.kit.iti.formal.automation.testtables.model;

/*-
 * #%L
 * geteta
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

import lombok.Data;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * created on 10.12.16.
 *
 * @author Alexander Weigl
 * @version 1
 */
@Data
public class Region extends TableNode {
    private List<TableNode> children = new ArrayList<>();

    public Region(int id) {
        super(id);
    }

    @Override
    public boolean isLeaf() {
        return false;
    }

    /**
     * @return
     */
    @Override
    public int count() {
        return children.stream().mapToInt(TableNode::count).sum();
    }

    /**
     * @return
     */
    @Override
    public List<State> flat() {
        return children.stream()
                .flatMap((a) -> a.flat().stream())
                .collect(Collectors.toList());
    }

    @Override
    public int depth() {
        return 1 + children.stream().mapToInt(TableNode::depth).max().orElse(0);
    }

    @Override
    public List<State.AutomatonState> getAutomataStates() {
        List<State.AutomatonState> seq = new ArrayList<>(100);
        flat().forEach(state -> seq.addAll(state.getAutomataStates()));
        return seq;
    }
}
