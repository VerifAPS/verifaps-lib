package edu.kit.iti.formal.automation.sfclang.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 - 2018 Alexander Weigl
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

import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.Top;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (30.01.18)
 */
@Data
public class SFCNetwork extends Top<IEC61131Parser.Sfc_networkContext> {
    private List<SFCStep> steps = new ArrayList<>();

    @Override
    public SFCNetwork copy() {
        SFCNetwork sfcNetwork = new SFCNetwork();
        sfcNetwork.steps = steps.stream().map(n -> n.copy()).collect(Collectors.toList());
        return sfcNetwork;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public Optional<SFCStep> getStep(String text) {
        return steps.stream().filter(s -> s.getName().equalsIgnoreCase(text)).findAny();
    }
}
