package edu.kit.iti.formal.smv.ast;

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.smv.SMVAstVisitor;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (11.06.17)
 */
public class SQuantified extends SMVExpr {
    private STemporalOperator operator;
    private List<SMVExpr> quantified = new ArrayList<>(2);

    public SQuantified() {
    }

    public SQuantified(STemporalOperator operator, List<SMVExpr> quantified) {
        this.operator = operator;
        this.quantified = quantified;
    }

    public SQuantified(STemporalOperator operator, SMVExpr... expr) {
        this(operator, Arrays.asList(expr));
    }

    @Override
    public SMVType getSMVType() {
        return SMVType.BOOLEAN;
    }

    @Override
    public @NotNull SQuantified inModule(@NotNull String module) {
        return new SQuantified(operator,
                quantified.stream().map(a -> a.inModule(module)).collect(Collectors.toList()));
    }

    @Override
    public <T> T accept(SMVAstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public STemporalOperator getOperator() {
        return operator;
    }

    public void setOperator(STemporalOperator operator) {
        this.operator = operator;
    }

    public List<SMVExpr> getQuantified() {
        return quantified;
    }


    public SMVExpr getQuantified(int i) {
        return quantified.get(i);
    }
}
