package edu.kit.iti.formal.smv.ast;

/*-
 * #%L
 * smv-model
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

import edu.kit.iti.formal.smv.SMVAstVisitor;
import org.jetbrains.annotations.NotNull;

/************************************************************/

/**
 *
 */
public class SBinaryExpression extends SMVExpr {
    /**
     *
     */
    public SMVExpr left;

    /**
     *
     */
    public SMVExpr right;

    /**
     *
     */
    public SBinaryOperator operator;

    public SBinaryExpression(SMVExpr left, SBinaryOperator op, SMVExpr right) {
        this.left = left;
        this.right = right;
        this.operator = op;
    }

    public SBinaryExpression() {

    }

    public SMVType getSMVType() {
        return SMVType.infer(left.getSMVType(), right.getSMVType());
    }

    @Override
    public @NotNull SBinaryExpression inModule(@NotNull String module) {
        return new SBinaryExpression(left.inModule(module), operator, right.inModule(module));
    }


    @Override
    public String toString() {
        return '(' + left.toString() + operator.symbol() + right + ')';
    }

    @Override
    public <T> T accept(SMVAstVisitor<T> visitor) {
        return visitor.visit(this);
    }


    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        SBinaryExpression that = (SBinaryExpression) o;

        if (left != null ? !left.equals(that.left) : that.left != null) return false;
        if (right != null ? !right.equals(that.right) : that.right != null) return false;
        return operator == that.operator;

    }

    @Override
    public int hashCode() {
        int result = left != null ? left.hashCode() : 0;
        result = 31 * result + (right != null ? right.hashCode() : 0);
        result = 31 * result + (operator != null ? operator.hashCode() : 0);
        return result;
    }
}
