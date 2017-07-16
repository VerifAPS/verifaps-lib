package edu.kit.iti.formal.automation.st.ast;

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

import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.datatypes.values.Value;
import edu.kit.iti.formal.automation.datatypes.values.Values;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.EqualsAndHashCode;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@EqualsAndHashCode
public class EnumerationTypeDeclaration extends TypeDeclaration<Literal> {
    private List<Token> allowedValues = new LinkedList<>();
    private List<Integer> values = new ArrayList<>();
    private Integer counter = 0;

    /**
     * <p>Constructor for EnumerationTypeDeclaration.</p>
     */
    public EnumerationTypeDeclaration() {
        setBaseTypeName("ENUM");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <S> S accept(Visitor<S> visitor) {
        return visitor.visit(this);
    }

    public void addValue(Token text) {
        allowedValues.add(text);
        values.add(counter);
        counter += 1;
    }

    public List<Token> getAllowedValues() {
        return allowedValues;
    }

    public void setAllowedValues(List<Token> allowedValues) {
        this.allowedValues = allowedValues;
    }

    @Override
    public EnumerateType getDataType(GlobalScope globalScope) {
        //TODO rework
        String init = allowedValues.get(0).getText();
        if (initialization != null) {
            if (initialization.getDataType() instanceof EnumerateType) {
                Value value = (Value) initialization.asValue();
                //init = value;
            } else if (initialization.getDataType() instanceof AnyInt) {
                Values.VAnyInt value = (Values.VAnyInt) initialization.asValue();
                //init = allowedValues.get(value);
            }
        }

        EnumerateType et = new EnumerateType(getTypeName(),
                allowedValues.stream().map(Token::getText).collect(Collectors.toList()),
                init);
        setBaseType(et);
        return et;
    }


    @Override
    public EnumerationTypeDeclaration copy() {
        EnumerationTypeDeclaration etd = new EnumerationTypeDeclaration();
        etd.allowedValues = new ArrayList<>(allowedValues);
        etd.counter = counter;
        etd.baseType = baseType;
        etd.baseTypeName = baseTypeName;
        etd.values = new ArrayList<>(values);
        etd.typeName = typeName;
        return etd;
    }


    public void setInt(Literal val) {
        Values.VAnyInt v = (Values.VAnyInt) val.asValue();
        values.set(values.size() - 1, v.getValue().intValue());
        counter = v.getValue().intValue() + 1;
    }
}
