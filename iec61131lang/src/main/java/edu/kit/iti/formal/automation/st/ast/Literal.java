package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
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

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.datatypes.values.Value;
import edu.kit.iti.formal.automation.datatypes.values.ValueTransformation;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.sfclang.Utils;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.NoArgsConstructor;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
@Data
@NoArgsConstructor
public class Literal extends Initialization {
    private final IdentifierPlaceHolder<Any> dataType = new IdentifierPlaceHolder<>();
    private boolean dataTypeExplicit;
    private Token token;
    // for integers only
    private boolean signed;

    public Literal(String dataTypeName, Token symbol) {
        token = symbol;
        dataType.setIdentifier(dataTypeName);
    }


    public Literal(String dataTypeName, String symbol) {
        token = new CommonToken(-1, symbol);
        dataType.setIdentifier(dataTypeName);
    }

    public Literal(Any dataType, String symbol) {
        token = new CommonToken(-1, symbol);
        this.dataType.setIdentifiedObject(dataType);
    }

    public Literal(Any dataType, Token symbol) {
        token = symbol;
        this.dataType.setIdentifiedObject(dataType);
    }

    /**
     * @return the text represenation of this literal, without any prefix
     */
    public String getTextValue() {
        Utils.Splitted s = Utils.split(getText());
        return s.value().orElse(null);
    }

    public static Literal integer(Token token, boolean signed) {
        Literal l = new Literal(DataTypes.ANY_INT, token);
        Utils.Splitted s = Utils.split(token.getText());
        if (s.prefix().isPresent()) {
            l.setDataTypeExplicit(true);
            l.setDataType(DataTypes.getDataType(s.prefix().get()));


        }
        l.setSigned(signed);
        return l;
    }

    public static Literal enumerate(Token token) {
        String dataTypeName = token.getText().split("[.#]")[0];
        return new Literal(dataTypeName, token);
    }

    public static Literal bool(Token symbol) {
        assert "TRUE".equalsIgnoreCase(symbol.getText())
                || "FALSE".equalsIgnoreCase(symbol.getText());
        return new Literal(AnyBit.BOOL, symbol);
    }

    public static Literal word(Token symbol) {
        String s = symbol.getText();
        Utils.Splitted first = Utils.split(s);

        if ("TRUE".equalsIgnoreCase(first.value().get()))
            return bool(symbol);
        if ("FALSE".equalsIgnoreCase(first.value().get()))
            return bool(symbol);


        AnyBit dataType = null;
        if (first.prefix().isPresent()) {
            dataType = AnyBit.DATATYPES
                    .stream()
                    .filter(a -> a.getName().equalsIgnoreCase(first.prefix().get()))
                    .findAny()
                    .get();

        }
        return new Literal(dataType, symbol);
    }

    public static Literal real(Token symbol) {
        return new Literal(AnyReal.REAL, symbol);
    }

    /*
    @Override
    public Literal clone() throws CloneNotSupportedException {
        Literal l = (Literal) super.clone();
        l.token = token;
        l.dataType = dataType.clone();
        return l;
    }*/

    public static Literal string(Token symbol, boolean b) {
        return new Literal(b ? IECString.STRING_16BIT : IECString.STRING_8BIT, symbol);

    }

    public static Literal time(Token text) {
        return new Literal(AnyReal.LREAL, text);
    }

    public static Literal timeOfDay(Token text) {
        return new Literal(AnyReal.LREAL, text);

    }

    public static Literal date(Token symbol) {
        return new Literal(AnyReal.LREAL, symbol);

    }

    public static Literal dateAndTime(Token symbol) {
        return new Literal(AnyReal.LREAL, symbol);
    }

    public static Literal integer(int val) {
        return integer(new CommonToken(-1, "" + Math.abs(val)), val < 0);
    }

    public static Literal ref_null(Token symbol) {
        return new Literal(AnyReference.ANY_REF, symbol);
    }

    public Any getDataType() {
        return dataType.getIdentifiedObject();
    }

    public void setDataType(Any dataType) {
        this.dataType.setIdentifiedObject(dataType);
    }

    public String getDataTypeName() {
        return dataType.getIdentifier();
    }

    public String getText() {
        return (signed ? "-" : "") + token.getText();
    }

    @Override
    public Any dataType(Scope localScope) throws VariableNotDefinedException, TypeConformityException {
        return dataType.getIdentifiedObject();
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public Value asValue() {
        return asValue(new ValueTransformation(this));
    }

    private Value asValue(DataTypeVisitor<Value> transformer) {
        if(dataType.getIdentifiedObject()==null) {
            throw new IllegalStateException("no identified data type");
        }
        return dataType.getIdentifiedObject().accept(transformer);
    }

    @Override
    public Literal copy() {
        Literal l = new Literal(getDataTypeName(), getToken());
        l.dataTypeExplicit = dataTypeExplicit;
        l.signed = signed;
        l.dataType.setIdentifiedObject(dataType.getIdentifiedObject());
        return l;
    }
}

