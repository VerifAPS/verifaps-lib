package edu.kit.iti.formal.automation.smv.translators;

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.datatypes.values.Bits;
import edu.kit.iti.formal.automation.datatypes.values.Value;
import edu.kit.iti.formal.automation.datatypes.values.Values;

import javax.annotation.Nonnull;
import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class DefaultInitValue implements InitValueTranslator {
    public static final DefaultInitValue INSTANCE = new DefaultInitValue();
    private static final DataTypeVisitor<Value> VISITOR = new InitValueVisitor();

    @Nonnull
    public Value getInit(@Nonnull Any type) {
        return type.accept(VISITOR);
    }

    private static class InitValueVisitor implements DataTypeVisitor<Value> {
        @Override
        public Value visit(AnyInt anyInt) {
            return new Values.VAnyInt(anyInt, BigInteger.ZERO);
        }

        @Override
        public Value visit(AnyReal anyInt) {
            return new Values.VAnyReal(anyInt, BigDecimal.ZERO);
        }

        @Override
        public Value visit(AnyBit.Bool bool) {
            return new Values.VBool(bool, false);
        }

        @Override
        public Value visit(AnyBit word) {
            return new Values.VAnyBit(word, new Bits(word.getBitLength(), 0));
        }

        @Override
        public Value visit(EnumerateType enumerateType) {
            return new Values.VAnyEnum(enumerateType, enumerateType.getDefValue());
        }
    }
}
