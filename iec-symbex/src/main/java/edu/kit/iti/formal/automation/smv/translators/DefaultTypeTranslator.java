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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.exceptions.IllegalTypeException;
import edu.kit.iti.formal.smv.EnumType;
import edu.kit.iti.formal.smv.SMVType;
import edu.kit.iti.formal.smv.SMVTypes;
import edu.kit.iti.formal.smv.SMVWordType;

/**
 * Created by weigl on 11.12.16.
 */
public class DefaultTypeTranslator implements TypeTranslator {
    public static final DefaultTypeTranslator INSTANCE = new DefaultTypeTranslator();
    private static final int WORD_LENGTH = 16;

    @Override
    public SMVType translate(AnyDt datatype) {
        DefaultTranslatorVisitor dtv = new DefaultTranslatorVisitor();
        return datatype.accept(dtv);
    }

    class DefaultTranslatorVisitor implements DataTypeVisitor<SMVType> {
        @Override
        public SMVType visit(AnyReal real) {
            return null;
        }

        @Override
        public SMVType visit(AnyReal.Real real) {
            return null;
        }

        @Override
        public SMVType visit(AnyReal.LReal real) {
            return null;
        }

        @Override
        public SMVType visit(AnyBit anyBit) {
            if (anyBit == AnyBit.Companion.getBOOL()) {
                return SMVTypes.BOOLEAN.INSTANCE;
            }
            return new SMVWordType(false, anyBit.getBitLength());
        }

        @Override
        public SMVType visit(AnyDate.DateAndTime dateAndTime) {
            throw new IllegalTypeException("Could not match");
        }

        @Override
        public SMVType visit(AnyDate.TimeOfDay timeOfDay) {
            return new SMVWordType(true, WORD_LENGTH);
            //throw new IllegalTypeException("Could not match");
        }

        @Override
        public SMVType visit(AnyDate.Date date) {
            throw new IllegalTypeException("Could not match");
        }

        @Override
        public SMVType visit(AnyInt inttype) {
       /*TODO: Make this configurable
            return new SMVType.SMVTypeWithWidth(
                inttype.isSigned() ?
                        GroundDataType.SIGNED_WORD :
                        GroundDataType.UNSIGNED_WORD, inttype.getBitLength());
        */
            return new SMVWordType(true, WORD_LENGTH);
        }

        @Override
        public SMVType visit(EnumerateType enumerateType) {
            return new EnumType(enumerateType.getAllowedValues());
        }

        @Override
        public SMVType visit(TimeType timeType) {
            return new SMVWordType(true, WORD_LENGTH);
        }

        @Override
        public SMVType visit(RangeType rangeType) {
            // TODO base types other than SINT
            // TODO variable width (needs to match with values everywhere)
            return new SMVWordType(true, WORD_LENGTH);
        }

        @Override
        public SMVType visit(RecordType recordType) {
            throw new IllegalTypeException("Could not match " + recordType);
        }

        @Override
        public SMVType visit(PointerType pointerType) {
            throw new IllegalTypeException("Could not match" + pointerType);
        }

        @Override
        public SMVType visit(IECString.String string) {
            throw new IllegalTypeException("Could not match" + string);
        }

        @Override
        public SMVType visit(IECString.WString wString) {
            throw new IllegalTypeException("Could not match");
        }

        @Override
        public SMVType visit(IECArray iecArray) {
            throw new IllegalTypeException("Could not match");
        }

        @Override
        public SMVType visit(AnyNum anyNum) {
            throw new IllegalTypeException("Could not match: " + anyNum);
        }

        @Override
        public SMVType visit(ClassDataType classDataType) {
            return null;
        }
    }
}
