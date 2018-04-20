package edu.kit.iti.formal.automation.smt;

/*-
 * #%L
 * iec-symbex
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

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import de.tudresden.inf.lat.jsexp.SexpParserException;
import edu.kit.iti.formal.smv.GroundDataType;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVType;

import java.math.BigInteger;

import static de.tudresden.inf.lat.jsexp.SexpFactory.newAtomicSexp;
import static de.tudresden.inf.lat.jsexp.SexpFactory.newNonAtomicSexp;

/**
 * Default translator for types from smv to smt. Uses bit vectors!
 *
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
public class DefaultS2STranslator implements S2SDataTypeTranslator {
    public static char[] paddedString(int length, char fill, String s) {
        char[] sb = new char[Math.max(length, s.length())];
        int i = 0;
        for (; i < length - s.length(); i++)
            sb[i] = fill;

        for (int j = 0; j < s.length(); j++, i++)
            sb[i] = s.charAt(j);
        return sb;
    }

    public static String twoComplement(BigInteger integer, int bitLength) {
        BigInteger pos = integer.signum() < 0 ? integer.negate() : integer;
        String binary = pos.toString(2);
        char[] b = paddedString(bitLength, '0', binary);
        if (integer.signum() < 0) {
            //complement
            for (int i = 0; i < b.length; i++) {
                b[i] = b[i] == '1' ? '0' : '1';
            }

            //+1
            for (int i = b.length - 1; i >= 0; i--) {
                b[i] = (char) (b[i] == '1' ? '0' : '1');
                if (b[i] == '1') {
                    break;
                }
            }

        }
        return new String(b);
    }

    @Override
    public Sexp translate(SMVType datatype) {
        if (GroundDataType.BOOLEAN == datatype.getBaseType())
            return newAtomicSexp(SMTProgram.SMT_BOOLEAN);

        if (datatype instanceof SMVType.SMVTypeWithWidth) {
            int width = ((SMVType.SMVTypeWithWidth) datatype).getWidth();
            Sexp bv = newNonAtomicSexp();
            bv.add(newAtomicSexp("_"));
            bv.add(newAtomicSexp("BitVec"));
            bv.add(newAtomicSexp(String.valueOf(width)));
            return bv;
        }

        if(datatype instanceof SMVType.EnumType) {
            try {
                return SexpFactory.parse("(_ BitVec 16)");
            } catch (SexpParserException e) {
                e.printStackTrace();
            }
        }

        throw new IllegalArgumentException();
    }
    @Override
    public Sexp translate(SLiteral l) {

        if (l.getSMVType() == SMVType.Companion.getBOOLEAN())
            return newAtomicSexp(l.getValue().toString().equalsIgnoreCase("TRUE") ? "true" : "false");

        String prefix = "#b";
        if (l.getSMVType().getBaseType() == GroundDataType.SIGNED_WORD
                || l.getSMVType().getBaseType() == GroundDataType.UNSIGNED_WORD) {
            SMVType.SMVTypeWithWidth t = (SMVType.SMVTypeWithWidth) l.getSMVType();
            BigInteger b = (BigInteger) l.getValue();
            return newAtomicSexp("#b" + twoComplement(b, t.getWidth()));
        }

        if (l.getSMVType() instanceof SMVType.EnumType) {
            SMVType.EnumType et = (SMVType.EnumType) l.getSMVType();
            String value = (String) l.getValue();
            int i = et.getValues().indexOf(value);
            return newAtomicSexp("#b" + twoComplement(BigInteger.valueOf(i), 16));
        }

        throw new IllegalArgumentException();
    }
}
