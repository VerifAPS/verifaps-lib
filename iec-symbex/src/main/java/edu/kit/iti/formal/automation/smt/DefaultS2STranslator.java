package edu.kit.iti.formal.automation.smt;

import de.tudresden.inf.lat.jsexp.Sexp;
import edu.kit.iti.formal.smv.ast.GroundDataType;
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
            return newAtomicSexp("BOOL");
        else {
            int width = ((SMVType.SMVTypeWithWidth) datatype).getWidth();
            Sexp bv = newNonAtomicSexp();
            bv.add(newAtomicSexp("_"));
            bv.add(newAtomicSexp("BitVec"));
            bv.add(newAtomicSexp(String.valueOf(width)));
            return bv;
        }
    }

    @Override
    public Sexp translate(SLiteral l) {

        if (l.getSMVType() == SMVType.BOOLEAN)
            return newAtomicSexp(l.value.toString().equalsIgnoreCase("TRUE") ? "true" : "false");

        String prefix = "#b";
        if (l.getSMVType().getBaseType() == GroundDataType.SIGNED_WORD
                || l.getSMVType().getBaseType() == GroundDataType.UNSIGNED_WORD) {
            SMVType.SMVTypeWithWidth t = (SMVType.SMVTypeWithWidth) l.getSMVType();
            BigInteger b = (BigInteger) l.value;
            return newAtomicSexp("#b" + twoComplement(b, t.getWidth()));
        }

        throw new IllegalArgumentException();
    }
}
