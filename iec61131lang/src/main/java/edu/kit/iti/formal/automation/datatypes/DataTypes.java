package edu.kit.iti.formal.automation.datatypes;

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

import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;

/**
 * <p>DataTypes class.</p>
 *
 * @author Alexander Weigl (25.06.2014)
 * @version 1
 */
public class DataTypes {
    public static final BigInteger DEFAULT = BigInteger.ZERO;
    public static final SInt SINT = new SInt();
    public static final USInt USINT = new USInt();
    public static final UInt UINT = new UInt();
    public static final Int INT = new Int();
    public static final UDInt UDINT = new UDInt();
    public static final DInt DINT = new DInt();
    public static final ULInt ULINT = new ULInt();
    public static final LInt LINT = new LInt();
    public static final AnyInt UNKNWON_SIGNED_INT = new AnySignedInt.Arbitrary(-1);
    public static final AnyUnsignedInt UNKNWON_UNSIGNED_INT = new AnyUnsignedInt.Arbitrary(-1);
    public static final AnyInt ANY_INT = new AnySignedInt(-1) {
        @Override
        public Optional<AnyInt> next() {
            return null;
        }

        @Override
        public AnyUnsignedInt asUnsgined() {
            return UNKNWON_UNSIGNED_INT;
        }

        @Override
        public AnyInt asSigned() {
            return UNKNWON_SIGNED_INT;
        }

        @Override
        public boolean isValid(long value) {
            return true;
        }
    };
    static HashMap<String, Any> map = new HashMap<>();

    static {
        add(AnyBit.BOOL);
        add(AnyBit.LWORD);
        add(AnyBit.WORD);
        add(AnyBit.DWORD);

        add(SINT);
        add(INT);
        add(DINT);
        add(LINT);

        add(USINT);
        add(UINT);
        add(UDINT);
        add(ULINT);

        add(AnyReal.LREAL);
        add(AnyReal.REAL);

        add(IECString.STRING_8BIT);
        add(IECString.STRING_16BIT);

        add(TimeType.TIME_TYPE);

        add(AnyDate.DATE);
        add(AnyDate.DATE_AND_TIME);
        add(AnyDate.TIME_OF_DAY);

        map.put("TOD", AnyDate.TIME_OF_DAY);
        map.put("DT", AnyDate.DATE_AND_TIME);
        map.put("T", TimeType.TIME_TYPE);
    }

    static void add(Any any) {
        map.put(any.getName(), any);
        map.put(any.getName().replace("_", ""), any);
    }

    /**
     * <p>getDataType.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public static Any getDataType(String name) {
        return map.get(name);
    }

    /**
     * <p>getDataTypeNames.</p>
     *
     * @return a {@link java.util.Set} object.
     */
    public static Set<String> getDataTypeNames() {
        return map.keySet();
    }

    public static List<? extends AnyInt> getIntegers() {
        return getIntegers(AnyInt.class);
    }

    public static List<? extends AnyInt> getIntegers(Class<? extends AnyInt> anyIntClass) {
        List<? extends AnyInt> list = get(anyIntClass);
        list.sort(Comparator.<AnyInt>comparingInt(o -> o.bitLength));
        return list;
    }

    public static List<? extends AnyInt> getSignedIntegers() {
        return getIntegers(AnySignedInt.class);
    }

    public static List<? extends AnyInt> getUnSignedIntegers() {
        return getIntegers(AnyUnsignedInt.class);
    }

    private static <T extends Any> List<? extends T> get(Class<T> anyClazz) {
        return (List<? extends T>) map.values().stream().filter(
                a -> anyClazz.isAssignableFrom(a.getClass()))
                .collect(Collectors.toList());
    }


    public static AnyInt findSuitableInteger(BigInteger s) {
        return findSuitableInteger(s, getIntegers());
    }

    public static AnyInt findSuitableInteger(BigInteger s, boolean signed) {
        return findSuitableInteger(s,
                signed ? DataTypes.getSignedIntegers()
                        : DataTypes.getUnSignedIntegers()
        );
    }

    public static AnyInt findSuitableInteger(BigInteger s, Iterable<? extends AnyInt> integerTypes) {
        for (AnyInt anyInt : integerTypes) {
            if (s.compareTo(anyInt.getUpperBound()) < 0
                    && anyInt.getLowerBound().compareTo(s) < 0) {
                return anyInt;
            }
        }
        throw new IllegalStateException("integer literal too big");
    }


}
