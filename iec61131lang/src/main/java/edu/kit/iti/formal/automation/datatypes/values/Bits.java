package edu.kit.iti.formal.automation.datatypes.values;

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

import lombok.*;

/**
 * Created by weigl on 11.06.14.
 * Immutable
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
@EqualsAndHashCode
@ToString
public class Bits {
    private long register;
    private final long nbits;

    /**
     * <p>Constructor for Bits.</p>
     *
     * @param nbits a long.
     */
    public Bits(long nbits) {
        this(0, nbits);
    }

    /**
     * <p>Constructor for Bits.</p>
     *
     * @param register a long.
     * @param nbits a long.
     */
    public Bits(long register, long nbits) {
        this.nbits = nbits;
        this.register = register & allMask(); // trunc
    }

    private long allMask() {
        if (nbits == 64) {
            return -1L;
        } else {
            return (1L << nbits) - 1;
        }
    }

    /**
     * <p>shl.</p>
     *
     * @param n a int.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     */
    public Bits shl(int n) {
        return new Bits(register << n, nbits);
    }

    /**
     * <p>shr.</p>
     *
     * @param n a int.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     */
    public Bits shr(int n) {
        return new Bits(register >>> n, nbits);
    }


    /**
     * <p>rol.</p>
     *
     * @param n a int.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     */
    public Bits rol(int n) {
        assert n <= nbits;

        if (n == nbits) {
            return this;
        }


        long maskAll = allMask();
        long maskRetain = (2 << (nbits - n)) - 1;
        long maskLoss = ~maskRetain & maskAll;

        long loss = register & maskRetain;
        long last = (loss >> (nbits - n));
        return new Bits((register << n) | last, nbits);
    }


    /**
     * <p>ror.</p>
     *
     * @param n a int.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     */
    public Bits ror(int n) {
        long maskAll = allMask();
        long maskLoss = (2 << n) - 1;

        long loss = maskLoss & register;
        long first = loss << n;

        return new Bits((register >>> n) | first, nbits);
    }

    /**
     * <p>Getter for the field <code>register</code>.</p>
     *
     * @return a long.
     */
    public long getRegister() {
        return register;
    }


    /**
     * <p>and.</p>
     *
     * @param other a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     */
    public Bits and(Bits other) {
        return new Bits(register & other.register, nbits);
    }

    /**
     * <p>or.</p>
     *
     * @param other a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     */
    public Bits or(Bits other) {
        return new Bits(register | other.register, nbits);
    }

    /**
     * <p>xor.</p>
     *
     * @param other a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.Bits} object.
     */
    public Bits xor(Bits other) {
        return new Bits(register ^ other.register, nbits);
    }


    /**
     * <p>Setter for the field <code>register</code>.</p>
     *
     * @param register a long.
     */
    public void setRegister(long register) {
        this.register = register;
    }
}
