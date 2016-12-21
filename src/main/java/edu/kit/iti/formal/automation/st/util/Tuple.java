package edu.kit.iti.formal.automation.st.util;

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

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class Tuple<S, T> {
    public final S a;
    public final T b;

    /**
     * <p>Constructor for Tuple.</p>
     *
     * @param a a S object.
     * @param b a T object.
     */
    public Tuple(S a, T b) {
        this.a = a;
        this.b = b;
    }

    /**
     * <p>make.</p>
     *
     * @param a a T object.
     * @param b a S object.
     * @param <T> a T object.
     * @param <S> a S object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.Tuple} object.
     */
    public static <T, S> Tuple<T, S> make(T a, S b) {
        return new Tuple(a, b);
    }
}
