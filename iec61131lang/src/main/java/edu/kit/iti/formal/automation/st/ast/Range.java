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

import lombok.Data;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@Data
public class Range implements Copyable<Range> {
    private final Literal start, stop;

    public Range(Literal start, Literal stop) {
        this.start = start;
        this.stop = stop;
    }

    public Range(int start, int stop) {
        this(Literal.integer(start), Literal.integer(stop));
    }

    /*public Range(Pair<Integer, Integer> p) {
        this(p.getKey(), p.getValue());
    }*/

    @Override
    public Range copy() {
        return new Range(start.copy(), stop.copy());
    }

    public int getStartValue() {
        return Integer.valueOf(start.getText());
    }

    public int getStopValue() {
        return Integer.valueOf(stop.getText());
    }
}
