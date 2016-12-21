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
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class Range {
    private ScalarValue<? extends AnyInt, Long> start;
    private ScalarValue<? extends AnyInt, Long> stop;

    /**
     * <p>Constructor for Range.</p>
     *
     * @param start a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     * @param stop a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     */
    public Range(ScalarValue<? extends AnyInt, Long> start, ScalarValue<? extends AnyInt, Long> stop) {
        this.start = start;
        this.stop = stop;
    }

    /**
     * <p>Getter for the field <code>start</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     */
    public ScalarValue<? extends AnyInt, Long> getStart() {
        return start;
    }

    /**
     * <p>Setter for the field <code>start</code>.</p>
     *
     * @param start a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     */
    public void setStart(ScalarValue<? extends AnyInt, Long> start) {
        this.start = start;
    }

    /**
     * <p>Getter for the field <code>stop</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     */
    public ScalarValue<? extends AnyInt, Long> getStop() {
        return stop
                ;
    }

    /**
     * <p>Setter for the field <code>stop</code>.</p>
     *
     * @param stop a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     */
    public void setStop(ScalarValue<? extends AnyInt, Long> stop) {
        this.stop = stop;
    }
}
