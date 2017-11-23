/*
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

package edu.kit.iti.formal.automation.stoo.trans;

import edu.kit.iti.formal.automation.stoo.STOOSimplifier;

/**
 * @author Augusto Modanese
 */
public abstract class STOOTransformation {
    /**
     * Reference ID for null.
     */
    static final int NULL_REFERENCE_ID = -1;

    /**
     * Name of the variable containing the instance ID.
     */
    static final String INSTANCE_ID_VAR_NAME = "_INSTANCE_ID";

    /**
     * Suffix for the instance ID type.
     */
    static final String INSTANCE_ID_TYPE_SUFFIX = "_TYPE";

    /**
     * Standard prefix of an instance array's name.
     */
    static final String INSTANCE_ARRAY_NAME_PREFIX = "_INSTANCES_";

    /**
     * Standard name to access the global variable list.
     */
    static final String GVL_NAME = "GVL";

    /**
     * Standard name for the self parameter to add to methods. See MethodToFunction.
     */
    static final String SELF_PARAMETER_NAME = "_SELF";

    /**
     * Separator to use between a class' name and its method when converting the method to a function.
     */
    static final String CLASS_METHOD_NAME_SEPARATOR = "_";

    STOOSimplifier.State state;

    public void transform(STOOSimplifier.State state) {
        this.state = state;
    }
}
