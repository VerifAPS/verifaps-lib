package edu.kit.iti.formal.automation.st;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Test;

/**
 * @author Philipp Krüger
 */
public class TestParseEmptyString {

    @Test//(expected = ErrorReporter.IEC61131ParserException.class)
    public void testParseEmptyString() {
        TopLevelElements tle = IEC61131Facade.INSTANCE.file(CharStreams.fromString(""));
        Assert.assertEquals(0, tle.size());
    }
}
