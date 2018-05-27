package edu.kit.iti.formal.automation;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2018 Alexander Weigl
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

import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import org.antlr.v4.runtime.CharStreams;
import org.jetbrains.annotations.NotNull;
import org.junit.Test;

import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (18.02.18)
 */
public class ProgramWithActionsTest {
    @Test
    public void test() throws IOException {
        TopLevelElements tle = IEC61131Facade.INSTANCE.file(CharStreams.fromStream(
                getClass().getResourceAsStream("program_with_actions.st")
        ));
        TopLevelElements newTle = SymbExFacade.simplify(tle);
        System.out.println(IEC61131Facade.INSTANCE.print(newTle));
    }
}
