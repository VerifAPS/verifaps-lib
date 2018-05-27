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
import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.ast.TypeDeclaration;
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

/**
 * @author Philipp Krüger
 * @author Alexander Weigl
 */
public class TestEnumParse extends DefaultVisitor<Void> {

    String code =
            "TYPE\n" +
                    "  MY_ENUM : (one, two, three);\n" +
                    "END_TYPE\n";

    @Test
    public void testEnumMembers() {
        TopLevelElements toplevel = IEC61131Facade.INSTANCE.file(CharStreams.fromString(code));
        TypeDeclarations decls = (TypeDeclarations) toplevel.get(0);
        EnumerationTypeDeclaration enumdecl = (EnumerationTypeDeclaration) decls.get(0);
        assertEquals(Arrays.asList("one", "two", "three"),
                enumdecl.getAllowedValues().stream().map(Token::getText).collect(Collectors.toList()));
    }


}
