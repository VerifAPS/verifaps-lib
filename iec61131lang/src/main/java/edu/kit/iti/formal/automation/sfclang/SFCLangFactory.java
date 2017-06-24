package edu.kit.iti.formal.automation.sfclang;

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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST;
import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import org.antlr.v4.runtime.*;

import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;

/**
 * Created by weigl on 07.02.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class SFCLangFactory {
    public static SFCDeclaration parse(String input) throws IOException {
        return parse(CharStreams.fromString(input));
    }

    public static SFCDeclaration parse(CharStream cs) {
        IEC61131Parser parser = IEC61131Facade.getParser(cs);
        return (SFCDeclaration) parser.start_sfc().accept(new IECParseTreeToAST());
    }
}
