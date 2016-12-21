package edu.kit.iti.formal.automation.st;

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

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.Top;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class STUtil {
    /**
     * <p>expr.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public static Expression expr(String str) {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(str));
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        return parser.expression().ast;
    }

    /**
     * <p>print.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @return a {@link java.lang.String} object.
     */
    public static String print(Top ast) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        ast.visit(stp);
        return stp.getString();
    }
}
