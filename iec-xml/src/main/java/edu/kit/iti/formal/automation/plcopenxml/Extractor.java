package edu.kit.iti.formal.automation.plcopenxml;

/*-
 * #%L
 * iec-xml
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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import joptsimple.OptionParser;
import joptsimple.OptionSet;
import org.jdom2.JDOMException;
import org.jetbrains.annotations.NotNull;

import java.io.File;
import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (21.11.17)
 */
public class Extractor {
    public static boolean toSt0;
    public static File output;

    public static void main(String args[]) throws JDOMException, IOException {
        OptionParser parser = new OptionParser("0o::h*");
        OptionSet options = parser.parse(args);

        if (options.hasArgument("o")) {
            output = new File(options.valueOf("o").toString());
        }

        toSt0 = options.has("0");

        String input = options.nonOptionArguments().get(0).toString();
        TopLevelElements toplevel = IECXMLFacade.readPLCOpenXml(input);
        @NotNull String out = IEC61131Facade.INSTANCE.print(toplevel);
        System.out.println(out);
    }
}
