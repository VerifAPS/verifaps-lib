package edu.kit.iti.formal.smv.printers;

/*-
 * #%L
 * smv-model
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

import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVModule;
import org.jetbrains.annotations.NotNull;

public class StringPrinter extends Printer {
    private final StringBuilder sb = new StringBuilder();

    public static String toString(@NotNull SMVExpr m) {
        StringPrinter p = new StringPrinter();
        m.accept(p);
        return p.sb.toString();
    }

    public static String toString(@NotNull SMVModule m) {
        StringPrinter p = new StringPrinter();
        m.accept(p);
        return p.sb.toString();
    }

    @Override
    void print(String s) {
        sb.append(s);
    }
}
