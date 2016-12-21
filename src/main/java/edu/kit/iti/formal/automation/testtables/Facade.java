package edu.kit.iti.formal.automation.testtables;

/*-
 * #%L
 * geteta
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
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.testtables.io.TableReader;
import edu.kit.iti.formal.automation.testtables.model.SReference;
import edu.kit.iti.formal.automation.testtables.io.NuXMVAdapter;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SVariable;
import org.apache.commons.io.IOUtils;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

public class Facade {
    public static GeneralizedTestTable readTable(String filename) throws JAXBException {
        TableReader tr = new TableReader(new File(filename));
        tr.run();
        return tr.getProduct();
    }

    public static TopLevelElements readProgram(String optionValue) throws IOException {
        try (FileReader r = new FileReader(optionValue)) {
            TopLevelElements a = IEC61131Facade.file(IOUtils.toString(r));
            IEC61131Facade.resolveDataTypes(a);
            return a;
        }
    }

    public static DelayModuleBuilder delay(SReference ref) {
        DelayModuleBuilder dmb = new DelayModuleBuilder(ref.getVariable(),
                ref.getCycles());
        return dmb;
    }


    public static SMVModule glue(SMVModule modTable, SMVModule modCode) {
        BinaryModelGluer mg = new BinaryModelGluer(modTable, modCode);
        mg.run();
        return mg.getProduct();
    }

    public static boolean runNuXMV(String tableFilename, SMVModule... modules) {
       return runNuXMV(tableFilename, Arrays.asList(modules));
    }

    public static String getHistoryName(SVariable variable, int cycles) {
        return getHistoryName(variable) + "._$" + cycles;
    }

    public static String getHistoryName(SVariable variable) {
        return variable.getName() + "__history";
    }

    public static boolean runNuXMV(String tableFilename, List<SMVModule> modules) {
        NuXMVAdapter adapter = new NuXMVAdapter(new File(tableFilename), modules);
        adapter.run();
        return adapter.isVerified();
    }
}
