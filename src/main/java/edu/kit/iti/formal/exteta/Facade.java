package edu.kit.iti.formal.exteta;

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.exteta.io.NuXMVAdapter;
import edu.kit.iti.formal.exteta.io.TableReader;
import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;
import edu.kit.iti.formal.smv.ast.SMVModule;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.apache.commons.io.IOUtils;

import javax.xml.bind.JAXBException;
import java.awt.color.ICC_ColorSpace;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.List;

class Facade {
    static GeneralizedTestTable readTable(String filename) throws JAXBException {
        TableReader tr = new TableReader(new File(filename));
        tr.run();
        return tr.getProduct();
    }

    static TopLevelElements readProgram(String optionValue) throws IOException {
        try (FileReader r = new FileReader(optionValue)) {
            TopLevelElements a = IEC61131Facade.file(IOUtils.toString(r));
            IEC61131Facade.resolveDataTypes(a);
            return a;
        }
    }

    public static SMVModule glue(SMVModule modTable, SMVModule modCode) {
        BinaryModelGluer mg = new BinaryModelGluer(modTable, modCode);
        mg.run();
        return mg.getProduct();
    }

    public static boolean runNuXMV(String tableFilename, SMVModule... modules) {
        NuXMVAdapter adapter = new NuXMVAdapter(new File(tableFilename), modules);
        adapter.run();
        return adapter.isVerified();
    }
}
