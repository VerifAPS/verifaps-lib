package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import edu.kit.iti.formal.automation.sfclang.PCLOpenXmlIntoSFCLang;
import edu.kit.iti.formal.automation.sfclang.SFCLangPrinter;
import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCFactory;
import edu.kit.iti.formal.automation.st.plcopenxml.model.SFCGraph;
import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 12.09.15.
 */
@Parameters(commandNames = "xml2sfc",
        separators = "=",
        commandDescription = "")
public class TransformPCLOpenXMLToSFCLang extends App {
    @Parameter(names = "files")
    public List<String> inputFiles = new ArrayList<>();

    public static void main(String[] args) throws IOException {
        TransformPCLOpenXMLToSFCLang app = new TransformPCLOpenXMLToSFCLang();
        new JCommander(app, args);
        app.execute();
    }

    public void execute() throws IOException {
        for (String inputFile : inputFiles) {
            File input = new File(inputFile);

            List<SFCGraph> sfcs = SFCFactory.sfcToGraph(input);

            for (SFCGraph sfc : sfcs) {
                PCLOpenXmlIntoSFCLang builder = new PCLOpenXmlIntoSFCLang(sfc);
                SFCDeclaration decl = builder.getDeclaration();
                String sfcstring = SFCLangPrinter.print(decl);
                File output = new File(input.getParentFile(),
                        FilenameUtils.removeExtension(inputFile) + "_" + decl.getName() + ".sfclang");
                FileUtils.writeStringToFile(output, sfcstring);
            }
        }
    }
}
