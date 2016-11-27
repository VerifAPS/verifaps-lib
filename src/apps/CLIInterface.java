package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.JCommander;

/**
 * Created by weigl on 18/01/15.
 */
public class CLIInterface {

    public static final void main(String args[]) throws Exception {
        CLIInterface cli = new CLIInterface();
        JCommander jc = new JCommander(cli);

        App[] apps = new App[]{
                new AstViewer(),
                new FiPhi(),
                new STSimplify(),
                new SfcApp(),
                new ShowParserTree(),
                new ST2PY(),
                new Transformer(),
                new TransformPCLOpenXMLToSFCLang()
        };

        for (App app : apps) {
            jc.addCommand(app);
        }

        jc.parse(args);

        for (App app : apps) {
            if (app.getCommandName().equals(jc.getParsedCommand())) {
                app.execute();
                return;
            }
        }

        jc.usage();

        return;
    }
}
