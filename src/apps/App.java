package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.Parameters;

/**
 * Created by weigl on 18/01/15.
 */
public abstract class App {

    public String getCommandName() {
        Parameters p = this.getClass().getAnnotation(Parameters.class);
        return p.commandNames()[0];
    }

    public abstract void execute() throws Exception;
}
