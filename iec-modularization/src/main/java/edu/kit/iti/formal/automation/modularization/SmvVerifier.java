package edu.kit.iti.formal.automation.modularization;

/*-
 * #%L
 * iec-modularization
 * %%
 * Copyright (C) 2017 Alexander Weigl
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


import edu.kit.iti.formal.smv.ast.SMVModule;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.regex.Pattern;

public final class SmvVerifier {

	private static final Pattern _INVAR_TRUE       = Pattern.compile("true$");
	private static final Pattern _INVAR_FALSE      = Pattern.compile("false$");
	private static final Pattern _INVAR_LINE_STATE = Pattern.compile(
			"^-- invariant");
	private static final Pattern _INVAR_LINE_LTL   = Pattern.compile(
			"^-- LTL specification");
	
	private final NuXmvProcess _nuXmv = new NuXmvProcess();
	
	public SmvVerifier(final String nuXmvPath) {
		_nuXmv.setExecutablePath(nuXmvPath);
	}
	
	public final boolean verify(
			final String        fileName,
			final boolean       ltl,
			final SMVModule ... modules) {

		Logging.log("Writing proof to '" + fileName + ".smv'");

		String invarLine = null;
		
		_nuXmv.setModuleFile(fileName + ".smv");
		
		try(PrintWriter pw = new PrintWriter(_nuXmv.getModuleFile())) {
			for(SMVModule i : modules) pw.println(i.toString());
		} catch(IOException e) {}
		
		_nuXmv.run();

		try(PrintWriter pw = new PrintWriter(new File(_nuXmv.getWorkingDirectory(), fileName + ".txt"))) {
			for(String i : _nuXmv.getOutput()) pw.println(i);
		} catch(IOException e) {}

		final Pattern invarLinePattern =
				ltl ? _INVAR_LINE_LTL : _INVAR_LINE_STATE;
		for(String i : _nuXmv.getOutput()) {
			if(invarLinePattern.matcher(i).find()) {
				invarLine = i;
				break;
			}
		}
		
		if(invarLine == null)
			throw new NullPointerException("no invariant line found");
		
		if(_INVAR_TRUE .matcher(invarLine).find()) return true;
		if(_INVAR_FALSE.matcher(invarLine).find()) return false;
		
		throw new NullPointerException("couldn't parse invariant");
	}
}
