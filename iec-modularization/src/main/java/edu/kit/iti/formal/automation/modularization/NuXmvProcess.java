package edu.kit.iti.formal.automation.modularization;

import java.io.BufferedReader;

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.LinkedList;
import java.util.List;

public final class NuXmvProcess implements Runnable {
	
	private String   _executablePath   = null;
	private String[] _output           = null;
	private File     _workingDirectory = new File(".");
	private File     _commandFile      = null;
	private File     _moduleFile       = null;
	
	public final String getExecutablePath() {
		return _executablePath;
	}
	
	public final File getModuleFile() {
		return _moduleFile;
	}
	
	public final String[] getOutput() {
		return _output;
	}
	
	public final File getWorkingDirectory() {
		return _workingDirectory;
	}
	
	@Override
	public final void run() {
		
		if(_moduleFile == null)
			throw new NullPointerException("No module file specified");
		
		if(_workingDirectory == null) setWorkingDirectory(".");
		if(_commandFile      == null) setCommandFile     ("ic3.xmv");
		
		_workingDirectory.mkdirs();
		
		final String[] commands = new String[]{
			_executablePath,
			"-source",
			_commandFile.getAbsolutePath(),
			_moduleFile.getAbsolutePath()};

		try {
			
			final PrintWriter pw = new PrintWriter(_commandFile);
			
			pw.println("read_model");
			pw.println("flatten_hierarchy");
			pw.println("show_vars");
			pw.println("encode_variables");
			pw.println("build_boolean_model");
			pw.println("check_invar_ic3");
			pw.println("check_ltlspec_klive");
			pw.println("quit");
			
			pw.close();
			
		} catch(FileNotFoundException e) {}
		
		try {
			
			final ProcessBuilder pb = new ProcessBuilder(commands).
				directory          (_workingDirectory).
				redirectErrorStream(true);
			
			final Process p = pb.start();
			
			// Ensure process is terminated if application is closed
			Runtime.getRuntime().addShutdownHook(
				new Thread(() -> p.destroyForcibly()));
			
			final BufferedReader br    =
				new BufferedReader(new InputStreamReader(p.getInputStream()));
			final List<String>   lines = new LinkedList<>();
			
			String line;
			while((line = br.readLine()) != null)
				if(!line.isEmpty()) lines.add(line);
			_output = lines.toArray(new String[lines.size()]);
			
			p.waitFor();
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public final NuXmvProcess setExecutablePath(final String executablePath) {
		_executablePath = executablePath;
		return this;
	}

	public final NuXmvProcess setCommandFile(final String path) {
		return setCommandFile(new File(_workingDirectory, path));
	}

	public final NuXmvProcess setCommandFile(final File file) {
		_commandFile = file;
		return this;
	}
	
	public NuXmvProcess setModuleFile(final String path) {
		return setModuleFile(new File(_workingDirectory, path));
	}

	public final NuXmvProcess setModuleFile(final File moduleFile) {
		_moduleFile = moduleFile;
		return this;
	}

	public final NuXmvProcess setWorkingDirectory(final String path) {
		return setWorkingDirectory(new File(path));
	}
	
	public final NuXmvProcess setWorkingDirectory(final File workingDirectory) {
		_workingDirectory = workingDirectory;
		return this;
	}
}
