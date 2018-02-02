/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 */
package edu.kit.iti.formal.automation.testtables.io;


import edu.kit.iti.formal.automation.testtables.exception.ProgramAbortionException;
import edu.kit.iti.formal.automation.testtables.report.Assignment;
import edu.kit.iti.formal.automation.testtables.report.Counterexample;
import edu.kit.iti.formal.automation.testtables.report.Message;
import edu.kit.iti.formal.automation.testtables.report.ObjectFactory;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (11.12.16)
 */
public class Report {
    public static boolean XML_MODE = false;
    static long START_TIME = System.currentTimeMillis();
    static Message msg;

    static {
        clear();
    }

    public static void clear() {
        msg = new Message();
        Message.Log log = new Message.Log();
        msg.setLog(log);
        msg.setReturncode("unknown");
    }

    public static void debug(String msg, Object... args) {
        print("debug", msg, args);
    }

    public static void info(String msg, Object... args) {
        print("info", msg, args);
    }

    public static void warn(String msg, Object... args) {
        print("warn", msg, args);
    }

    public static void error(String msg, Object... args) {
        print("error", msg, args);
    }

    public static void fatal(String msg, Object... args) {
        print("fatal", msg, args);
        setErrorLevel("fatal-error");
    }

    public static void abort() {
        throw new ProgramAbortionException();
    }

    private static void print(String level, String fmt, Object... args) {
        if (fmt == null) {
            return;//            throw new IllegalArgumentException("fmt is null");
        }
        Message.Log.Entry e = new Message.Log.Entry();
        e.setLevel(level);
        e.setTime((int) (System.currentTimeMillis() - START_TIME));
        e.setValue(String.format(fmt, args));
        msg.getLog().getEntry().add(e);
    }

    public static void setErrorLevel(String s) {
        msg.setReturncode(s);
    }

    public static void close() {
        if (!XML_MODE) {
            for (Message.Log.Entry e : msg.getLog().getEntry()) {
                System.out.printf("[%5d] (%5s): %s%n", e.getTime(), e.getLevel(), e.getValue());
            }

            int i = 0;
            if (msg.getCounterexample() != null) {
                for (Counterexample.Step step : msg.getCounterexample()
                        .getTrace().getStep()) {
                    System.out.format("STEP %d %n", i++);
                    step.getInput().forEach(Report.print("INPUT > "));
                    step.getState().forEach(Report.print("STATE > "));
                    System.out.println();
                }

                msg.getCounterexample().getRowMappings().getRowMap()
                        .forEach(rm -> {
                            System.out.println("ROWMAP > " + rm);
                        });
            }
            System.out.println("STATUS: " + msg.getReturncode());
        } else {
            try {
                JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
                Marshaller m = jaxbContext.createMarshaller();
                m.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);
                m.marshal(msg, System.out);
            } catch (JAXBException e) {
                e.printStackTrace();
            }
        }

    }

    private static Consumer<Assignment> print(String suffix) {
        return (Assignment assignment) -> {
            System.out.println(
                    suffix + "" + assignment.getName() + " = " + assignment
                            .getValue());
        };
    }

    public static void setCounterExample(Counterexample counterExample) {
        if (msg.getCounterexample() == null) {
            msg.setCounterexample(new Message.Counterexample());
        }
        msg.getCounterexample().setTrace(counterExample);
    }

    public static Message getMessage() {
        return msg;
    }
}
