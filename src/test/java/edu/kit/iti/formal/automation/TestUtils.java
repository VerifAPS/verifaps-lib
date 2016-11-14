package edu.kit.iti.formal.automation;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 14.11.16.
 */
public class TestUtils {


    public static Iterable<Object[]> loadLines(String filename) throws IOException {
        List<Object[]> validExpression = new ArrayList<>(4096);
        InputStream ve = TestUtils.class.getResourceAsStream(filename);

        if (ve == null) {
            System.err.println("Could not find: " + filename);
            return validExpression;
        }

        BufferedReader stream = new BufferedReader(new InputStreamReader(ve));
        String tmp = "";
        while ((tmp = stream.readLine()) != null) {
            if (tmp.startsWith("#"))
                continue;
            validExpression.add(new Object[]{tmp});
        }

        System.out.println("Found: " + filename + " with " + validExpression.size() +" lines!");

        return validExpression;
    }

}
