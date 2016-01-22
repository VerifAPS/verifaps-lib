package edu.kit.iti.formal.automation.util;

import java.io.IOException;
import java.io.Writer;
import java.util.Stack;

/**
 * @author weigla
 * @date 15.06.2014
 */
public class CodeFileWriter {
    private Writer fw;

    private String ident = "    ";
    private int identDepth = 0;
    private int lastSeperatorInsertPosition;
    private Stack<Boolean> lastIsDiv = new Stack<>();


    public CodeFileWriter(Writer fw) {
        this.fw = fw;
    }


    public CodeFileWriter appendIdent() throws IOException {
        for (int i = 0; i < identDepth; i++) {
            fw.write(ident);
        }
        return this;
    }

    public CodeFileWriter increaseIdent() {
        identDepth++;
        return this;
    }

    public CodeFileWriter decreaseIdent() {
        identDepth--;
        return this;
    }

    public CodeFileWriter nl() throws IOException {
        fw.write("\n");
        appendIdent();
        return this;
    }

    public CodeFileWriter append(Object obj) throws IOException {
        fw.write(obj.toString());
        return this;
    }

    public CodeFileWriter append(String obj) throws IOException {
        fw.write(obj);
        return this;
    }

    public CodeFileWriter append(float f) throws IOException {
        fw.write(String.valueOf(f));
        return this;
    }


    public CodeFileWriter append(double d) throws IOException {
        fw.write(String.valueOf(d));
        return this;
    }

    public CodeFileWriter append(char[] str) throws IOException {
        fw.write(str);
        return this;
    }

    public CodeFileWriter append(char[] str, int offset, int len) throws IOException {
        fw.write(str, offset, len);
        return this;
    }
}
