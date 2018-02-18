package edu.kit.iti.formal.automation.parser;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2018 Alexander Weigl
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

import com.google.common.base.Strings;
import lombok.*;
import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (18.02.18)
 */
public class ErrorReporter extends BaseErrorListener {
    @Getter
    @Setter
    private boolean print = true;
    @Getter
    private List<SyntaxError> errors = new ArrayList<>();

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line,
                            int charPositionInLine, String msg, RecognitionException e) {
        SyntaxError.SyntaxErrorBuilder se = SyntaxError.builder();
        se.recognizer = recognizer;
        se.offendingSymbol = (Token) offendingSymbol;
        se.source = se.offendingSymbol.getTokenSource().getSourceName();
        se.line = line;
        se.charPositionInLine = charPositionInLine;
        se.msg = msg;
        if (print) {
            System.err.printf("[syntax-error] %s:%d%d: %s%n", se.source, line, charPositionInLine, msg);
        }
        errors.add(se.build());
    }

    public boolean hasErrors() {
        return !errors.isEmpty();
    }

    public void throwException() throws IEC61131ParserException {
        if (hasErrors()) throw new IEC61131ParserException(Collections.unmodifiableList(errors));
    }

    public void throwException(String[] lines) throws IEC61131ParserException {
        if (hasErrors()) {
            String msg = errors.stream().map(se -> se.getBeatifulErrorMessage(lines)).collect(Collectors.joining("\n---\n"));
            throw new IEC61131ParserException(
                    msg,
                    Collections.unmodifiableList(errors));
        }
    }

    public void throwException(Supplier<String[]> lines) throws IEC61131ParserException {
        if (hasErrors()) {
            throwException(lines.get());
        }
    }

    @Value
    @Builder
    private static class SyntaxError {
        @NotNull
        private Recognizer<?, ?> recognizer;
        @NotNull
        private Token offendingSymbol;
        private int line;
        private int charPositionInLine;
        @NotNull
        private String msg;
        private String source;

        public String getBeatifulErrorMessage(String[] lines) {
            return "syntax-error in " + positionAsUrl() + "\n"
                    + msg + "\n" + showInInput(lines) + "\n";
        }

        public String showInInput(String[] lines) {
            String line = lines[this.line];
            StringBuilder sb = new StringBuilder();
            sb.append(line)
                    .append("\n")
                    .append(Strings.repeat(" ", charPositionInLine - 1))
                    .append(Strings.repeat("^", offendingSymbol.getText().length()))
            ;
            return sb.toString();
        }

        public String positionAsUrl() {
            return String.format("file://source:%d", line);
        }
    }


    @Getter
    @RequiredArgsConstructor
    public static class IEC61131ParserException extends RuntimeException {
        private final List<SyntaxError> errors;

        public IEC61131ParserException(String msg, List<SyntaxError> ts) {
            super(msg);
            errors = ts;
        }

        public String print(String[] lines, CharSequence delimter) {
            String msg = errors.stream().map(se -> se.getBeatifulErrorMessage(lines))
                    .collect(Collectors.joining(delimter));
            return msg;
        }
    }
}
