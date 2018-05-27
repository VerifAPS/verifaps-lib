package edu.kit.iti.formal.automation.st;

/*-
 * #%L
 * iec61131lang
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

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.Vocabulary;
import org.junit.Assert;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (28.06.17)
 */
public class CommentTests {
    @Test
    public void oneAndStuff() {
        String s = "(* aff *) dsfsaf *)";
        IEC61131Lexer l = new IEC61131Lexer(CharStreams.fromString(s));
        List<? extends Token> toks = l.getAllTokens();
        Vocabulary v = l.getVocabulary();
        List<String> names = toks.stream().map(t -> v.getSymbolicName(t.getType())).collect(Collectors.toList());

        Assert.assertEquals(Arrays.asList(
                "COMMENT", "WS", "IDENTIFIER", "WS", "MULT", "RPAREN"
        ), names);
        Assert.assertEquals(6, toks.size());
    }


    @Test
    public void mlSLmix() {
        String s = "(* \n//abc *)";
        IEC61131Lexer l = new IEC61131Lexer(CharStreams.fromString(s));
        List<? extends Token> toks = l.getAllTokens();
        Vocabulary v = l.getVocabulary();
        List<String> names = toks.stream().map(t -> v.getSymbolicName(t.getType())).collect(Collectors.toList());

        Assert.assertEquals("COMMENT", names.get(0));
        Assert.assertEquals(1, toks.size());
    }


}
