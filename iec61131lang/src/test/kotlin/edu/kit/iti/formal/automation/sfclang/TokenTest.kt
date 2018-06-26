package edu.kit.iti.formal.automation.sfclang

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import org.antlr.v4.runtime.ANTLRInputStream
import org.junit.Test

/**
 * Created by weigl on 07.02.16.
 */
class TokenTest {
    @Test
    fun sfcTok() {
        val lexer = IEC61131Lexer(ANTLRInputStream("SFC"))
        for (t in lexer.allTokens) {
            //System.out.println(t.getType());
        }
    }
}
