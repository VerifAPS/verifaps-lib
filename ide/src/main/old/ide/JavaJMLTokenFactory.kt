package edu.kit.iti.formal.automation.ide

import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Recognizer
import org.fife.ui.rsyntaxtextarea.Token
import org.fife.ui.rsyntaxtextarea.TokenImpl
import org.fife.ui.rsyntaxtextarea.TokenMakerBase
import java.util.*
import javax.swing.text.Segment

/**
 * @author Alexander Weigl
 * @version 1 (22.05.19)
 */
class AntlrTokenMakerFactory(val lexerFactory: AntlrLexerFactory) : TokenMakerBase() {
    private val tokenMap = HashMap<Int, Int>()
    fun add(editorType: Int, vararg antlrTypes: Int) {
        for (antlrType in antlrTypes) {
            tokenMap[antlrType] = editorType
        }
    }

    protected fun rewriteTokenType(antlrType: Int) = antlrType// tokenMap[antlrType] ?: TokenTypes.ERROR_CHAR


    override fun getTokenList(text: Segment?, initialTokenType: Int, startOffset: Int): Token {
        var initTokType = initialTokenType
        val startTime = System.currentTimeMillis()
        resetTokenList()
        requireNotNull(text)

        val charSeq = text.toString()
        val lexer = lexerFactory.create(charSeq)

        //initialTokenType contains the list of mode stack of the lexer
        var mode = initTokType and 0xF //using four bits for lexer mode
        lexer._mode = mode
        initTokType = initTokType shr 4
        while (initTokType > 0) {
            mode = initTokType and 0xF //using four bits for lexer mode
            lexer.pushMode(mode)
            initTokType = initTokType shr 4
        }

        val tokens = ArrayList<org.antlr.v4.runtime.Token>()
        val modes = ArrayList<Int>()
        var cur = lexer.nextToken()
        while (cur.type != Recognizer.EOF) {
            //System.out.format("%25s %-25s%n", cur.getText(), lexer.getVocabulary().getSymbolicName(cur.getType()));
            modes.add(lexer._mode)
            tokens.add(cur)
            cur = lexer.nextToken()
        }

        //Handling of unfinished token, a token sequence with ANTLR `more` action
        if (cur.type == Recognizer.EOF && cur.stopIndex - cur.startIndex > 0) {
            changeType(lexer, cur)
            if (cur.type != org.antlr.v4.runtime.Token.EOF) {
                modes.add(lexer._mode)
                tokens.add(cur)
            }
        }

        if (tokens.size == 0) {
            currentToken = TokenImpl(text,
                    text.offset,
                    text.offset,
                    startOffset, 0, 0)

            val token = object : TokenImpl() {
                override fun isPaintable(): Boolean {
                    return false
                }
            }
            token.text = null
            token.offset = -1
            token.nextToken = null
            token.type = initialTokenType
            currentToken.nextToken=token
            return currentToken
        } else {
            mode = 0
            // skip last artificial '\n' token
            for (i in tokens.indices) {
                val token = tokens[i]
                mode = modes[i]
                val newType = rewriteTokenType(token.type)
                val start = token.startIndex
                val t = TokenImpl(text,
                        text.offset + start,
                        text.offset + start + token.text.length - 1,
                        startOffset + start, newType, 0)
                t.languageIndex = mode
                if (firstToken == null) {
                    firstToken = t
                    currentToken = t
                } else {
                    assert(currentToken != null)
                    currentToken.setNextToken(t)
                }
                currentToken = t
            }

            var tokenType = 0xF and simulateNewLine(lexer)//current mode is not on stack
            while (lexer._modeStack.size() > 0) {
                tokenType = tokenType shl 4 or (0xF and lexer._modeStack.pop())
            }

            val token = object : TokenImpl() {
                override fun isPaintable(): Boolean {
                    return false
                }
            }
            token.text = null
            token.offset = -1
            token.nextToken = null
            token.type = tokenType
            currentToken.setNextToken(token)
        }

        val stop = System.currentTimeMillis()
        //println("JavaJMLTokenFactory.getTokenList : " + (stop - startTime) + " ms")
        return firstToken
    }

    protected fun changeType(lexer: Lexer, cur: org.antlr.v4.runtime.Token) {}

    protected fun simulateNewLine(l: Lexer): Int = l._mode
}
