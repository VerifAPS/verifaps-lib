package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.IOException
import java.net.URISyntaxException
import java.net.URL
import java.nio.file.Path
import java.nio.file.Paths

fun createAst(file: Path): IEC61131Parser {
    val lexer = IEC61131Lexer(CharStreams.fromPath(file))
    val parser = IEC61131Parser(CommonTokenStream(lexer))
    return parser
}

fun createAst(file: URL) = createAst(Paths.get(file.toURI()))