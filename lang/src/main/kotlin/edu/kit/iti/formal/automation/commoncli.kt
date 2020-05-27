package edu.kit.iti.formal.automation

import com.github.ajalt.clikt.core.ParameterHolder
import com.github.ajalt.clikt.parameters.groups.OptionGroup
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.util.currentDebugLevel
import kotlin.system.exitProcess

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/11/20)
 */
class ProgramOptions : OptionGroup("options for handling programs") {
    fun readProgram(): PouExecutable {
        val pous = IEC61131Facade.readProgramsWLPN(library, program)
        require(pous.isNotEmpty()) { "No program was given" }
        val exec = pous.first()
        require(exec != null) { "Could not find any program by ${program.first()}" }
        return exec
    }

    fun readPrograms(): List<PouExecutable> {
        val pous = IEC61131Facade.readProgramsWLPN(library, program)
        require(pous.isNotEmpty()) { "No program was given" }
        val exec = pous.first()
        require(exec != null) { "Could not find any program by ${program.first()}" }
        return pous.filterNotNull()
    }

    val library by option("-L", "--library", help = "library files").file().multiple()

    val program by option("-P", "--program", "-c", help = "program files")
            .multiple(required = true)

    val disableSimplify by option("--no-simplify", help = "disable")
            .flag("--simplify", default = false)
}

class CommonArguments() : OptionGroup() {
    fun enableVerbosity() {
        if(verbose)
            currentDebugLevel = 3
    }

    fun showVersion() {
        if (version) {
            val urls = javaClass.classLoader.getResource("META-INF/version.property")
            urls?.openStream()?.use {
                it.transferTo(System.out)
            }
        }
        exitProcess(0)
    }

    operator fun invoke() {
        enableVerbosity()
        showVersion()
    }

    val verbose by option("--verbose").flag()
    val version by option("--version").flag()
}

fun ParameterHolder.nuxmv() =
        option("--nuxmv",
                help = "Path to nuXmv binary. You can also set the environment variable \$NUXMV",
                envvar = "NUXMV")
                .default("nuXmv")

fun ParameterHolder.dryRun() =
        option("--model-check", help = "the model checker is invoked when set [default:true]")
                .flag("--dont-model-check", "--dry-run", default = true)

fun ParameterHolder.outputFolder() = option("-o", "--output", help = "Output directory")
