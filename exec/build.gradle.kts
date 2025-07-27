plugins {
    id("application")
    id("kotlin-convention")
}

application {
    mainClass = "empty"
}

description = "Case Studies and Executables of VerifAPS"

dependencies {
    implementation(project(":symbex"))
    implementation(project(":geteta"))
    implementation(project(":aps-rvt"))
    implementation(project(":run"))
    implementation(project(":ide"))
    implementation(project(":stvs"))
    implementation(libs.clickt)
}

fun entrypoint(name: String, mc: String) {
    val startScripts by tasks.getting(CreateStartScripts::class)
    val t by tasks.register<CreateStartScripts>("createStart$name") {
        description = name
        group = "start-script"
        applicationName = name
        classpath = startScripts.classpath
        outputDir = startScripts.outputDir
        mainClass = mc

        (unixStartScriptGenerator as  TemplateBasedScriptGenerator).template =
            resources.text.fromFile("src/startScriptUnix.txt")

        (windowsStartScriptGenerator as  TemplateBasedScriptGenerator).template =
            resources.text.fromFile("src/startScriptWindows.txt")
    }

    // val applicationDistribution by tasks
    // println(applicationDistribution)
    application.applicationDistribution.from(t) { into("bin") }
    t.dependsOn(startScripts)
}

entrypoint("mod", "edu.kit.iti.formal.automation.rvt.modularization.ModApp")
entrypoint("kastel-demo", "edu.kit.iti.formal.automation.KastelDemonstrator")
entrypoint("sc12f", "edu.kit.iti.formal.automation.Sc12f")

// legacy name
entrypoint("sc11-rev", "edu.kit.iti.formal.automation.SC11_rev")
entrypoint("reteta", "edu.kit.iti.formal.automation.testtables.apps.RetetaApp")
entrypoint("geteta", "edu.kit.iti.formal.automation.testtables.apps.Geteta")
entrypoint("geteta-smt", "edu.kit.iti.formal.automation.testtables.apps.GetetaSmt")
entrypoint("ttver", "edu.kit.iti.formal.automation.testtables.apps.Geteta")
entrypoint("ttver-c", "edu.kit.iti.formal.automation.testtables.apps.GetetaSmt")
entrypoint("rttver", "edu.kit.iti.formal.automation.testtables.apps.RetetaApp")
entrypoint("ttprint", "edu.kit.iti.formal.automation.testtables.apps.Printer")
entrypoint("ttmonitor", "edu.kit.iti.formal.automation.testtables.apps.Monitor")
entrypoint("ttsynth", "edu.kit.iti.formal.automation.testtables.apps.Synthesis")
entrypoint("ttunwind", "edu.kit.iti.formal.automation.testtables.apps.UnwindODSApp")
entrypoint("ttcsv", "edu.kit.iti.formal.automation.testtables.apps.Csv")
entrypoint("ttcov", "edu.kit.iti.formal.automation.testtables.apps.Coverage")
entrypoint("rvt", "edu.kit.iti.formal.automation.rvt.RvtAps")
entrypoint("flycheck", "edu.kit.iti.formal.automation.Flycheck")
entrypoint("check", "edu.kit.iti.formal.automation.Check")
entrypoint("verifaps-versions", "edu.kit.iti.formal.util.Version")
entrypoint("st2cpp", "edu.kit.iti.formal.automation.ST2CppApp")
entrypoint("ide", "edu.kit.iti.formal.automation.fx.Main")
entrypoint("stvs", "edu.kit.iti.formal.stvs.Main")
entrypoint("smteta", "edu.kit.iti.formal.automation.testtables.apps.SMTeta")
entrypoint("xml2st", "edu.kit.iti.formal.automation.Xml2TxtApp")

application {
    applicationDistribution.duplicatesStrategy = DuplicatesStrategy.EXCLUDE
}

// Integration test requires the presence of the shell scripts
val test by tasks.getting
test.dependsOn(tasks.installDist)

val tmpTools = project.layout.buildDirectory.dir("tmp/tools").get().asFile.toPath()

val downloadNuxmvLinux by tasks.registering(Download::class) {
    source.set(uri("https://nuxmv.fbk.eu/theme/download.php?file=nuXmv-2.1.0-linux64.tar.xz"))
    outputFile.set(tmpTools.resolve("nuxmv-linux-64.tar.xz").toFile())
}

val nuxmvLinuxTar by tasks.registering(ExtractXz::class) {
    mustRunAfter(downloadNuxmvLinux.get())
    inputs.files(downloadNuxmvLinux.get())
    input.set(downloadNuxmvLinux.get().outputFile.get())
    output.set(tmpTools.resolve("nuxmv-linux-64.tar").toFile())
}

val downloadZ3Linux by tasks.registering(Download::class) {
    source.set(uri("https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-glibc-2.39.zip"))
    outputFile.set(tmpTools.resolve("z3-linux.zip").toFile())
}

val downloadZ3Win by tasks.registering(Download::class) {
    source.set(uri("https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-win.zip"))
    outputFile.set(tmpTools.resolve("tmp/z3-windows.zip").toFile())
}

val downloadZ3Macos by tasks.registering(Download::class) {
    source.set(uri("https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-win.zip"))
    outputFile.set(tmpTools.resolve("tmp/z3-windows.zip").toFile())
}

val downloadNuxmvWin by tasks.registering(Download::class) {
    source.set(uri("https://nuxmv.fbk.eu/theme/download.php?file=nuXmv-2.1.0-win64.7z"))
    outputFile.set(tmpTools.resolve("tmp/z3-windows.zip").toFile())
}

val downloadNuxmvMac by tasks.registering(Download::class) {
    source.set(uri("https://nuxmv.fbk.eu/theme/download.php?file=nuXmv-2.1.0-macos-universal.tar.xz"))
    outputFile.set(tmpTools.resolve("tmp/z3-windows.zip").toFile())
}

val nuxmvWinUnzip by tasks.registering(Extract7z::class) {
    dependsOn(downloadNuxmvWin)
    inputs.files(downloadNuxmvWin.get())
    input.set(downloadNuxmvWin.get().outputFile.get())
    output.set(tmpTools.resolve("nuxmv-windows").toFile())
}

val nuxmvMacosTar by tasks.registering(ExtractXz::class) {
    dependsOn(downloadNuxmvMac)
    inputs.files(downloadNuxmvMac.get())
    input.set(downloadNuxmvMac.get().outputFile.get())
    output.set(tmpTools.resolve("nuxmv-macos.tar").toFile())
}

val mainDist = distributions.getByName(DistributionPlugin.MAIN_DISTRIBUTION_NAME)

afterEvaluate {
    distributions {
        main {
            distributionBaseName = "verifaps"
            distributionClassifier = "universal"
            contents {
                from("$rootDir/README.md")
                from("$rootDir/LICENSE")
                into("examples") {
                    from("$rootDir/share")
                }
            }
        }

        create("linux") {
            distributionBaseName = "verifaps"
            distributionClassifier = "linux"
            contents {
                with(mainDist.contents)
                into("tools") {
                    from(zipTree(downloadZ3Linux.get().outputFile))
                    from(tarTree(nuxmvLinuxTar.get().output))
                }
                exclude {
                    it.name.endsWith("-windows.jar") ||
                        it.name.endsWith("-macos.jar")
                }
            }
        }

        create("windows") {
            distributionBaseName = "verifaps"
            distributionClassifier = "windows"
            contents {
                with(mainDist.contents)
                into("tools") {
                    from(zipTree(downloadZ3Win.get().outputFile))
                    from(fileTree(nuxmvWinUnzip.get().output))
                }
                into("examples") {
                    from("$rootDir/share")
                }
                exclude {
                    it.name.endsWith("-linux.jar") || it.name.endsWith("-macos.jar")
                }
            }
        }

        create("macos") {
            distributionBaseName = "verifaps"
            distributionClassifier = "macos"
            contents {
                with(mainDist.contents)
                into("tools") {
                    from(zipTree(downloadZ3Macos.get().outputFile))
                    from(tarTree(nuxmvMacosTar.get().output))
                }
                into("examples") {
                    from("$rootDir/share")
                }
                exclude {
                    it.name.endsWith("-windows.jar") ||
                        it.name.endsWith("-macos.jar")
                }
            }
        }
    }
}