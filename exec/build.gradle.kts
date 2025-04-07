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
    }

    //val applicationDistribution by tasks
    //println(applicationDistribution)
    application.applicationDistribution.from(t) { into("bin") }
    t.dependsOn(startScripts)
}

entrypoint("mod", "edu.kit.iti.formal.automation.rvt.modularization.ModApp")
entrypoint("kastel-demo", "edu.kit.iti.formal.automation.KastelDemonstrator")
entrypoint("sc12f", "edu.kit.iti.formal.automation.Sc12f")

//legacy name
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