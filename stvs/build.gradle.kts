import java.io.ByteArrayOutputStream

plugins {
    id("kotlin-convention")
    id("application")
    id("org.openjfx.javafxplugin") version "0.1.0"
}

version = "1.5.0-beta"

repositories {
    // try to resolve by pom first
    mavenCentral {
        metadataSources {
            mavenPom()
        }
    }
    // try to get artifacts if no useful pom is found
    mavenCentral {
        metadataSources {
            artifact()
        }
    }
    // Ivy can be used as well
    ivy {
        url = uri("https://www.sosy-lab.org/ivy")
        patternLayout {
            artifact("/[organisation]/[module]/[classifier]-[revision].[ext]")
            ivy("/[organisation]/[module]/ivy-[revision].xml")
        }
        metadataSources {
            artifact()
        }
    }
}



dependencies {
    implementation(project(":lang"))
    implementation(project(":geteta"))

    implementation("org.sosy-lab:java-smt:5.0.1")
    val z3Version = "4.13.4"
    //javasmt-solver-z3-4.13.4-libz3-x64.dll
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3-x64@dll")
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java-x64@dll")
    //javasmt-solver-z3-4.13.4.jar
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version")


    implementation(libs.jdom)
    implementation("jaxen:jaxen:2.0.0")

    implementation("com.google.code.gson:gson:2.12.1")

    implementation("org.fxmisc.cssfx:cssfx:11.2.2")
    implementation(project(":fxutils"))
}

fun getVersionName(): String {
    val stdout = ByteArrayOutputStream()
    exec {
        commandLine = listOf("git", "rev-parse", "--short", "HEAD")
        standardOutput = stdout
    }
    return stdout.toString().trim()
}

application { mainClass = "edu.kit.iti.formal.stvs.StvsApplication" }

/*ext.sharedManifest = manifest {
    attributes(
        "Implementation-Title" to "StructuredText Verification Studio (stvs)",
        "Implementation-Version" to version,
        "Specification-Version" to getVersionName(),
        "Main-Class" to mainClassName
    )
}*/

tasks.named<Test>("test") {
    useJUnitPlatform() {
        excludeTags("performance", "demo", "random")
    }
}

tasks.register<Test>("guiTest") {
    /*filter {
        //includeTestsMatching "edu.kit.iti.formal.stvs.view.*"
    }
    useJUnitPlatform {
        exclude "edu.kit.iti.formal.stvs.Demo"
        exclude "edu.kit.iti.formal.stvs.Performance"
    }*/
}

//compileKotlin.dependsOn("generateGrammarSource")
//compileTestKotlin.dependsOn("generateTestGrammarSource")


// coverage
//cobertura.coverageFormats = ["html", "xml"] // coveralls plugin depends on xml format report
