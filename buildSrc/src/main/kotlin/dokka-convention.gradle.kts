plugins {
    id("org.jetbrains.dokka")
}


/*
dokka {
    moduleName.set("Project Name")
    /*dokkaSourceSets.main {
        includes.from("README.md")
        sourceLink {
            localDirectory.set(file("src/main/kotlin"))
            remoteUrl("https://github.com/verifaps/verifaps-lib/blob/")
            remoteLineSuffix.set("#L")
        }
    }*/
    pluginsConfiguration.html {
        //customStyleSheets.from("styles.css")
        //customAssets.from("logo.png")
        //footerMessage.set("(c) Your Company")
    }
}
*/