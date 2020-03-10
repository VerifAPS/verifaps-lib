Synthesis Test Project
======================

This is a small, self-contained Gradle C++ project. `./gradlew` and `./gradlew.bat` have been edited to point to the
root project's Gradle wrapper.

You can import this directory in CLion, but you may need to manually point it to the correct Gradle installation inside
your `~/.gradle` directory by adjusting the project settings. If you're building on Windows, you may have to configure
the path to the VS build tools manually in `build.gradle`:

```groovy
model {
    toolChains {
        visualCpp(VisualCpp) {
            installDir "C:\\Program Files (x86)\\Microsoft Visual Studio\\2019\\BuildTools"
        }
    }
}
```