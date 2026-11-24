## Build & Toolchain
- Gradle (Kotlin DSL) via the wrapper: always use `./gradlew`.
- JDK **21** pinned by `jvmToolchain(21)`; no toolchain auto-provisioning is configured, local JDK is required
- Dependency defined in `gradle/libs.versions.toml`

## Commands
| Task | Command |
|------|---------|
| Compile all tests | `./gradlew testClasses` |
| Run unit tests (skip integration) | `./gradlew test -x :exec:test` |
| Run full `check` | `./gradlew check` |
| Build CLI executables | `./gradlew :exec:installDist` |
| Format / verify format | `./gradlew spotlessApply` / `./gradlew spotlessCheck` |
| Generate API docs | `./gradlew dokkaGenerate` |

- Executables land in `exec/build/install/exec/bin/`.
- `check` also runs `:exec:test` (integration), which needs `nuXmv` and `z3`; use `-x :exec:test` for a solver-free run.
- CI runs `spotlessCheck` separately; the test job runs `testClasses` → `test -x :exec:test` → `assemble` → `:exec:test`.

## Single Test
```sh
./gradlew :lang:test --tests "edu.kit.iti.formal.automation.SomeTest"
./gradlew :symbex:test --tests "edu.kit.iti.formal.automation.SomeTest.someMethod"
```

## Integration Tests (`:exec:test`)
- Depends on `:exec:installDist` and invokes the generated scripts from `exec/build/install/exec/bin/`.
- Needs `nuXmv` via `NUXMV` env var, on `PATH`, or at `$HOME/share/nuXmv-2.1.0-linux64/bin/nuXmv`; needs `z3` on `PATH`.
- The `linux`/`windows`/`macos` distributions bundle `tools/` and export `NUXMV`/`Z3`; plain `installDist` does not.

## Architecture
- `lang` (Structured Text/SFC AST + ANTLR parser) is the core; `xml` (PLCopenXML), `smv` (SMV/nuXmv) and `smt` (SMT-LIB) are lower-level modules.
- `symbex` (symbolic execution, depends on `lang`/`smv`/`smt`) feeds `run` (interpreter), `aps-rvt` (regression verification), and `geteta` (generalized test tables).
- `stvs`, `ide`, `fxutils` are JavaFX GUI modules. `exec` aggregates all apps; CLI entrypoints are registered with `entrypoint(name, mainClass)` in `exec/build.gradle.kts`.
- `web-backend` is commented out in `settings.gradle.kts` and is not built.
- Kotlin/Java base package is `edu.kit.iti.formal.automation` (plus `...util`, `...smv`, `...smt`, `...stvs`).

## Generated Code
- ANTLR grammars live in `*/src/main/antlr` (`lang`, `geteta`, `smv`, `smt`). Generated parsers go into `build/` and are wired into compile tasks — never edit generated sources.

## Conventions
- Spotless (ktlint via `.editorconfig`) enforces the GPL-3.0-or-later license header on every Kotlin file; run `spotlessApply` instead of hand-formatting.
- Tests JUnit 6. Several tests are intentionally excluded or tagged/disabled in module build files (e.g. `geteta`, `lang`, `stvs`); don't remove those exclusions.
- Per-module notes: `README.md`, `run/Module.md`, `geteta/README.md`, `lang/README.md`, `stvs/CONTRIBUTING.md`. Some are stale (e.g. Maven instructions), so trust `build.gradle.kts` over prose.