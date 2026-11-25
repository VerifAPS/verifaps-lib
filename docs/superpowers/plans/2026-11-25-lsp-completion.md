# VerifAPS LSP Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Finish the `:lsp` module so it serves Structured Text, SMV, and Generalized Test Tables (GTT) with correct LSP capabilities, push diagnostics, semantic tokens, folding ranges, tests, and updated dependencies on branch `weigl/lsp`.

**Architecture:** A shared `FileAntlrManager` caches parse trees and publishes diagnostics; each language supplies a `TextDocumentService`, `WorkspaceService`, `Highlighter`, and folding registrations. `Main` selects the server from `--language`. A capability is advertised only when the corresponding request is implemented. Diagnostics are pushed from `didOpen`/`didChange`/`didSave` (no pull-diagnostics).

**Tech Stack:** Kotlin 2.4.21, Gradle 9.9.2 (wrapper), JDK 21, lsp4j 1.0.0, ANTLR 4.13.2, JUnit 6, existing `lang`/`smv`/`geteta` parsers.

**Spec:** PR #211 (“Add LSP support for Structured Text, SMV, and GTT”) plus the gap audit captured by the tasks below.

## Global Constraints

- Work on `weigl/lsp` in the existing worktree `/tmp/opencode/verifaps-lsp`; do not change `master`.
- LSP positions are 0-based; ANTLR `line` is 1-based and `charPositionInLine` is 0-based.
- Only advertise implemented capabilities. Remove or implement advertised-but-missing features.
- Diagnostics are pushed (`textDocument/publishDiagnostics`) on open/change/save; do not advertise `diagnosticProvider`.
- Use the existing parsers: `IEC61131Facade.getParser`, `SMVFacade.getParser`, `GetetaFacade.createParser`.
- Every task ends with `spotlessApply`, the listed focused test command, and a commit.
- Keep SonarCloud’s new duplication < 3% and add no new reliability bugs.
- JDK: `JAVA_HOME="$HOME/.sdkman/candidates/java/21.0.13.0+9-tem"`; commands use `./gradlew`.

## Review Focus

1. **Multi-line tokens in semantic tokens** — block comments/strings must be split per line; otherwise the 5-int delta encoding is invalid. Covered by `HighlighterTest`.
2. **Folding ranges on leaf and nested contexts** — `ParserRuleContext.children` can be null, and ANTLR lines must be converted to 0-based. Covered by `FoldingRangeHelperTest`.
3. **Syntax errors during `didOpen`/`didChange`/`didSave`** — must publish diagnostics and not escape the LSP handler. Covered by `FileAntlrManagerTest`.
4. **Document selectors and capabilities** — `.st`, `.smv`, `.gtt` selectors and capabilities must match implemented requests. Covered by each `*LanguageServerTest`.
5. **Empty/short files and EOF tokens** — no invalid or off-by-one ranges. Covered by `*TextDocumentServiceTest`.

---

### Task 1: Apply dependency updates on `weigl/lsp`

**Files:**
- Modify: `buildSrc/src/main/kotlin/kotlin-convention.gradle.kts` (jacoco, kotlin-test-junit)
- Modify: `buildSrc/src/main/kotlin/dokka-convention.gradle.kts`
- Modify: `xml/build.gradle`
- Modify: `fxutils/build.gradle.kts`
- Modify: `stvs/build.gradle.kts`

**Interfaces:**
- Consumes: none.
- Produces: the versions used by all later tasks; no API changes.

- [ ] **Step 1: Apply the validated stable versions**

Set exactly:
- `jacoco { toolVersion = "0.8.16" }`
- `testImplementation("org.jetbrains.kotlin:kotlin-test-junit:2.4.21")`
- `dokkaPlugin("org.jetbrains.dokka:mathjax-plugin:2.3.0")`
- `xml`: `jaxen:jaxen:2.0.6`, `com.fasterxml.jackson.core:jackson-databind:2.23.0`
- `fxutils`: JavaFX version `22.0.2` in both the `javafx {}` block and `org.openjfx:$module:22.0.2:$classifier`
- `stvs`: `org.sosy-lab:java-smt:5.0.1-990-g2a1205c7f`, `z3Version = "4.17.0-1009b13"`

- [ ] **Step 2: Run the affected modules**

Run: `./gradlew :xml:test :fxutils:compileKotlin :stvs:test --console=plain`
Expected: `BUILD SUCCESSFUL`. (This combination was already verified locally; the solver classifiers resolve from Maven Central.)

- [ ] **Step 3: Format and commit**

Run: `./gradlew spotlessCheck --console=plain`
Commit: `build: update dependencies (jacoco, dokka, jackson, jaxen, javafx, java-smt, z3)`

---

### Task 2: Shared LSP utilities and semantic tokens

**Files:**
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/util.kt`
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/Highlighter.kt`
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/FoldingRangeHelper.kt`
- Create: `lsp/src/test/kotlin/edu/kit/iti/formal/lsp/UtilTest.kt`
- Create: `lsp/src/test/kotlin/edu/kit/iti/formal/lsp/FoldingRangeHelperTest.kt`
- Create: `lsp/src/test/kotlin/edu/kit/iti/formal/lsp/HighlighterTest.kt`

**Interfaces:**
- Consumes: `org.eclipse.lsp4j.Position`, `Range`, `Diagnostic`, `FoldingRange`, `SemanticTokens`.
- Produces:
  - `internal fun String.substring(start: Position, end: Position): String` — offsets a position from the start of its line.
  - `internal fun SyntaxErrorReporter.ParserException.toDiagnostics(): List<Diagnostic>` — one error diagnostic per parse error; range from `line`/`charPositionInLine` and `offendingSymbol.text.length`.
  - `fun ParseCancellationException.toDiagnostics(): List<Diagnostic>` — parse `line (\d+):(\d+)` from `message`; fall back to `(0,0)`.
  - `fun Highlighter.analyzeText(text: String): SemanticTokens` — split tokens that span lines.
  - `open class FoldingRangeHelper` — `foldingRange()` returns 0-based `FoldingRange` values.

- [ ] **Step 1: Write the failing tests**

```kotlin
// UtilTest
@Test fun `substring uses the line start, not the newline index`() {
    assertEquals("b", "a\nbc".substring(Position(1, 1), Position(1, 2)))
}
@Test fun `parser diagnostics are 0-based and cover the token`() {
    // construct SyntaxErrorReporter.SyntaxError(line = 2, charPositionInLine = 3, msg = "x", offendingSymbol = token("abc"))
    // assert Diagnostic.range.start == Position(1, 3) and end == Position(1, 6)
}
@Test fun `parse cancellation extracts line and column`() {
    val d = ParseCancellationException("line 3:4 mismatched input").toDiagnostics().single()
    assertEquals(Position(2, 4), d.range.start)
}
```

```kotlin
// FoldingRangeHelperTest
@Test fun `folding ranges are zero based and skip single lines`() {
    val helper = FoldingRangeHelper()
    val ctx = object : ParserRuleContext() {}
    ctx.start = CommonToken(0).apply { line = 1 }
    ctx.stop = CommonToken(0).apply { line = 3 }
    helper.registerFoldingContext(ctx.javaClass) { "TEST" }
    val ranges = CompletableFuture.completedFuture(ctx).foldingRange().get()
    assertEquals(listOf(FoldingRange(0, 2)), ranges)
}
```

```kotlin
// HighlighterTest
@Test fun `a multi line block comment is split into one token per line`() {
    // fake lexer returns one COMMENT token whose text is "/* a\nb */"
    // assert SemanticTokens data has two entries (lines 0 and 1), second column 0
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `./gradlew :lsp:test --tests '*UtilTest' --tests '*FoldingRangeHelperTest' --tests '*HighlighterTest' --console=plain`
Expected: FAIL (assertions or missing behavior).

- [ ] **Step 3: Implement the utilities**

`String.substring(Position, Position)`:
- Walk the string once, recording the offset of the start of each line.
- Return `substring(lineStart(start.line) + start.character, lineStart(end.line) + end.character)`.
- Order the two offsets with `min`/`max`.

`ParserException.toDiagnostics()`:
- `line = error.line - 1`, `column = error.charPositionInLine`, `end = column + (error.offendingSymbol?.text?.length ?: 1)`.
- Message: `error.msg ?: ""`.

`ParseCancellationException.toDiagnostics()`:
- `Regex("line (\\d+):(\\d+)")`; if found, `Position(line - 1, column)`, else `Position(0, 0)`.
- Range end is `start + 1` on the same line.

`Highlighter.analyzeText`:
- For each token, split `token.text` on `\n`.
- Emit a semantic token for each non-empty segment:
  - first segment: `line = token.line - 1`, `column = token.charPositionInLine`
  - later segments: `line = token.line - 1 + segmentIndex`, `column = 0`
  - length = segment length.
- Skip tokens with `tokenType(token) == null`.

`FoldingRangeHelper`:
- Use `FoldingRange(n.start.line - 1, n.stop.line - 1)`.
- Replace `n.children` with `n.children?.filterIsInstance<ParserRuleContext>() ?: emptyList()`.

- [ ] **Step 4: Run the tests to verify they pass**

Run the same command as Step 2.
Expected: PASS.

- [ ] **Step 5: Format and commit**

Run: `./gradlew spotlessApply`
Commit: `fix(lsp): correct positions, diagnostics, folding, and semantic token encoding`

---

### Task 3: `FileAntlrManager` diagnostics lifecycle

**Files:**
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/FileAntlrManager.kt`
- Create: `lsp/src/test/kotlin/edu/kit/iti/formal/lsp/FileAntlrManagerTest.kt`

**Interfaces:**
- Consumes: `SyntaxErrorReporter.ParserException.toDiagnostics()`, `ParseCancellationException.toDiagnostics()`.
- Produces:
  - `protected open fun publishDiagnostics(params: PublishDiagnosticsParams)` — default delegates to `server.client.publishDiagnostics`.
  - `didOpen`, `didChange`, `didSave` parse and publish; `didClose` clears `fileCache` and `fileErrors`.
  - `fun getSync(uri: String): T` remains the cached parse entry point.

- [ ] **Step 1: Write the failing test**

```kotlin
class FileAntlrManagerTest {
    @Test fun `didOpen publishes an empty diagnostic list for valid ST`() {
        // temp .st file with "PROGRAM P END_PROGRAM"
        // manager.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "st", 1, text)))
        // assert captured params.diagnostics.isEmpty()
    }
    @Test fun `didOpen publishes diagnostics for a syntax error`() {
        // temp .st file with "PROGRAM"
        // assert captured params.diagnostics.isNotEmpty()
    }
    @Test fun `didClose removes the cached tree and errors`() {
        // open, close, reopen a changed file; assert the new tree is used
    }
}
```

Use a test subclass of `FileAntlrManager<IEC61131Parser.StartContext>` with:
- `parse(x) = IEC61131Facade.getParser(x).also { it.errorReporter.throwException() }.start()`
- overridden `publishDiagnostics` capturing the last `PublishDiagnosticsParams`.

- [ ] **Step 2: Run the test to verify it fails**

Run: `./gradlew :lsp:test --tests '*FileAntlrManagerTest' --console=plain`
Expected: FAIL (`didOpen` currently calls `getSync` and does not publish).

- [ ] **Step 3: Implement the lifecycle**

Add:

```kotlin
protected open fun publishDiagnostics(params: PublishDiagnosticsParams) {
    server.client.publishDiagnostics(params)
}

private fun parseAndPublish(uri: String) {
    try {
        getSync(uri)
        publishDiagnostics(PublishDiagnosticsParams(uri, emptyList()))
    } catch (e: SyntaxErrorReporter.ParserException) {
        publishDiagnostics(PublishDiagnosticsParams(uri, e.toDiagnostics()))
    } catch (e: ParseCancellationException) {
        publishDiagnostics(PublishDiagnosticsParams(uri, e.toDiagnostics()))
    }
}

override fun didOpen(params: DidOpenTextDocumentParams) {
    invalidate(params.textDocument.uri)
    parseAndPublish(params.textDocument.uri)
}
override fun didChange(params: DidChangeTextDocumentParams) {
    invalidate(params.textDocument.uri)
    parseAndPublish(params.textDocument.uri)
}
override fun didSave(params: DidSaveTextDocumentParams) {
    invalidate(params.textDocument.uri)
    parseAndPublish(params.textDocument.uri)
}
override fun didClose(params: DidCloseTextDocumentParams) {
    fileCache.remove(params.textDocument.uri)
    fileErrors.remove(params.textDocument.uri)
}
```

Keep `get(uri)` publishing on failure as today. Do not swallow `FileNotFound`/IO exceptions; let them surface.

- [ ] **Step 4: Run the test to verify it passes**

Run: `./gradlew :lsp:test --tests '*FileAntlrManagerTest' --console=plain`
Expected: PASS.

- [ ] **Step 5: Format and commit**

Run: `./gradlew spotlessApply`
Commit: `fix(lsp): publish diagnostics on open, change, and save`

---

### Task 4: Complete the Structured Text server

**Files:**
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/st/StructuredTextLanguageServer.kt`
- Create: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/st/StructuredTextFoldingRange.kt`
- Create: `lsp/src/test/kotlin/edu/kit/iti/formal/lsp/st/StructuredTextLanguageServerTest.kt`

**Interfaces:**
- Consumes: `StDocumentHighlighter.legend`, `FileAntlrManager`, `FoldingRangeHelper`.
- Produces:
  - `object StructuredTextFoldingRange : FoldingRangeHelper()` registering IEC61131 parser contexts.
  - `StructuredTextLanguageServer.initialize` returns `textDocumentSync = Full`, `semanticTokensProvider` for `**/*.st`, `foldingRangeProvider = Either.forLeft(true)`.

- [ ] **Step 1: Write the failing test**

```kotlin
class StructuredTextLanguageServerTest {
    @Test fun `initialize advertises sync, semantic tokens, and folding for st`() {
        val caps = StructuredTextLanguageServer().initialize(InitializeParams()).get().capabilities
        assertEquals(Either.forLeft(TextDocumentSyncKind.Full), caps.textDocumentSync)
        assertNotNull(caps.semanticTokensProvider)
        assertEquals(Either.forLeft(true), caps.foldingRangeProvider)
        val filter = caps.semanticTokensProvider.documentSelector.single()
        assertEquals("**/*.st", filter.pattern)
        assertNull(caps.hoverProvider) // not implemented
    }
}
```

Sample ST for the other tests:

```
PROGRAM P
VAR
    x : INT;
END_VAR
x := 1;
END_PROGRAM
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `./gradlew :lsp:test --tests '*StructuredTextLanguageServerTest' --console=plain`
Expected: FAIL (current `initialize` returns an empty result).

- [ ] **Step 3: Implement capabilities and ST folding**

In `initialize`, set:
- `capabilities.setTextDocumentSync(TextDocumentSyncKind.Full)`
- `capabilities.semanticTokensProvider = SemanticTokensWithRegistrationOptions(documentHighlighter.legend, SemanticTokensServerFull(true), false, listOf(DocumentFilter("st", "file", Either.forLeft("**/*.st"))))`
- `capabilities.semanticTokensProvider.range = Either.forLeft(true)`
- `capabilities.foldingRangeProvider = Either.forLeft(true)`
- `return InitializeResult(capabilities, ServerInfo("verifaps-st", "0.0.1"))`
- Remove the unused `params` field and the pull-diagnostics override; push diagnostics come from `FileAntlrManager`.

Create `StructuredTextFoldingRange`:

```kotlin
object StructuredTextFoldingRange : FoldingRangeHelper() {
    init {
        register<IEC61131Parser.Program_declarationContext> { it.identifier.text }
        register<IEC61131Parser.Function_declarationContext> { it.identifier.text }
        register<IEC61131Parser.Function_block_declarationContext> { it.identifier.text }
        register<IEC61131Parser.Class_declarationContext> { it.identifier.text }
        register<IEC61131Parser.Interface_declarationContext> { it.identifier.text }
        register<IEC61131Parser.MethodContext> { it.identifier.text }
        register<IEC61131Parser.Var_declsContext> { "VAR" }
        register<IEC61131Parser.If_statementContext> { "IF" }
        register<IEC61131Parser.Case_statementContext> { "CASE" }
        register<IEC61131Parser.Type_declarationContext> { "TYPE" }
    }
}
```

Change `StructuredTextTextDocumentService.foldingRange` to use `with(StructuredTextFoldingRange)`.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `./gradlew :lsp:test --tests '*StructuredText*' --console=plain`
Expected: PASS.

- [ ] **Step 5: Format and commit**

Run: `./gradlew spotlessApply`
Commit: `feat(lsp): complete Structured Text server capabilities and folding`

---

### Task 5: Complete the SMV server

**Files:**
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/smv/SmvLanguageServer.kt`
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/smv/SmvTextWorkspaceService.kt`
- Create: `lsp/src/test/kotlin/edu/kit/iti/formal/lsp/smv/SmvLanguageServerTest.kt`

**Interfaces:**
- Consumes: `SmvDocumentHighlighter.legend`, `SmvFoldingRange`.
- Produces: `SmvLanguageServer.initialize` advertises only sync, semantic tokens (`**/*.smv`), and folding.

- [ ] **Step 1: Write the failing test**

```kotlin
@Test fun `initialize advertises smv sync, tokens, folding only`() {
    val caps = SmvLanguageServer().initialize(InitializeParams()).get().capabilities
    assertEquals(Either.forLeft(TextDocumentSyncKind.Full), caps.textDocumentSync)
    assertEquals("**/*.smv", caps.semanticTokensProvider.documentSelector.single().pattern)
    assertEquals(Either.forLeft(true), caps.foldingRangeProvider)
    assertNull(caps.hoverProvider)
    assertNull(caps.codeActionProvider)
    assertNull(caps.executeCommandProvider)
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `./gradlew :lsp:test --tests '*SmvLanguageServerTest' --console=plain`
Expected: FAIL (selector is `**/*.key`, many unimplemented capabilities are set).

- [ ] **Step 3: Implement the capability cleanup**

- Replace the document filter with `DocumentFilter("smv", "file", Either.forLeft("**/*.smv"))`.
- Set only `textDocumentSync`, `semanticTokensProvider` (full+range, selector), and `foldingRangeProvider`.
- Remove hover, declaration, code action, code lens, selection range, formatting, completion, signature help, and `executeCommandProvider`.
- Remove the `actions` ServiceLoader block and the `executeCommandProvider`; delete `LspAction.kt` if no other use remains.
- Use provider ids/names `verifaps-smv`; remove all `KeY`/`key` strings.
- Add comments to the empty `SmvTextWorkspaceService` methods explaining they are intentional.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `./gradlew :lsp:test --tests '*Smv*' --console=plain`
Expected: PASS.

- [ ] **Step 5: Format and commit**

Run: `./gradlew spotlessApply`
Commit: `feat(lsp): align SMV server capabilities and document selector`

---

### Task 6: Implement the GTT server

**Files:**
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/gtt/GttLanguageServer.kt`
- Create: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/gtt/GttDocumentHighlighter.kt`
- Create: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/gtt/GttFoldingRange.kt`
- Create: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/gtt/GttTextDocumentService.kt`
- Create: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/gtt/GttTextWorkspaceService.kt`
- Create: `lsp/src/test/kotlin/edu/kit/iti/formal/lsp/gtt/GttLanguageServerTest.kt`

**Interfaces:**
- Consumes: `GetetaFacade.createParser(CharStream)`, `TestTableLanguageLexer`, `TestTableLanguageParser`, `FileAntlrManager`, `FoldingRangeHelper`.
- Produces:
  - `class GttTextDocumentService(server) : FileAntlrManager<TestTableLanguageParser.FileContext>(server)`
  - `class GttTextWorkspaceService(server) : WorkspaceService`
  - `object GttFoldingRange : FoldingRangeHelper()`
  - `GttLanguageServer.initialize` advertises sync, semantic tokens (`**/*.gtt`), folding.

- [ ] **Step 1: Write the failing test**

Use a valid sample (from `geteta/examples/weight/table.gtt`):

```
table Ta {
    var input i_fWeight : INT
    group 0 [1, 1] {
        row initWait [5,5] {
            i_fWeight: 0
        }
    }
}
```

```kotlin
@Test fun `initialize advertises gtt capabilities`() {
    val caps = GttLanguageServer().initialize(InitializeParams()).get().capabilities
    assertEquals(Either.forLeft(TextDocumentSyncKind.Full), caps.textDocumentSync)
    assertEquals("**/*.gtt", caps.semanticTokensProvider.documentSelector.single().pattern)
    assertNotNull(caps.foldingRangeProvider)
}
@Test fun `text document service parses a gtt and returns tokens`() {
    // create a temp .gtt, call semanticTokensFull, assert data is non-empty
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `./gradlew :lsp:test --tests '*Gtt*' --console=plain`
Expected: FAIL (`getTextDocumentService()` throws `NotImplementedError`).

- [ ] **Step 3: Implement the GTT server**

`GttTextDocumentService.parse`:

```kotlin
override fun parse(x: CharStream): TestTableLanguageParser.FileContext {
    val parser = GetetaFacade.createParser(x)
    val ctx = parser.file()
    parser.errorReporter.throwException()
    return ctx
}
```

`GttDocumentHighlighter`:
- `createLexer(text) = TestTableLanguageLexer(CharStreams.fromString(text))`
- Map `CONTRACT, AUTOMATON, TCONST, OMEGA, GVAR, WITH, VAR, AS, OF, OPTIONS, ROW, GROUP, STATE, INPUT, OUTPUT, RELATIONAL, TABLE, ASSUME, ASSERT, COLUMN, NEXT` to `KEYWORD`.
- Map comparison/arithmetic/logical tokens (`AND, OR, XOR, DIV, MOD, MULT, PLUS, MINUS, POWER, EQUALS, NOT_EQUALS, LESS_THAN, LESS_EQUALS, GREATER_THAN, GREATER_EQUALS, NOT, LPAREN, RPAREN, LBRACKET, RBRACKET, LBRACE, RBRACE, COMMA, SEMICOLON, COLON, DOT, ARROW_RIGHT, GUARD`) to `OPERATOR`.
- `INTEGER`/`FLOAT` to `NUMBER`; `T`/`F` (TRUE/FALSE) to `KEYWORD`; `S` (string) to `STRING`; `COMMENT`/`LINE_COMMENT` to `COMMENT`; `IDENTIFIER`/`FQ_VARIABLE` to `VARIABLE`.

`GttFoldingRange` registers:
`TableContext`, `GroupContext`, `RowContext`, `CaContext`, `StateContext`, `ContractContext`, `OptsContext`, `FunctionContext` (use the rule context class names generated by the GTT grammar).

`GttLanguageServer`:
- `initialize` sets sync Full, semantic tokens (legend, full+range, `**/*.gtt`), folding.
- `getTextDocumentService()` / `getWorkspaceService()` return lazily created instances; remove both `TODO`s.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `./gradlew :lsp:test --tests '*Gtt*' --console=plain`
Expected: PASS.

- [ ] **Step 5: Format and commit**

Run: `./gradlew spotlessApply`
Commit: `feat(lsp): implement GTT language server`

---

### Task 7: CLI, dead code, and duplicate grammar

**Files:**
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/Main.kt`
- Modify: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/MyLanguageServer.kt` (only if needed for the executor)
- Delete: `lsp/src/main/antlr/IEC61131Parser.g4` (identical unused copy of `lang`’s grammar)
- Delete: `lsp/src/main/kotlin/edu/kit/iti/formal/lsp/LspAction.kt` if Task 5 removed its last use
- Create: `lsp/src/test/kotlin/edu/kit/iti/formal/lsp/MainTest.kt`

**Interfaces:**
- Produces: `internal fun createLanguageServer(language: Language): MyLanguageServer` in `Main.kt`; `launchLanguageServer` uses it.
- `--language` help becomes `"Language to serve: gtt, st, smv (default: st)"`.

- [ ] **Step 1: Write the failing test**

```kotlin
@Test fun `createLanguageServer returns the server for each language`() {
    assertTrue(createLanguageServer(Language.STRUCTURED_TEXT) is StructuredTextLanguageServer)
    assertTrue(createLanguageServer(Language.SMV) is SmvLanguageServer)
    assertTrue(createLanguageServer(Language.GTT) is GttLanguageServer)
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `./gradlew :lsp:test --tests '*MainTest' --console=plain`
Expected: FAIL (`createLanguageServer` is missing).

- [ ] **Step 3: Implement**

- Extract the `when (language)` factory from `launchLanguageServer` into `internal fun createLanguageServer(language: Language): MyLanguageServer`.
- Update the `--language` help text; the default remains `Language.STRUCTURED_TEXT`.
- Delete `lsp/src/main/antlr/IEC61131Parser.g4`; it is not processed (the `lsp` module does not apply the `antlr` plugin) and is identical to `lang`’s grammar.
- Remove `LspAction.kt` if unused after Task 5; otherwise fix the `META-INF/services` comment to `edu.kit.iti.formal.lsp.LspAction`.
- `./gradlew :lsp:compileKotlin` must still pass after deleting the grammar.

- [ ] **Step 4: Run the test to verify it passes**

Run: `./gradlew :lsp:test --tests '*MainTest' --console=plain`
Expected: PASS.

- [ ] **Step 5: Format and commit**

Run: `./gradlew spotlessApply`
Commit: `chore(lsp): tidy CLI, capabilities, and remove duplicate grammar`

---

### Task 8: Full verification and PR metadata

**Files:**
- No source changes expected; fix any failures found.

- [ ] **Step 1: Run the full local gate**

```bash
./gradlew testClasses spotlessCheck test -x :exec:test --no-problems-report
./gradlew :exec:test
./gradlew assemble :exec:assembleDist
./gradlew dokkaGenerate
```

Expected: `BUILD SUCCESSFUL` for each. `:exec:test` needs `nuXmv` and `z3` on PATH (or the documented `NUXMV` environment variable).

- [ ] **Step 2: Check the SonarCloud gate**

After pushing, query:
`https://sonarcloud.io/api/qualitygates/project_status?projectKey=VerifAPS_verifaps-lib&pullRequest=211`
Expected: `status: OK`, `new_duplicated_lines_density < 3`, `new_reliability_rating = 1`.

- [ ] **Step 3: Update PR #211**

- Remove the WIP note from the PR body.
- State that all three servers are functional: ST, SMV, GTT.
- List the implemented requests: text sync, push diagnostics, semantic tokens (full/range), folding.
- Note the dependency updates and the test commands.
- Push the branch and confirm the `Tests` and `SonarCloud` checks pass.
