# V# for VS Code

Syntax highlighting for [V#](https://github.com/bluechiperic/vsharp). Files named `.vs` are recognized as V#.

The grammar follows the compiler. Reserved words (`fn`, `let`, `requires`, `ensures`, …) are keywords everywhere. Contextual words are highlighted only where they mean something: `grad` and `wrt` in a derivative declaration, `io`, `device`, and `async` after `effects`, and a namespace after `use`. `?name` is a typed hole. Strings highlight escapes and `{interpolation}`.

Comments toggle with `Ctrl+/`. Braces, brackets, and quotes pair automatically, and the editor indents with two spaces, which is what `vsharpc fmt` writes.

## Install

From this directory:

```
npm install
npm test
npx @vscode/vsce package
```

In VS Code or Cursor, run **Extensions: Install from VSIX…** and choose the generated `vsharp-0.1.0.vsix`.

`.vs` is also used by some shader tools for vertex shaders. If those files are highlighted as V#, set the association for that workspace:

```json
"files.associations": { "*.vertex.vs": "hlsl" }
```

## Check the grammar

`npm test` tokenizes a fixture and every `.vs` file under `samples/` and `tests/`. It checks that a `use` line does not paint the next declaration, and that keywords inside comments and string text stay uncolored.
