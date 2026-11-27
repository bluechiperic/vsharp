import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const oniguruma = require("vscode-oniguruma");
const textmate = require("vscode-textmate");

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, "..");
const repo = path.resolve(root, "../..");

const wasm = fs.readFileSync(path.join(root, "node_modules/vscode-oniguruma/release/onig.wasm")).buffer;
const onigLib = oniguruma.loadWASM(wasm).then(() => ({
  createOnigScanner: (patterns) => new oniguruma.OnigScanner(patterns),
  createOnigString: (s) => new oniguruma.OnigString(s),
}));

const registry = new textmate.Registry({
  onigLib,
  loadGrammar: async (scopeName) => {
    if (scopeName !== "source.vsharp") return null;
    const file = path.join(root, "syntaxes/vsharp.tmLanguage.json");
    return textmate.parseRawGrammar(fs.readFileSync(file, "utf8"), file);
  },
});

const grammar = await registry.loadGrammar("source.vsharp");
if (!grammar) throw new Error("grammar failed to load");

let failures = 0;

function tokenize(text) {
  const lines = text.split(/\r?\n/);
  let stack = null;
  return lines.map((line) => {
    const result = grammar.tokenizeLine(line, stack);
    stack = result.ruleStack;
    return result.tokens.map((token) => ({
      text: line.slice(token.startIndex, token.endIndex),
      scopes: token.scopes,
    }));
  });
}

function fail(message) {
  failures++;
  console.error(message);
}

function dump(lines, tokens) {
  return tokens
    .map((row, i) => `${String(i + 1).padStart(3)} ${JSON.stringify(lines[i])}\n${row.map((t) => `      ${JSON.stringify(t.text)}  ${t.scopes.join(" ")}`).join("\n")}`)
    .join("\n");
}

function expectScope(tokens, text, scope, label) {
  const hits = tokens.flat().filter((t) => t.text === text);
  if (hits.length === 0) {
    fail(`${label}: no token ${JSON.stringify(text)}`);
    return;
  }
  if (!hits.some((t) => t.scopes.some((s) => s.includes(scope)))) {
    fail(`${label}: ${JSON.stringify(text)} scopes were ${hits.map((t) => t.scopes.join(" ")).join(" | ")}, wanted ${scope}`);
  }
}

function expectNoScope(tokens, scope, label) {
  for (const token of tokens.flat()) {
    if (token.scopes.some((s) => s.includes(scope))) {
      fail(`${label}: ${JSON.stringify(token.text)} unexpectedly has ${scope}`);
    }
  }
}

function check(text, asserts, label) {
  const lines = text.split(/\r?\n/);
  const tokens = tokenize(text);
  const before = failures;
  for (const [tokenText, scope] of asserts) expectScope(tokens, tokenText, scope, label);
  if (failures !== before) console.error(dump(lines, tokens));
}

check(
  `// throws when the contract is wrong
spec fn sum_to(n: Int) -> Int
fn dw1 = grad loss wrt w1
fn main() -> Unit effects device, io {
extern fn pause(ms: Int32) -> Unit effects async from "System.Threading.Tasks.Task.Delay"
return "{v.patient} on {v.day}"
return ?answer
ensures result >= 0 ==> a[result] == key
@JsonPropertyName("w") width: Decimal
requires 0m <= percent && percent <= 100m
let ratio = 0.5
filter(vs, v => v.fee >= 0m)
use System.Text.Json.Serialization
interface Shape {
  fn area(self) -> Decimal
ensures match result { Ok(b) => true, Err(e) => false }
`,
  [
    ["spec", "keyword.other.fn"],
    ["sum_to", "entity.name.function"],
    ["n", "variable.parameter"],
    ["Int", "support.type"],
    ["->", "keyword.operator"],
    ["dw1", "entity.name.function"],
    ["grad", "keyword.other.grad"],
    ["wrt", "keyword.other.grad"],
    ["loss", "entity.name.function"],
    ["w1", "variable.parameter"],
    ["effects", "keyword.control.contract"],
    ["device", "constant.language.effect"],
    ["io", "constant.language.effect"],
    ["async", "constant.language.effect"],
    ["from", "keyword.control"],
    ["patient", "variable.other.property"],
    ["?", "punctuation.definition.hole"],
    ["answer", "entity.name.function.hole"],
    ["result", "variable.language"],
    ["==>", "keyword.operator"],
    ["JsonPropertyName", "entity.name.type.attribute"],
    ["width", "variable.parameter"],
    ["Decimal", "support.type"],
    ["0m", "constant.numeric.decimal"],
    ["100m", "constant.numeric.decimal"],
    ["&&", "keyword.operator"],
    ["0.5", "constant.numeric.float"],
    ["filter", "entity.name.function.call"],
    ["v", "variable.parameter"],
    ["=>", "keyword.operator.arrow"],
    ["fee", "variable.other.property"],
    ["use", "keyword.other.use"],
    ["Serialization", "entity.name.namespace"],
    ["interface", "keyword.other.declaration"],
    ["Shape", "entity.name.type"],
    ["area", "entity.name.function"],
    ["self", "variable.language"],
    ["{", "punctuation.definition.block"],
    ["match", "keyword.control"],
    ["Ok", "entity.name.type.constructor"],
    ["true", "constant.language"],
  ],
  "fixture",
);

check(
  `module Shapes

use System.ComponentModel

interface Shape {
  fn area(self) -> Decimal
`,
  [
    ["Shapes", "entity.name.type"],
    ["use", "keyword.other.use"],
    ["ComponentModel", "entity.name.namespace"],
    ["interface", "keyword.other.declaration"],
    ["Shape", "entity.name.type"],
    ["fn", "keyword.other.fn"],
    ["area", "entity.name.function"],
  ],
  "use does not swallow the next declaration",
);

const effectsLine = tokenize("fn main() -> Unit effects device, io {")[0];
const effectsBrace = effectsLine.find((token) => token.text === "{");
if (!effectsBrace?.scopes.some((scope) => scope.includes("punctuation.definition.block"))) {
  fail(`brace after effects was not punctuation: ${JSON.stringify(effectsBrace)}`);
}

const commentLine = tokenize("// throws when the contract is wrong")[0];
expectNoScope([commentLine], "keyword.control", "comment hides keywords");

const stringLine = tokenize('return "fn requires {name}"')[0];
const fnInString = stringLine.filter((t) => t.text === "fn" || t.text === "requires");
if (fnInString.some((t) => t.scopes.some((s) => s.startsWith("keyword.")))) {
  fail(`string text was highlighted as a keyword:\n${dump(['return "fn requires {name}"'], [stringLine])}`);
}
expectScope([stringLine], "name", "meta.interpolation", "interpolation");

function walk(dir, out) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) walk(full, out);
    else if (entry.name.endsWith(".vs")) out.push(full);
  }
}

const sources = [];
walk(path.join(repo, "samples"), sources);
walk(path.join(repo, "tests"), sources);
for (const file of sources) {
  try {
    tokenize(fs.readFileSync(file, "utf8"));
  } catch (error) {
    fail(`${path.relative(repo, file)}: ${error.message}`);
  }
}
console.log(`tokenized ${sources.length} .vs files`);

if (failures > 0) {
  console.error(`${failures} failure(s)`);
  process.exit(1);
}
console.log("highlight tests passed");
