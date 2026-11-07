// The fixtures are T1's `net.fetch` obligation for `net.ask.onResult`, from the kernel: its challenge, a proof, and
// the attacks the kernel's `proofs/lean.test.mjs` makes on Comparator. `scripts/fixtures.sh` makes them from
// `fixtures/Fixtures/`.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { gunzipSync } from "node:zlib";
import { instantiate } from "../index.js";

const lean = await instantiate(
	readFileSync(new URL("../lean.wasm", import.meta.url)),
);
const fixture = (name) =>
	gunzipSync(
		readFileSync(new URL(`fixtures/${name}.ndjson.gz`, import.meta.url)),
	).toString("utf8");
const challenge = fixture("Challenge");

const refused = async (solution, why) => {
	const checked = await lean.check(challenge, solution);
	assert.equal(checked.result, "refused");
	assert.match(checked.reason, why);
};

test("a proof of the statement is accepted, within a Worker's memory", async () => {
	const checked = await lean.check(challenge, fixture("Proof"));
	assert.equal(checked.result, "accepted", checked.reason);
	assert.ok(checked.memoryBytes <= 96 * 2 ** 20, `${checked.memoryBytes}`);
});

test("sorry, a new axiom and native_decide are refused", async () => {
	await refused(challenge, /unpermitted axiom "sorryAx"/);
	await refused(fixture("Axiom"), /unpermitted axiom "cheat"/);
	// Lean 4.35 compiles `native_decide` to an axiom of its own.
	await refused(
		fixture("NativeDecide"),
		/unpermitted axiom "shortcut\._native\.native_decide\.ax_\d+_\d+"/,
	);
});

// `obligation`'s type is `statement`, so a change to what it says shows as a change to `statement`.
test("a proof of another statement is refused", async () => {
	await refused(fixture("Other"), /^statement isn't the challenge's$/);
});

test("a solution that redefines a name, a notation or an instance is refused", async () => {
	// Smt.seq.contains, defined as never true.
	await refused(
		fixture("Redefine"),
		/^Smt\.seq\.contains isn't the challenge's$/,
	);
	// Negation (`Not p`) read as `True`.
	await refused(fixture("Notation"), /^statement isn't the challenge's$/);
	// `a ++ b` read as `[]`.
	await refused(fixture("Instance"), /^statement isn't the challenge's$/);
});

test("a proof that isn't one is refused by nanoda", async () => {
	// The proof's value replaced by its own statement, which has the wrong type.
	const proof = fixture("Proof");
	const name = proof.match(
		/\{"in":(\d+),"str":\{"pre":0,"str":"obligation"\}\}/,
	)[1];
	const theorem = new RegExp(`("name":${name},"type":(\\d+),"value":)\\d+`);
	assert.match(proof, theorem);
	const broken = proof.replace(theorem, (_, head, type) => `${head}${type}`);
	await refused(broken, /^nanoda: /);
});

test("a solution must hold what Lean's kernel gives its own meaning", async () => {
	// Without Nat.add's definition, the kernel would compute a Nat.add the solution never defined.
	const proof = fixture("Proof");
	const nat = proof.match(/\{"in":(\d+),"str":\{"pre":0,"str":"Nat"\}\}/)[1];
	const add = proof.match(
		new RegExp(`\\{"in":(\\d+),"str":\\{"pre":${nat},"str":"add"\\}\\}`),
	)[1];
	const definition = new RegExp(
		`^\\{"def":\\{[^\n]*"name":${add},[^\n]*\n`,
		"m",
	);
	assert.match(proof, definition);
	await refused(
		proof.replace(definition, ""),
		/the solution doesn't declare Nat\.add/,
	);
});

test("an export the checker can't read is refused", async () => {
	const noChallenge = await lean.check("", fixture("Proof"));
	assert.match(noChallenge.reason, /^the challenge has no theorem obligation$/);
	await refused("", /^the solution has no theorem obligation$/);
	await refused(`${fixture("Proof")}\nnot json`, /^the solution: line \d+/);
});
