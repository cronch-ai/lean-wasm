// What an accepted check reports of each declaration: a digest that names it whatever export it came from, what it
// uses and what it rests on. Two fixtures exported from different modules, T1's proof and constrained reasoning's,
// share declarations from Lean's prelude, numbered differently in each.

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

const t1 = async () => {
	const checked = await lean.check(fixture("Challenge"), fixture("Proof"));
	assert.equal(checked.result, "accepted", checked.reason);
	return checked.declarations;
};

const reasoning = async () => {
	const call = {
		facts: { late: ["812"], premium: ["812"] },
		goal: { pred: "refundable", args: ["812"] },
	};
	const checked = await lean.checkCall(
		fixture("reasoning/Theory"),
		call,
		fixture("reasoning/Proof"),
	);
	assert.equal(checked.result, "accepted", checked.reason);
	return checked.declarations;
};

const byName = (declarations) =>
	new Map(declarations.flatMap((d) => d.names.map((n) => [n, d])));

test("every declaration is reported once, with a digest, its uses and its axioms", async () => {
	const declarations = await t1();
	const names = declarations.flatMap((d) => d.names);
	assert.equal(new Set(names).size, names.length);
	const declared = new Set(names);
	for (const d of declarations) {
		assert.match(d.digest, /^sha256:[0-9a-f]{64}$/, d.names[0]);
		for (const used of d.uses) assert.ok(declared.has(used), used);
		for (const axiom of d.axioms) {
			assert.ok(
				["propext", "Quot.sound", "Classical.choice"].includes(axiom),
				axiom,
			);
		}
	}
	const decls = byName(declarations);
	assert.equal(decls.get("obligation").kind, "thm");
	assert.deepEqual(decls.get("propext").axioms, ["propext"]);
	assert.equal(
		new Set(declarations.map((d) => d.digest)).size,
		declarations.length,
	);
});

test("the same check reports the same declarations", async () => {
	assert.deepEqual(await t1(), await t1());
});

test("a declaration has the same digest in every export, and different ones differ", async () => {
	const a = byName(await t1());
	const b = byName(await reasoning());
	// `obligation` and the lemmas Lean makes for its proof (`obligation._proof_1_1`) have the same names in both, but
	// say different things. Everything else both hold is the prelude's.
	const own = (n) => n === "obligation" || n.startsWith("obligation.");
	const shared = [...a.keys()].filter((n) => b.has(n) && !own(n));
	assert.ok(shared.includes("Nat.add"), shared.join(" "));
	for (const name of shared) {
		assert.equal(a.get(name).digest, b.get(name).digest, name);
	}
	assert.notEqual(a.get("obligation").digest, b.get("obligation").digest);
	assert.notEqual(
		a.get("obligation._proof_1_1").digest,
		b.get("obligation._proof_1_1").digest,
	);
});
