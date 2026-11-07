// Constrained reasoning: a call's statement, built from a pinned theory and the grant's facts, and the proofs checked
// against it. The fixtures are `fixtures/Reasoning/`, exported as `scripts/fixtures.sh` says: the refund policy as a
// theory, a proof that order 812 is refundable, and the attacks on it.

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
		readFileSync(
			new URL(`fixtures/reasoning/${name}.ndjson.gz`, import.meta.url),
		),
	).toString("utf8");
const theory = fixture("Theory");

/** The grant's facts after the lookup of order 812, and the goal that it is refundable. */
const refund = (
	order = "812",
	facts = { late: ["812"], premium: ["812"] },
) => ({
	facts,
	goal: { pred: "refundable", args: [order] },
});

const refused = async (call, solution, why, of = theory) => {
	const checked = await lean.checkCall(of, call, solution);
	assert.equal(checked.result, "refused");
	assert.match(checked.reason, why);
};

test("the statement is every fact in the grant, to the goal, as Lean", async () => {
	assert.deepEqual(await lean.statement(theory, refund()), {
		statement:
			'forall (damaged late premium refundable : String -> Prop), Gamma damaged late premium refundable -> late "812" -> premium "812" -> refundable "812"',
	});
	// Sorted and without repeats, whatever order the grant has them in.
	const shuffled = refund("812", {
		premium: ["812", "812"],
		late: ["812"],
	});
	assert.deepEqual(
		await lean.statement(theory, shuffled),
		await lean.statement(theory, refund()),
	);
	// A string is quoted as Lean reads it.
	const odd = await lean.statement(theory, refund('8"1\\2'));
	assert.match(odd.statement, /refundable "8\\"1\\\\2"$/);
});

test("the theory's predicates are Gamma's, in its order", async () => {
	assert.deepEqual(await lean.predicates(theory), {
		predicates: ["damaged", "late", "premium", "refundable"].map((name) => ({
			name,
			arity: 1,
		})),
	});
	assert.match(
		(await lean.predicates(fixture("Proof"))).error,
		/declares obligation/,
	);
});

test("a proof from the grant's facts is accepted, within a Worker's memory", async () => {
	const checked = await lean.checkCall(theory, refund(), fixture("Proof"));
	assert.equal(checked.result, "accepted", checked.reason);
	assert.ok(checked.memoryBytes <= 96 * 2 ** 20, `${checked.memoryBytes}`);
});

test("a proof of anything else is refused", async () => {
	const other = /obligation doesn't have the challenge's statement/;
	// Another order.
	await refused(refund("813"), fixture("Proof"), other);
	// A fact the grant doesn't have.
	await refused(refund(), fixture("Damaged"), other);
	// A fact the grant has and the proof leaves out: every fact is a hypothesis, so the statement isn't the same.
	const more = refund("812", {
		late: ["812"],
		premium: ["812"],
		damaged: ["700"],
	});
	await refused(more, fixture("Proof"), other);
});

test("a policy of the solution's own, and an axiom of its own, are refused", async () => {
	await refused(refund(), fixture("Lenient"), /Gamma isn't the challenge's/);
	await refused(refund(), fixture("Cheat"), /unpermitted axiom "cheat"/);
});

test("the theory's consistency is Gamma with every predicate True", async () => {
	assert.deepEqual(await lean.statement(theory, { goal: "consistent" }), {
		statement:
			"Gamma (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True)",
	});
	const checked = await lean.checkCall(
		theory,
		{ goal: "consistent" },
		fixture("Consistent"),
	);
	assert.equal(checked.result, "accepted", checked.reason);
	await refused({ goal: "consistent" }, fixture("Proof"), /statement/);
});

test("a call the theory can't state is refused before any proof is read", async () => {
	const error = async (call, why, of = theory) => {
		const out = await lean.statement(of, call);
		assert.match(out.error, why);
		await refused(call, fixture("Proof"), why, of);
	};
	await error(refund("812", { shipped: ["812"] }), /no predicate shipped/);
	await error(
		{ goal: { pred: "refundable", args: ["812", "813"] } },
		/takes 1 arguments, not 2/,
	);
	await error({ goal: "consistent", facts: { late: ["1"] } }, /no facts/);
	await error({ goal: "everything" }, /neither an atom/);
	await error({ goal: "consistent", extra: 1 }, /unknown field extra/);
	// A theory must define Gamma, and must not state obligation itself.
	await error(
		refund(),
		/no name Gamma/,
		fixture("Proof").replace(/"Gamma"/g, '"Gamma2"'),
	);
	await error(refund(), /declares obligation/, fixture("Proof"));
});
