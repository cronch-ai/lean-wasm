# lean-wasm

[nanoda](https://github.com/ammkrn/nanoda_lib), an independent Lean 4 kernel, built for Cloudflare Workers, as the npm package `@cronch/lean`. The [cronch platform](https://github.com/cronch-ai/platform) uses it to check Lean proofs of the kernel's rule obligations. See [Checking in a Worker](https://github.com/cronch-ai/kernel/blob/main/docs/2026-11-06-lean.md#checking-in-a-worker).

Full Lean can't run in a Worker, but checking a proof needs only a kernel. So a proof is elaborated with full Lean elsewhere, and exported with `lean4export`; this checks the export. It works as [Comparator](https://github.com/leanprover/comparator) does:

- The **challenge** is the statement, with `theorem obligation : statement := sorry`, as the kernel's `proofs/check-lean.mjs` writes it. It is trusted: the platform pins its export when a rule is registered.
- The **solution** proves `theorem obligation : statement`, restating what it needs.
- The solution is accepted when:
  - its `obligation` has the challenge's type;
  - every declaration that type uses, and every declaration those use, is the challenge's, so it can't change what a name, a notation or an instance means;
  - the declarations Lean's kernel gives a meaning of its own (`Nat.add`, `String.ofList`, the quotient and the rest) are the challenge's;
  - nanoda checks every declaration in it, permitting no axiom but `propext`, `Quot.sound` and `Classical.choice`. That refuses `sorry`, a new `axiom` and `native_decide`.

nanoda as built here:

- **Single-threaded, from memory:** it checks serially, from bytes the wrapper writes. Two of its functions are made public for that (`patches/nanoda.patch`).
- **Small memory:** an 8 MiB stack, first in memory so an overflow traps, and at most 96 MiB in all, under a Worker's 128 MB. T1's proofs check in about 200 ms and 16 MiB.
- **A panic is a refusal:** nanoda reports most errors by panicking. The panic traps, and the wrapper returns its message. Each check has its own instance.

A check has no budget of its own: a Worker's CPU limit is what stops one that runs long.

## Use

```js
import { EXPORTED, instantiate } from "@cronch/lean";
import wasm from "@cronch/lean/lean.wasm"; // a compiled module in a Worker; bytes in Node

const lean = await instantiate(wasm);
await lean.check(challenge, solution); // { result: "accepted" } or { result: "refused", reason }
```

Export the challenge and the solution alike, with the names in `EXPORTED`:

```sh
lake env leanexport Solution -- obligation Quot Quot.mk ... outParam
```

## Constrained reasoning

A harness can act only on what a checked proof shows, from a fixed theory and from facts trusted results gave ([Constrained reasoning](https://linear.app/cronch-ai/document/constrained-reasoning-acting-only-on-what-follows-from-a-fixed-theory-79e80245ee7f)). Each call's statement depends on the run's facts, so it can't be pinned ahead of time, and full Lean can't elaborate it in a Worker. So the statement is built here, directly as kernel terms:

- The **theory** is an export of a module defining `Gamma`, whose binders are its predicates, each over strings: `def Gamma (damaged late premium refundable : String -> Prop) : Prop`. Export it with `Gamma`, `True` and the names in `EXPORTED` but `obligation`, and pin it when it is published.
- A **call** is every fact the grant holds, by predicate, and a goal: `{ facts: { late: ["812"], premium: ["812"] }, goal: { pred: "refundable", args: ["812"] } }`.
- The **statement** is `forall (damaged late premium refundable : String -> Prop), Gamma damaged late premium refundable -> late "812" -> premium "812" -> refundable "812"`: every fact a hypothesis, sorted and without repeats. It needs only Pi types, applications and string literals, so no elaborator is needed to write it.
- The goal `"consistent"` instead states `Gamma` with every predicate `True`: a model of the theory in which every atom is true, so the theory with any facts at all is consistent. A platform requires it to publish a theory.

```js
await lean.statement(theory, call); // { statement } as Lean, for `theorem obligation : <statement> := ...`
await lean.checkCall(theory, call, solution); // as `check`, against the statement built from the theory
```

The challenge is the theory's export with `obligation` appended, compared with the solution as any challenge is, so a solution can't redefine `Gamma`, and nanoda checks it with the same axioms. The Lean text is a convenience: a solution elaborated from other text doesn't match. The fixtures are `fixtures/Reasoning/`: the refund policy, a proof, and the attacks on it.

## Development

You need the Rust toolchain in `rust-toolchain.toml` and Node 24. The dev container provides both.

```sh
npm run build   # javascript/lean.wasm and lean.sha256, from nanoda at versions.env's revision
npm test
npm run lint
```

The test fixtures are T1's `net.fetch` obligation from the kernel, and the attacks on it. `scripts/fixtures.sh` makes them from `fixtures/Fixtures/`, with Lean 4.35.0 on `PATH`. `fixtures/Cronch/Smt.lean` is the kernel's.

A push to `main` that changes `javascript/package.json`'s version publishes a GitHub release with the npm tarball, `lean.wasm` and `lean.sha256`.

## License

Apache 2.0. `lean.wasm` bundles nanoda and a few Rust crates, under their own licenses: see [NOTICE](javascript/NOTICE).
