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
lake env leanexport Solution -- obligation Quot Quot.mk … outParam
```

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
