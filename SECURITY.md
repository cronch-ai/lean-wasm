# Security

Report a vulnerability privately, through GitHub: **Security > Report a vulnerability** on this repo. Please don't open a public issue for it.

## What counts

This repo checks Lean proofs against pinned statements, so a vulnerability is anything that makes it accept what it shouldn't:

- A proof accepted for a statement it doesn't prove, or for a different statement than the one pinned.
- An axiom other than `propext`, `Quot.sound` and `Classical.choice` (or `sorry`, or `native_decide`) getting past the check.
- Input that makes the checker crash, hang without bound, or escape the Worker it runs in.

If you're not sure whether something counts, report it privately anyway.
