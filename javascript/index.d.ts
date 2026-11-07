/** The checker's answer. Only `accepted` means the solution proves the challenge's theorem. */
export type Checked =
	| { readonly result: "accepted"; readonly memoryBytes: number }
	/** The solution doesn't prove it, or isn't an export the checker can read; `reason` says why. */
	| {
			readonly result: "refused";
			readonly reason: string;
			readonly memoryBytes: number;
	  };

/** What a call asks of a theory: that `goal` follows from `Gamma` and every fact, or that the theory is consistent. */
export type Call =
	| {
			/** Each predicate's facts: an argument, or a list of them for a predicate of more than one. */
			readonly facts?: Readonly<
				Record<string, readonly (string | readonly string[])[]>
			>;
			readonly goal: {
				readonly pred: string;
				readonly args: readonly string[];
			};
	  }
	| { readonly goal: "consistent" };

/** A predicate of a theory's `Gamma`, over `arity` strings. */
export interface Predicate {
	readonly name: string;
	readonly arity: number;
}

export interface Lean {
	/**
	 * Whether `solution` proves the theorem `obligation` of `challenge`. Both are lean4export exports of
	 * {@link EXPORTED}. The challenge is trusted, as its statement: pin it, and pass it as pinned. The solution is
	 * checked by nanoda, permitting only `propext`, `Quot.sound` and `Classical.choice`.
	 */
	check(
		challenge: string | Uint8Array,
		solution: string | Uint8Array,
	): Promise<Checked>;

	/**
	 * Whether `solution` proves what `call` asks of `theory`, a pinned export defining `Gamma`. The challenge is built
	 * from them here, then checked as {@link Lean.check} checks one.
	 */
	checkCall(
		theory: string | Uint8Array,
		call: Call,
		solution: string | Uint8Array,
	): Promise<Checked>;

	/** The statement {@link Lean.checkCall} checks, as Lean, or why the theory can't state it. */
	statement(
		theory: string | Uint8Array,
		call: Call,
	): Promise<{ statement: string } | { error: string }>;

	/** The theory's predicates, in `Gamma`'s order, or why it isn't a theory. */
	predicates(
		theory: string | Uint8Array,
	): Promise<{ predicates: Predicate[] } | { error: string }>;
}

/** The theorem a solution proves. */
export const THEOREM: "obligation";

/** The names to export from the challenge and the solution alike. */
export const EXPORTED: readonly string[];

/** Instantiate the checker from its bytes, or from a compiled module where bytes can't be compiled (a Worker). */
export function instantiate(
	source: BufferSource | WebAssembly.Module,
): Promise<Lean>;
