/** The checker's answer. Only `accepted` means the solution proves the challenge's theorem. */
export type Checked =
	| { readonly result: "accepted"; readonly memoryBytes: number }
	/** The solution doesn't prove it, or isn't an export the checker can read; `reason` says why. */
	| {
			readonly result: "refused";
			readonly reason: string;
			readonly memoryBytes: number;
	  };

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
}

/** The theorem a solution proves. */
export const THEOREM: "obligation";

/** The names to export from the challenge and the solution alike. */
export const EXPORTED: readonly string[];

/** Instantiate the checker from its bytes, or from a compiled module where bytes can't be compiled (a Worker). */
export function instantiate(
	source: BufferSource | WebAssembly.Module,
): Promise<Lean>;
