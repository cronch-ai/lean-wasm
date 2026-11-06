/** The theorem a solution proves, as the kernel's `proofs/check-lean.mjs` names it. */
export const THEOREM = "obligation";

/**
 * What to export, from the challenge and from the solution alike: the theorem, and the declarations Lean's kernel
 * gives a meaning of its own, which are compared too (as Comparator compares them). For example
 * `lake env leanexport Solution -- ${EXPORTED.join(" ")}`.
 */
export const EXPORTED = [
	THEOREM,
	"Quot",
	"Quot.mk",
	"Quot.lift",
	"Quot.ind",
	"propext",
	"Quot.sound",
	"Classical.choice",
	"Nat.add",
	"Nat.sub",
	"Nat.mul",
	"Nat.pow",
	"Nat.gcd",
	"Nat.div",
	"Nat.mod",
	"Nat.beq",
	"Nat.ble",
	"Nat.land",
	"Nat.lor",
	"Nat.xor",
	"Nat.shiftLeft",
	"Nat.shiftRight",
	"String.ofList",
	"Char.ofNat",
	"List",
	"eagerReduce",
	"Nat",
	"String",
	"String.mk",
	"Char",
	"optParam",
	"autoParam",
	"semiOutParam",
	"outParam",
];

const encoder = new TextEncoder();
const decoder = new TextDecoder();

/**
 * Instantiate the checker from its bytes, or from a compiled module where bytes can't be compiled (a Worker,
 * importing `@cronch/lean/lean.wasm`).
 */
export async function instantiate(source) {
	const module =
		source instanceof WebAssembly.Module
			? source
			: await WebAssembly.compile(source);

	return {
		async check(challenge, solution) {
			// Each check has its own instance: a refusal can trap, and leaves nothing behind.
			const instance = await WebAssembly.instantiate(module, {});
			const x = instance.exports;
			const write = (input) => {
				const bytes = typeof input === "string" ? encoder.encode(input) : input;
				const ptr = x.alloc(bytes.length);
				new Uint8Array(x.memory.buffer, ptr, bytes.length).set(bytes);
				return [ptr, bytes.length];
			};
			const message = () =>
				decoder.decode(
					new Uint8Array(x.memory.buffer, x.message_ptr(), x.message_len()),
				);
			const memoryBytes = () => x.memory.buffer.byteLength;
			try {
				if (x.check(...write(challenge), ...write(solution)) === 0) {
					return { result: "accepted", memoryBytes: memoryBytes() };
				}
				return {
					result: "refused",
					reason: message(),
					memoryBytes: memoryBytes(),
				};
			} catch (e) {
				if (!(e instanceof WebAssembly.RuntimeError)) throw e;
				// nanoda panicked, or ran out of stack or memory.
				return {
					result: "refused",
					reason: message() || e.message,
					memoryBytes: memoryBytes(),
				};
			}
		},
	};
}
