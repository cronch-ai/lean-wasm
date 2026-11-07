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

	/** Runs `entry` over the inputs in an instance of its own: a refusal can trap, and leaves nothing behind. */
	async function call_(entry, ...inputs) {
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
			const status = x[entry](...inputs.flatMap(write));
			return {
				ok: status === 0,
				message: message(),
				memoryBytes: memoryBytes(),
			};
		} catch (e) {
			if (!(e instanceof WebAssembly.RuntimeError)) throw e;
			// nanoda panicked, or ran out of stack or memory.
			return {
				ok: false,
				message: message() || e.message,
				memoryBytes: memoryBytes(),
			};
		}
	}

	const verdict = ({ ok, message, memoryBytes }) =>
		ok
			? { result: "accepted", memoryBytes }
			: { result: "refused", reason: message, memoryBytes };

	return {
		/** Whether `solution` proves the pinned `challenge`'s `obligation`. */
		async check(challenge, solution) {
			return verdict(await call_("check", challenge, solution));
		},

		/**
		 * Whether `solution` proves what `call` asks of the pinned `theory`: constrained reasoning's statement, built
		 * here from the theory's `Gamma`, every fact in `call.facts` and `call.goal` (an atom `{ pred, args }`, or
		 * `"consistent"`).
		 */
		async checkCall(theory, call, solution) {
			return verdict(
				await call_("check_call", theory, JSON.stringify(call), solution),
			);
		},

		/** The statement `checkCall` checks, as Lean: `{ statement }`, or `{ error }`. */
		async statement(theory, call) {
			const out = await call_("statement", theory, JSON.stringify(call));
			return out.ok ? { statement: out.message } : { error: out.message };
		},

		/** The theory's predicates, in `Gamma`'s order: `{ predicates: [{ name, arity }] }`, or `{ error }`. */
		async predicates(theory) {
			const out = await call_("predicates", theory);
			return out.ok
				? { predicates: JSON.parse(out.message) }
				: { error: out.message };
		},
	};
}
