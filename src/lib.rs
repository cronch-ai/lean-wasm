//! nanoda, an independent Lean kernel, for a Worker: no threads, no files, and two exports in memory. See README.md.
//!
//! `check` takes a challenge (the statement, pinned) and a solution (its proof), both in lean4export's format. It
//! accepts the solution when its `obligation` says what the challenge's does (`compare`), and nanoda checks every
//! declaration in it, permitting no axiom but `propext`, `Quot.sound` and `Classical.choice`.
//!
//! `check_call` does the same against a challenge it builds: constrained reasoning's statement, from a pinned theory
//! and a call's facts and goal (`reasoning`). `statement` gives that statement as Lean, for the solution's author.

mod compare;
mod reasoning;

use nanoda_lib::util::Config;
use std::sync::Mutex;

const CONFIG: &str = r#"{
    "use_stdin": true,
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "nat_extension": true,
    "string_extension": true
}"#;

/// Why the last check refused, read by the JS wrapper.
static MESSAGE: Mutex<Vec<u8>> = Mutex::new(Vec::new());

fn set_message(s: &str) {
    let mut m = MESSAGE.lock().unwrap_or_else(|e| e.into_inner());
    m.clear();
    m.extend_from_slice(s.as_bytes());
}

/// `len` bytes for the wrapper to write an export into. They are never freed: each check has its own instance.
#[no_mangle]
pub extern "C" fn alloc(len: usize) -> *mut u8 {
    let mut v = Vec::<u8>::with_capacity(len);
    let p = v.as_mut_ptr();
    std::mem::forget(v);
    p
}

#[no_mangle]
pub extern "C" fn message_ptr() -> *const u8 {
    MESSAGE.lock().unwrap_or_else(|e| e.into_inner()).as_ptr()
}

#[no_mangle]
pub extern "C" fn message_len() -> usize {
    MESSAGE.lock().unwrap_or_else(|e| e.into_inner()).len()
}

/// 0 when the solution proves the challenge's theorem, or 1 with the reason in `message`. nanoda reports most
/// errors by panicking: the panic's message is kept, and the instance traps.
///
/// # Safety
///
/// Each pointer and length must be a buffer from `alloc`, written by the caller.
#[no_mangle]
pub unsafe extern "C" fn check(
    challenge: *const u8,
    challenge_len: usize,
    solution: *const u8,
    solution_len: usize,
) -> i32 {
    std::panic::set_hook(Box::new(|info| set_message(&format!("nanoda: {info}"))));
    let challenge = std::slice::from_raw_parts(challenge, challenge_len);
    let solution = std::slice::from_raw_parts(solution, solution_len);
    match run(challenge, solution) {
        Ok(()) => 0,
        Err(e) => {
            set_message(&e);
            1
        }
    }
}

/// 0 when the solution proves what the call asks of the theory, or 1 with the reason in `message`, as `check`.
/// The call is JSON: `{ "facts": { "late": ["812"] }, "goal": { "pred": "refundable", "args": ["812"] } }`, or with
/// the goal `"consistent"` and no facts.
///
/// # Safety
///
/// Each pointer and length must be a buffer from `alloc`, written by the caller.
#[no_mangle]
pub unsafe extern "C" fn check_call(
    theory: *const u8,
    theory_len: usize,
    call: *const u8,
    call_len: usize,
    solution: *const u8,
    solution_len: usize,
) -> i32 {
    std::panic::set_hook(Box::new(|info| set_message(&format!("nanoda: {info}"))));
    let theory = std::slice::from_raw_parts(theory, theory_len);
    let call = std::slice::from_raw_parts(call, call_len);
    let solution = std::slice::from_raw_parts(solution, solution_len);
    let checked = parse_call(call)
        .and_then(|call| reasoning::challenge(theory, &call).map_err(|e| format!("the theory: {e}")))
        .and_then(|challenge| run(&challenge, solution));
    match checked {
        Ok(()) => 0,
        Err(e) => {
            set_message(&e);
            1
        }
    }
}

/// 0 with the call's statement as Lean in `message`, or 1 with the reason there.
///
/// # Safety
///
/// Each pointer and length must be a buffer from `alloc`, written by the caller.
#[no_mangle]
pub unsafe extern "C" fn statement(theory: *const u8, theory_len: usize, call: *const u8, call_len: usize) -> i32 {
    let theory = std::slice::from_raw_parts(theory, theory_len);
    let call = std::slice::from_raw_parts(call, call_len);
    match parse_call(call).and_then(|call| reasoning::lean(theory, &call).map_err(|e| format!("the theory: {e}"))) {
        Ok(text) => {
            set_message(&text);
            0
        }
        Err(e) => {
            set_message(&e);
            1
        }
    }
}

fn parse_call(call: &[u8]) -> Result<reasoning::Call, String> {
    reasoning::Call::parse(call).map_err(|e| format!("the call: {e}"))
}

fn run(challenge: &[u8], solution: &[u8]) -> Result<(), String> {
    compare::compare(challenge, solution)?;
    let config: Config = serde_json::from_str(CONFIG).map_err(|e| e.to_string())?;
    let (export, _) = nanoda_lib::parser::parse_export_file(solution, config).map_err(|e| format!("nanoda: {e}"))?;
    export.check_all_declars_serial();
    Ok(())
}
