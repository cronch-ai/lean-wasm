//! A call's statement, built from a pinned theory: constrained reasoning's challenge, written as kernel terms so that
//! no elaborator runs per call. See README.md.
//!
//! The theory is an export of a module that defines `Gamma`, whose binders are its predicates, each over strings:
//! `def Gamma (damaged late premium refundable : String -> Prop) : Prop`. It is exported with `True` and the builtins,
//! and pinned when it is published. A call names facts and a goal, and the statement is
//!
//! `forall (damaged late premium refundable : String -> Prop), Gamma damaged late premium refundable -> late "812" ->
//! premium "812" -> refundable "812"`
//!
//! with every fact as a hypothesis, sorted and without repeats, so it doesn't depend on the order the facts came in.
//! The consistency statement instead says that `Gamma` holds with every predicate `True`: one model of the theory
//! with every atom true, so the theory with any facts at all is consistent.
//!
//! The challenge is the theory's export with that theorem appended, named `obligation`, and is compared with a
//! solution as any pinned challenge is. The same statement is also printed as Lean, for whoever elaborates a proof.
//! The printed text is never trusted: a solution elaborated from other text doesn't match the challenge.

use serde_json::{json, Value};
use std::collections::{BTreeSet, HashMap};

/// What a call asks: every fact the grant holds, by predicate, and what is to be shown.
pub struct Call {
    facts: Vec<(String, Vec<String>)>,
    goal: Goal,
}

enum Goal {
    /// The theory is consistent with every set of facts.
    Consistent,
    Atom {
        pred: String,
        args: Vec<String>,
    },
}

fn strings(v: &Value, what: &str) -> Result<Vec<String>, String> {
    v.as_array()
        .ok_or_else(|| format!("{what} isn't a list"))?
        .iter()
        .map(|s| {
            s.as_str()
                .map(str::to_string)
                .ok_or_else(|| format!("{what} holds a non-string"))
        })
        .collect()
}

impl Call {
    /// `{ "facts": { "late": ["812"] }, "goal": { "pred": "refundable", "args": ["812"] } }`, or the goal
    /// `"consistent"` with no facts. A fact of a predicate of one argument is a string, and of more a list of them.
    pub fn parse(bytes: &[u8]) -> Result<Call, String> {
        let v: Value = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        let o = v.as_object().ok_or("isn't an object")?;
        if let Some(k) = o.keys().find(|k| !matches!(k.as_str(), "facts" | "goal")) {
            return Err(format!("unknown field {k}"));
        }
        let mut facts = Vec::new();
        if let Some(f) = o.get("facts") {
            for (pred, all) in f.as_object().ok_or("facts isn't an object")? {
                for a in all.as_array().ok_or_else(|| format!("{pred}'s facts aren't a list"))? {
                    let args = match a {
                        Value::String(s) => vec![s.clone()],
                        other => strings(other, &format!("a fact of {pred}"))?,
                    };
                    facts.push((pred.clone(), args));
                }
            }
        }
        let goal = match o.get("goal").ok_or("has no goal")? {
            Value::String(s) if s == "consistent" => Goal::Consistent,
            Value::Object(g) => {
                if let Some(k) = g.keys().find(|k| !matches!(k.as_str(), "pred" | "args")) {
                    return Err(format!("unknown field {k} in the goal"));
                }
                Goal::Atom {
                    pred: g
                        .get("pred")
                        .and_then(Value::as_str)
                        .ok_or("the goal has no pred")?
                        .to_string(),
                    args: strings(g.get("args").ok_or("the goal has no args")?, "the goal's args")?,
                }
            }
            _ => return Err("the goal is neither an atom nor \"consistent\"".to_string()),
        };
        Ok(Call { facts, goal })
    }
}

/// The theory's predicates, in `Gamma`'s order, and what the statement needs of its export.
struct Theory<'t> {
    text: &'t str,
    predicates: Vec<(String, usize)>,
    gamma: u64,
    string: u64,
    truth: Option<u64>,
    obligation: Option<u64>,
    next_name: u64,
    next_expr: u64,
}

const RESERVED: &[&str] = &["Gamma", "String", "True", "Prop", "Type", "fun", "forall"];

fn identifier(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next().is_some_and(|c| c.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !RESERVED.contains(&s)
}

fn expr<'e>(exprs: &'e HashMap<u64, Value>, id: &Value) -> Result<&'e Value, String> {
    let id = id.as_u64().ok_or("an expression id isn't a number")?;
    exprs.get(&id).ok_or_else(|| format!("expression {id} isn't defined"))
}

fn is_prop(e: &Value) -> bool {
    e.get("sort").and_then(Value::as_u64) == Some(0)
}

/// How many strings a predicate's type `String -> ... -> Prop` takes, or `None` if it isn't one.
fn arity<'e>(exprs: &'e HashMap<u64, Value>, mut e: &'e Value, string: u64) -> Result<Option<usize>, String> {
    let is_string = |e: &Value| {
        e.get("const")
            .is_some_and(|c| c["name"].as_u64() == Some(string) && c["us"].as_array().is_some_and(Vec::is_empty))
    };
    let mut n = 0;
    while let Some(f) = e.get("forallE") {
        if !is_string(expr(exprs, &f["type"])?) {
            return Ok(None);
        }
        n += 1;
        e = expr(exprs, &f["body"])?;
    }
    Ok((n > 0 && is_prop(e)).then_some(n))
}

fn read(theory: &[u8]) -> Result<Theory<'_>, String> {
    let text = std::str::from_utf8(theory).map_err(|e| e.to_string())?;
    let mut names: HashMap<u64, (u64, String)> = HashMap::new();
    let mut exprs: HashMap<u64, Value> = HashMap::new();
    let mut decls: Vec<(String, Value)> = Vec::new();
    let (mut next_name, mut next_expr) = (1, 1);
    for (i, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let v: Value = serde_json::from_str(line).map_err(|e| format!("line {}: {e}", i + 1))?;
        if let Some(id) = v.get("in").and_then(Value::as_u64) {
            next_name = next_name.max(id + 1);
            if let Some(s) = v.get("str") {
                let pre = s.get("pre").and_then(Value::as_u64).unwrap_or(u64::MAX);
                let part = s.get("str").and_then(Value::as_str).unwrap_or_default();
                names.insert(id, (pre, part.to_string()));
            }
        } else if let Some(id) = v.get("ie").and_then(Value::as_u64) {
            next_expr = next_expr.max(id + 1);
            exprs.insert(id, v);
        } else if let Some((kind, body)) = v.as_object().and_then(|o| o.iter().next()) {
            decls.push((kind.clone(), body.clone()));
        }
    }
    // A name at the top level, such as `Gamma`: its id, if the export has it.
    let top = |s: &str| {
        names
            .iter()
            .filter(|(_, (pre, part))| *pre == 0 && part == s)
            .map(|(id, _)| *id)
            .min()
    };
    let gamma = top("Gamma").ok_or("the theory has no name Gamma")?;
    let string = top("String").ok_or("the theory has no name String")?;
    let declared = |name: u64, kind: &str| {
        decls
            .iter()
            .find(|(k, body)| k == kind && body.get("name").and_then(Value::as_u64) == Some(name))
    };
    let truth = top("True").filter(|&t| {
        decls.iter().any(|(k, body)| {
            k == "inductive"
                && body["types"]
                    .as_array()
                    .is_some_and(|ts| ts.iter().any(|x| x["name"].as_u64() == Some(t)))
        })
    });
    let obligation = top(crate::compare::THEOREM);
    if let Some(o) = obligation {
        if decls
            .iter()
            .any(|(_, body)| body.get("name").and_then(Value::as_u64) == Some(o))
        {
            return Err("the theory declares obligation".to_string());
        }
    }
    let (_, def) = declared(gamma, "def").ok_or("the theory doesn't define Gamma")?;
    if def["levelParams"].as_array().is_none_or(|p| !p.is_empty()) {
        return Err("Gamma has universe parameters".to_string());
    }
    let mut predicates = Vec::new();
    let mut e = expr(&exprs, &def["type"])?;
    while let Some(f) = e.get("forallE") {
        let name = f["name"].as_u64().and_then(|n| names.get(&n));
        let name = match name {
            Some((0, s)) if identifier(s) => s.clone(),
            _ => return Err("a predicate of Gamma isn't named as a plain identifier".to_string()),
        };
        let n = arity(&exprs, expr(&exprs, &f["type"])?, string)?
            .ok_or_else(|| format!("predicate {name} isn't over strings, to Prop"))?;
        if predicates.iter().any(|(p, _)| *p == name) {
            return Err(format!("Gamma has two predicates {name}"));
        }
        predicates.push((name, n));
        e = expr(&exprs, &f["body"])?;
    }
    if predicates.is_empty() || !is_prop(e) {
        return Err("Gamma isn't a proposition over predicates".to_string());
    }
    Ok(Theory {
        text,
        predicates,
        gamma,
        string,
        truth,
        obligation,
        next_name,
        next_expr,
    })
}

/// A term of the statement, before it is numbered.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Term {
    BVar(usize),
    Prop,
    Const(u64),
    Str(String),
    App(Box<Term>, Box<Term>),
    Pi(Box<Term>, Box<Term>),
    Lam(Box<Term>, Box<Term>),
}

fn app(f: Term, a: Term) -> Term {
    Term::App(Box::new(f), Box::new(a))
}

fn pi(ty: Term, body: Term) -> Term {
    Term::Pi(Box::new(ty), Box::new(body))
}

/// An atom, `pred` applied to its arguments: what to apply, and the Lean text.
struct Atom {
    pred: usize,
    args: Vec<String>,
}

fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => out.push_str(&format!("\\x{:02x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// The statement, as a term over the theory's constants and as Lean.
fn statement(theory: &Theory, call: &Call) -> Result<(Term, String), String> {
    let k = theory.predicates.len();
    let arrow = |n: usize, to: Term| (0..n).fold(to, |t, _| pi(Term::Const(theory.string), t));
    let index = |pred: &str| {
        theory
            .predicates
            .iter()
            .position(|(p, _)| p == pred)
            .ok_or_else(|| format!("Gamma has no predicate {pred}"))
    };
    let atom = |pred: &str, args: Vec<String>| -> Result<Atom, String> {
        let i = index(pred)?;
        let want = theory.predicates[i].1;
        if args.len() != want {
            return Err(format!("{pred} takes {want} arguments, not {}", args.len()));
        }
        Ok(Atom { pred: i, args })
    };
    let gamma_text = |args: Vec<String>| format!("Gamma {}", args.join(" "));
    if let Goal::Consistent = call.goal {
        if !call.facts.is_empty() {
            return Err("consistency takes no facts".to_string());
        }
        let truth = theory.truth.ok_or("the theory doesn't declare True")?;
        let mut term = Term::Const(theory.gamma);
        let mut text = Vec::new();
        for (_, n) in &theory.predicates {
            let lam = (0..*n).fold(Term::Const(truth), |t, _| {
                Term::Lam(Box::new(Term::Const(theory.string)), Box::new(t))
            });
            term = app(term, lam);
            text.push(format!("(fun {}=> True)", "_ ".repeat(*n)));
        }
        return Ok((term, gamma_text(text)));
    }
    let Goal::Atom { pred, args } = &call.goal else {
        unreachable!()
    };
    let goal = atom(pred, args.clone())?;
    let mut facts = BTreeSet::new();
    for (pred, args) in &call.facts {
        facts.insert((index(pred)?, args.clone()));
    }
    let mut hypotheses: Vec<Atom> = Vec::new();
    for (pred, args) in facts {
        hypotheses.push(atom(&theory.predicates[pred].0, args)?);
    }
    // Under `depth` binders, predicate `i` (the outermost first) is `BVar(depth - 1 - i)`.
    let applied = |a: &Atom, depth: usize| {
        let head = Term::BVar(depth - 1 - a.pred);
        a.args.iter().fold(head, |t, s| app(t, Term::Str(s.clone())))
    };
    let shown = |a: &Atom| {
        let mut parts = vec![theory.predicates[a.pred].0.clone()];
        parts.extend(a.args.iter().map(|s| quote(s)));
        parts.join(" ")
    };
    let n = hypotheses.len();
    let mut body = applied(&goal, k + 1 + n);
    for (i, h) in hypotheses.iter().enumerate().rev() {
        body = pi(applied(h, k + 1 + i), body);
    }
    let holds = (0..k).fold(Term::Const(theory.gamma), |t, i| app(t, Term::BVar(k - 1 - i)));
    body = pi(holds, body);
    for (_, arity) in theory.predicates.iter().rev() {
        body = pi(arrow(*arity, Term::Prop), body);
    }

    let names: Vec<String> = theory.predicates.iter().map(|(p, _)| p.clone()).collect();
    let mut by_arity: Vec<(usize, Vec<String>)> = Vec::new();
    for (p, a) in &theory.predicates {
        match by_arity.last_mut() {
            Some((n, ps)) if n == a => ps.push(p.clone()),
            _ => by_arity.push((*a, vec![p.clone()])),
        }
    }
    let binders: Vec<String> = by_arity
        .iter()
        .map(|(a, ps)| format!("({} : {}Prop)", ps.join(" "), "String -> ".repeat(*a)))
        .collect();
    let mut chain = vec![gamma_text(names)];
    chain.extend(hypotheses.iter().map(shown));
    chain.push(shown(&goal));
    let text = format!("forall {}, {}", binders.join(" "), chain.join(" -> "));
    Ok((body, text))
}

/// Appends a term's expressions to `out`, each after the ones it uses, and gives its id.
fn emit(t: &Term, next: &mut u64, seen: &mut HashMap<Term, u64>, out: &mut String) -> u64 {
    if let Some(&id) = seen.get(t) {
        return id;
    }
    let line = match t {
        Term::BVar(i) => json!({ "bvar": i }),
        Term::Prop => json!({ "sort": 0 }),
        Term::Const(name) => json!({ "const": { "name": name, "us": [] } }),
        Term::Str(s) => json!({ "strVal": s }),
        Term::App(f, a) => {
            let (f, a) = (emit(f, next, seen, out), emit(a, next, seen, out));
            json!({ "app": { "fn": f, "arg": a } })
        }
        Term::Pi(ty, body) | Term::Lam(ty, body) => {
            let (ty, body) = (emit(ty, next, seen, out), emit(body, next, seen, out));
            let binder = json!({ "binderInfo": "default", "body": body, "name": 0, "type": ty });
            if matches!(t, Term::Pi(..)) {
                json!({ "forallE": binder })
            } else {
                json!({ "lam": binder })
            }
        }
    };
    let id = *next;
    *next += 1;
    let mut line = line;
    line["ie"] = json!(id);
    out.push_str(&line.to_string());
    out.push('\n');
    seen.insert(t.clone(), id);
    id
}

/// The call's challenge: the theory's export, with `obligation` stating what the call asks.
pub fn challenge(theory: &[u8], call: &Call) -> Result<Vec<u8>, String> {
    let theory = read(theory)?;
    let (term, _) = statement(&theory, call)?;
    let mut out = theory.text.to_string();
    if !out.ends_with('\n') {
        out.push('\n');
    }
    let obligation = match theory.obligation {
        Some(id) => id,
        None => {
            let id = theory.next_name;
            out.push_str(&json!({ "in": id, "str": { "pre": 0, "str": crate::compare::THEOREM } }).to_string());
            out.push('\n');
            id
        }
    };
    let mut next = theory.next_expr;
    let ty = emit(&term, &mut next, &mut HashMap::new(), &mut out);
    // A challenge's proof is never read: a theorem is compared by what it says.
    let thm = json!({ "thm": { "all": [obligation], "levelParams": [], "name": obligation, "type": ty, "value": ty } });
    out.push_str(&thm.to_string());
    out.push('\n');
    Ok(out.into_bytes())
}

/// The call's statement as Lean, for `theorem obligation : <statement> := ...` after the theory's own text.
pub fn lean(theory: &[u8], call: &Call) -> Result<String, String> {
    let theory = read(theory)?;
    Ok(statement(&theory, call)?.1)
}

/// The theory's predicates, in `Gamma`'s order, with how many strings each takes, as JSON:
/// `[{ "name": "late", "arity": 1 }, ...]`.
pub fn predicates(theory: &[u8]) -> Result<String, String> {
    let theory = read(theory)?;
    let list: Vec<Value> = theory
        .predicates
        .iter()
        .map(|(name, arity)| json!({ "name": name, "arity": arity }))
        .collect();
    Ok(Value::Array(list).to_string())
}
