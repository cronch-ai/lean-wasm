//! Whether a solution proves the challenge's theorem, as Comparator decides it: its `obligation` has the challenge's
//! type, and every declaration that type uses, and every declaration those use, is the challenge's. So a solution
//! can't change what a name, a notation or an instance in the statement means. Whether its proof is a proof is
//! nanoda's to check.
//!
//! The two exports number their names, levels and expressions independently, so each is read into one shared,
//! canonical form first: two terms are the same exactly when their canonical ids are. Binder names and metadata
//! don't change what a term means, so they are left out. A field this file doesn't know is refused, never compared.

use serde_json::{Map, Value};
use std::collections::{HashMap, HashSet};

/// The theorem a solution proves, as the kernel's `proofs/check-lean.mjs` names it.
pub const THEOREM: &str = "obligation";

/// The declarations Lean's kernel gives a meaning of its own (the quotient, the axioms, and the literals' types and
/// operations), whatever the statement uses. Comparator exports and compares these too, so a solution can't redefine
/// `Nat.add` while the kernel computes it. Both exports must hold them: export with `obligation` and these names.
pub const BUILTINS: &[&str] = &[
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

/// A name, level or expression, with its parts as canonical ids.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Node {
    Anonymous,
    Str(u32, String),
    Num(u32, u64),
    Zero,
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
    BVar(u64),
    Sort(u32),
    Const(u32, Vec<u32>),
    App(u32, u32),
    Lam(u32, u32),
    Pi(u32, u32),
    Let(u32, u32, u32),
    NatLit(String),
    StrLit(String),
    Proj(u32, u64, u32),
}

#[derive(Default)]
struct Interner {
    ids: HashMap<Node, u32>,
    nodes: Vec<Node>,
}

impl Interner {
    fn id(&mut self, node: Node) -> u32 {
        if let Some(&id) = self.ids.get(&node) {
            return id;
        }
        let id = self.nodes.len() as u32;
        self.nodes.push(node.clone());
        self.ids.insert(node, id);
        id
    }

    /// The canonical id of a dotted name such as `Quot.mk`.
    fn name(&mut self, dotted: &str) -> u32 {
        let mut id = self.id(Node::Anonymous);
        for part in dotted.split('.') {
            id = self.id(Node::Str(id, part.to_string()));
        }
        id
    }

    fn show(&self, id: u32) -> String {
        match &self.nodes[id as usize] {
            Node::Str(pre, s) if matches!(self.nodes[*pre as usize], Node::Anonymous) => s.clone(),
            Node::Str(pre, s) => format!("{}.{s}", self.show(*pre)),
            Node::Num(pre, i) => format!("{}.{i}", self.show(*pre)),
            _ => "[anonymous]".to_string(),
        }
    }
}

/// A declaration: its kind, its canonical form, and the expressions whose constants it uses.
struct Decl {
    kind: String,
    canon: Value,
    exprs: Vec<u32>,
}

/// An export's declarations, by canonical name. Each name an inductive block declares maps to the whole block.
struct Export {
    decls: HashMap<u32, Decl>,
}

/// One export's ids, mapped to canonical ids.
struct Reader<'i> {
    interner: &'i mut Interner,
    names: HashMap<u64, u32>,
    levels: HashMap<u64, u32>,
    exprs: HashMap<u64, u32>,
}

fn num(v: Option<&Value>, what: &str) -> Result<u64, String> {
    v.and_then(Value::as_u64)
        .ok_or_else(|| format!("{what} isn't a number"))
}

fn text(v: Option<&Value>, what: &str) -> Result<String, String> {
    v.and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| format!("{what} isn't a string"))
}

fn object<'v>(v: Option<&'v Value>, what: &str) -> Result<&'v Map<String, Value>, String> {
    v.and_then(Value::as_object)
        .ok_or_else(|| format!("{what} isn't an object"))
}

/// Scalar fields of a declaration, compared as they are.
const SCALARS: &[&str] = &[
    "hints",
    "safety",
    "isUnsafe",
    "numParams",
    "numIndices",
    "numFields",
    "nfields",
    "cidx",
    "numNested",
    "numMotives",
    "numMinors",
    "k",
    "isReflexive",
    "isRec",
    "kind",
];

const DECLS: &[&str] = &["def", "thm", "axiom", "opaque", "quot", "inductive"];

impl Reader<'_> {
    fn name(&self, v: Option<&Value>) -> Result<u32, String> {
        let id = num(v, "a name")?;
        self.names
            .get(&id)
            .copied()
            .ok_or_else(|| format!("name {id} isn't defined"))
    }

    fn level(&self, v: Option<&Value>) -> Result<u32, String> {
        let id = num(v, "a level")?;
        self.levels
            .get(&id)
            .copied()
            .ok_or_else(|| format!("level {id} isn't defined"))
    }

    fn expr(&self, v: Option<&Value>) -> Result<u32, String> {
        let id = num(v, "an expression")?;
        self.exprs
            .get(&id)
            .copied()
            .ok_or_else(|| format!("expression {id} isn't defined"))
    }

    fn define(table: &mut HashMap<u64, u32>, id: u64, canonical: u32) -> Result<(), String> {
        if table.insert(id, canonical).is_some() {
            return Err(format!("{id} is defined twice"));
        }
        Ok(())
    }

    fn read_name(&mut self, o: &Map<String, Value>) -> Result<(), String> {
        let id = num(o.get("in"), "in")?;
        let node = if let Some(s) = o.get("str") {
            let s = object(Some(s), "str")?;
            Node::Str(self.name(s.get("pre"))?, text(s.get("str"), "str")?)
        } else if let Some(n) = o.get("num") {
            let n = object(Some(n), "num")?;
            Node::Num(self.name(n.get("pre"))?, num(n.get("i"), "i")?)
        } else {
            return Err("a name is neither str nor num".to_string());
        };
        let canonical = self.interner.id(node);
        Self::define(&mut self.names, id, canonical)
    }

    fn read_level(&mut self, o: &Map<String, Value>) -> Result<(), String> {
        let id = num(o.get("il"), "il")?;
        let pair = |r: &Self, v: Option<&Value>| -> Result<(u32, u32), String> {
            match v.and_then(Value::as_array).map(Vec::as_slice) {
                Some([a, b]) => Ok((r.level(Some(a))?, r.level(Some(b))?)),
                _ => Err("max and imax take two levels".to_string()),
            }
        };
        let node = if let Some(l) = o.get("succ") {
            Node::Succ(self.level(Some(l))?)
        } else if o.contains_key("max") {
            let (a, b) = pair(self, o.get("max"))?;
            Node::Max(a, b)
        } else if o.contains_key("imax") {
            let (a, b) = pair(self, o.get("imax"))?;
            Node::IMax(a, b)
        } else if let Some(n) = o.get("param") {
            Node::Param(self.name(Some(n))?)
        } else {
            return Err("unknown level".to_string());
        };
        let canonical = self.interner.id(node);
        Self::define(&mut self.levels, id, canonical)
    }

    fn read_expr(&mut self, o: &Map<String, Value>) -> Result<(), String> {
        let id = num(o.get("ie"), "ie")?;
        let (kind, body) = o
            .iter()
            .find(|(k, _)| k.as_str() != "ie")
            .ok_or("an expression has no body")?;
        let b = |what: &str| object(Some(body), what);
        let canonical = match kind.as_str() {
            // Metadata doesn't change what a term means.
            "mdata" => self.expr(b("mdata")?.get("expr"))?,
            _ => {
                let node = match kind.as_str() {
                    "bvar" => Node::BVar(num(Some(body), "bvar")?),
                    "sort" => Node::Sort(self.level(Some(body))?),
                    "const" => {
                        let c = b("const")?;
                        let us = c
                            .get("us")
                            .and_then(Value::as_array)
                            .ok_or("const has no us")?
                            .iter()
                            .map(|u| self.level(Some(u)))
                            .collect::<Result<_, _>>()?;
                        Node::Const(self.name(c.get("name"))?, us)
                    }
                    "app" => {
                        let a = b("app")?;
                        Node::App(self.expr(a.get("fn"))?, self.expr(a.get("arg"))?)
                    }
                    "lam" | "forallE" => {
                        let l = b(kind)?;
                        let (ty, body) = (self.expr(l.get("type"))?, self.expr(l.get("body"))?);
                        if kind == "lam" {
                            Node::Lam(ty, body)
                        } else {
                            Node::Pi(ty, body)
                        }
                    }
                    "letE" => {
                        let l = b("letE")?;
                        Node::Let(
                            self.expr(l.get("type"))?,
                            self.expr(l.get("value"))?,
                            self.expr(l.get("body"))?,
                        )
                    }
                    "natVal" => Node::NatLit(text(Some(body), "natVal")?),
                    "strVal" => Node::StrLit(text(Some(body), "strVal")?),
                    "proj" => {
                        let p = b("proj")?;
                        Node::Proj(
                            self.name(p.get("typeName"))?,
                            num(p.get("idx"), "idx")?,
                            self.expr(p.get("struct"))?,
                        )
                    }
                    other => return Err(format!("unknown expression {other}")),
                };
                self.interner.id(node)
            }
        };
        Self::define(&mut self.exprs, id, canonical)
    }

    /// A declaration's fields with ids made canonical. A theorem's proof is left out: it isn't part of what the
    /// theorem says.
    fn canon(&self, o: &Map<String, Value>, theorem: bool, exprs: &mut Vec<u32>) -> Result<Value, String> {
        let mut out = Map::new();
        for (k, v) in o {
            let names = |r: &Self, v: &Value| -> Result<Value, String> {
                v.as_array()
                    .ok_or_else(|| format!("{k} isn't a list"))?
                    .iter()
                    .map(|n| r.name(Some(n)).map(Value::from))
                    .collect::<Result<Vec<_>, _>>()
                    .map(Value::from)
            };
            let objects = |r: &Self, v: &Value, exprs: &mut Vec<u32>| -> Result<Value, String> {
                v.as_array()
                    .ok_or_else(|| format!("{k} isn't a list"))?
                    .iter()
                    .map(|x| r.canon(object(Some(x), k)?, false, exprs))
                    .collect::<Result<Vec<_>, _>>()
                    .map(Value::from)
            };
            let value = match k.as_str() {
                "name" | "induct" | "ctor" | "typeName" => Value::from(self.name(Some(v))?),
                "all" | "levelParams" => names(self, v)?,
                // In an inductive block, a list of constructors; in one of its types, a list of their names.
                "ctors" if v.as_array().is_some_and(|a| a.iter().all(Value::is_number)) => names(self, v)?,
                "ctors" | "types" | "recs" | "rules" => objects(self, v, exprs)?,
                "value" if theorem => continue,
                "type" | "value" | "rhs" => {
                    let e = self.expr(Some(v))?;
                    exprs.push(e);
                    Value::from(e)
                }
                s if SCALARS.contains(&s) => v.clone(),
                other => return Err(format!("unknown field {other}")),
            };
            out.insert(k.clone(), value);
        }
        Ok(Value::Object(out))
    }
}

fn read(bytes: &[u8], interner: &mut Interner) -> Result<Export, String> {
    let text = std::str::from_utf8(bytes).map_err(|e| e.to_string())?;
    let mut r = Reader {
        interner,
        names: HashMap::new(),
        levels: HashMap::new(),
        exprs: HashMap::new(),
    };
    let anonymous = r.interner.id(Node::Anonymous);
    let zero = r.interner.id(Node::Zero);
    r.names.insert(0, anonymous);
    r.levels.insert(0, zero);
    let mut decls = HashMap::new();
    for (i, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let at = |e: String| format!("line {}: {e}", i + 1);
        let v: Value = serde_json::from_str(line).map_err(|e| at(e.to_string()))?;
        let o = v.as_object().ok_or_else(|| at("not an object".to_string()))?;
        if o.contains_key("meta") {
            continue;
        } else if o.contains_key("in") {
            r.read_name(o).map_err(at)?;
        } else if o.contains_key("il") {
            r.read_level(o).map_err(at)?;
        } else if o.contains_key("ie") {
            r.read_expr(o).map_err(at)?;
        } else {
            let (kind, body) = match o.iter().next() {
                Some((k, b)) if o.len() == 1 && DECLS.contains(&k.as_str()) => (k.clone(), b),
                _ => return Err(at("unknown line".to_string())),
            };
            let body = object(Some(body), &kind).map_err(at)?;
            let mut exprs = Vec::new();
            let canon = r.canon(body, kind == "thm", &mut exprs).map_err(at)?;
            let mut declared = Vec::new();
            if kind == "inductive" {
                for part in ["types", "ctors", "recs"] {
                    for x in body.get(part).and_then(Value::as_array).into_iter().flatten() {
                        declared.push(r.name(x.get("name")).map_err(at)?);
                    }
                }
            } else {
                declared.push(r.name(body.get("name")).map_err(at)?);
            }
            for name in declared {
                let decl = Decl {
                    kind: kind.clone(),
                    canon: canon.clone(),
                    exprs: exprs.clone(),
                };
                if decls.insert(name, decl).is_some() {
                    return Err(at(format!("{} is declared twice", r.interner.show(name))));
                }
            }
        }
    }
    Ok(Export { decls })
}

/// The constants and structure names `exprs` use, pushed to `todo`. `seen` is shared across calls, so each canonical
/// expression is walked once.
fn constants(interner: &Interner, exprs: &[u32], seen: &mut HashSet<u32>, todo: &mut Vec<u32>) {
    let mut stack = exprs.to_vec();
    while let Some(e) = stack.pop() {
        if !seen.insert(e) {
            continue;
        }
        match &interner.nodes[e as usize] {
            Node::Const(name, _) => todo.push(*name),
            Node::App(a, b) | Node::Lam(a, b) | Node::Pi(a, b) => stack.extend([*a, *b]),
            Node::Let(a, b, c) => stack.extend([*a, *b, *c]),
            Node::Proj(name, _, s) => {
                todo.push(*name);
                stack.push(*s);
            }
            _ => {}
        }
    }
}

/// `Ok` when `solution`'s `obligation` says what `challenge`'s does, with every declaration it rests on the same.
pub fn compare(challenge: &[u8], solution: &[u8]) -> Result<(), String> {
    let mut interner = Interner::default();
    let c = read(challenge, &mut interner).map_err(|e| format!("the challenge: {e}"))?;
    let s = read(solution, &mut interner).map_err(|e| format!("the solution: {e}"))?;
    let theorem = interner.name(THEOREM);
    let (ct, st) = match (c.decls.get(&theorem), s.decls.get(&theorem)) {
        (Some(ct), Some(st)) if ct.kind == "thm" && st.kind == "thm" => (ct, st),
        (Some(ct), _) if ct.kind == "thm" => return Err(format!("the solution has no theorem {THEOREM}")),
        _ => return Err(format!("the challenge has no theorem {THEOREM}")),
    };
    if ct.canon != st.canon {
        return Err(format!("{THEOREM} doesn't have the challenge's statement"));
    }
    let mut todo: Vec<u32> = BUILTINS.iter().map(|n| interner.name(n)).collect();
    let mut seen_exprs = HashSet::new();
    constants(&interner, &ct.exprs, &mut seen_exprs, &mut todo);
    let mut seen = HashSet::new();
    while let Some(name) = todo.pop() {
        if !seen.insert(name) {
            continue;
        }
        let shown = || interner.show(name);
        let cd = c
            .decls
            .get(&name)
            .ok_or_else(|| format!("the challenge doesn't declare {}", shown()))?;
        let sd = s
            .decls
            .get(&name)
            .ok_or_else(|| format!("the solution doesn't declare {}", shown()))?;
        if cd.kind != sd.kind || cd.canon != sd.canon {
            return Err(format!("{} isn't the challenge's", shown()));
        }
        constants(&interner, &cd.exprs, &mut seen_exprs, &mut todo);
    }
    Ok(())
}
