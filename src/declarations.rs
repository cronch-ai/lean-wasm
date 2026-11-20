//! Every declaration in an export, with a digest that names it whatever export it came from: what a proof-checker
//! stores each declaration under, so one checked in one proof is the same record in every other.
//!
//! A digest is SHA-256 over a tagged encoding (README.md, "Declarations"). Names, levels and expressions are hashed
//! by structure, so how an export numbers them doesn't matter. A declaration's digest covers its canonical form, a
//! theorem's proof, and the digest of each declaration it uses: change anything it rests on, and it changes too.

use crate::compare::{self, Decl, Field, Interner, Node, Tree};
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use std::collections::{BTreeSet, HashMap, HashSet};

type Digest = [u8; 32];

/// Bytes to hash: each part tagged, and each variable-length part prefixed with its length.
#[derive(Default)]
struct Enc(Vec<u8>);

impl Enc {
    fn tag(mut self, t: u8) -> Self {
        self.0.push(t);
        self
    }
    fn num(mut self, n: u64) -> Self {
        self.0.extend_from_slice(&n.to_be_bytes());
        self
    }
    fn text(self, s: &str) -> Self {
        let mut e = self.num(s.len() as u64);
        e.0.extend_from_slice(s.as_bytes());
        e
    }
    fn digest(mut self, d: &Digest) -> Self {
        self.0.extend_from_slice(d);
        self
    }
    fn finish(self) -> Digest {
        Sha256::digest(&self.0).into()
    }
}

/// Every interned node's digest, by canonical id. A node's parts have smaller ids, so one pass in order does.
fn nodes(interner: &Interner) -> Vec<Digest> {
    let mut out: Vec<Digest> = Vec::with_capacity(interner.nodes.len());
    for node in &interner.nodes {
        let d = |id: &u32| out[*id as usize];
        let e = Enc::default();
        let digest = match node {
            Node::Anonymous => e.tag(0x00),
            Node::Str(pre, s) => e.tag(0x01).digest(&d(pre)).text(s),
            Node::Num(pre, i) => e.tag(0x02).digest(&d(pre)).num(*i),
            Node::Zero => e.tag(0x10),
            Node::Succ(l) => e.tag(0x11).digest(&d(l)),
            Node::Max(a, b) => e.tag(0x12).digest(&d(a)).digest(&d(b)),
            Node::IMax(a, b) => e.tag(0x13).digest(&d(a)).digest(&d(b)),
            Node::Param(n) => e.tag(0x14).digest(&d(n)),
            Node::BVar(i) => e.tag(0x20).num(*i),
            Node::Sort(l) => e.tag(0x21).digest(&d(l)),
            Node::Const(n, us) => us
                .iter()
                .fold(e.tag(0x22).digest(&d(n)).num(us.len() as u64), |e, u| e.digest(&d(u))),
            Node::App(f, a) => e.tag(0x23).digest(&d(f)).digest(&d(a)),
            Node::Lam(t, b) => e.tag(0x24).digest(&d(t)).digest(&d(b)),
            Node::Pi(t, b) => e.tag(0x25).digest(&d(t)).digest(&d(b)),
            Node::Let(t, v, b) => e.tag(0x26).digest(&d(t)).digest(&d(v)).digest(&d(b)),
            Node::NatLit(n) => e.tag(0x27).text(n),
            Node::StrLit(s) => e.tag(0x28).text(s),
            Node::Proj(n, i, s) => e.tag(0x29).digest(&d(n)).num(*i).digest(&d(s)),
        }
        .finish();
        out.push(digest);
    }
    out
}

fn tree(t: &Tree, nodes: &[Digest]) -> Digest {
    let d = |id: &u32| &nodes[*id as usize];
    let mut e = Enc::default().tag(0x30).num(t.len() as u64);
    for (key, field) in t {
        e = e.text(key);
        e = match field {
            Field::Name(n) => e.tag(0x31).digest(d(n)),
            Field::Names(ns) => ns.iter().fold(e.tag(0x32).num(ns.len() as u64), |e, n| e.digest(d(n))),
            Field::Expr(x) => e.tag(0x33).digest(d(x)),
            Field::Trees(ts) => ts
                .iter()
                .fold(e.tag(0x34).num(ts.len() as u64), |e, t| e.digest(&tree(t, nodes))),
            Field::Scalar(v) => e.tag(0x35).text(&v.to_string()),
        };
    }
    e.finish()
}

fn hex(d: &Digest) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}

/// What `report` says of one declaration.
struct Done {
    digest: Digest,
    axioms: BTreeSet<String>,
}

/// Every declaration in `export`, as JSON: `[{ names, kind, digest, uses, axioms }]`, ordered by first name. `uses` are
/// the declarations it references directly, and `axioms` every axiom it rests on, through its uses.
pub fn report(export: &[u8]) -> Result<String, String> {
    let mut interner = Interner::default();
    let x = compare::read(export, &mut interner)?;
    let digests = nodes(&interner);
    // Each block once, by its first name.
    let block = |name: &u32| -> &Decl { &x.decls[name] };
    let first = |name: &u32| block(name).names[0];

    let mut uses: HashMap<u32, BTreeSet<u32>> = HashMap::new();
    for decl in x.decls.values() {
        let key = decl.names[0];
        if uses.contains_key(&key) {
            continue;
        }
        let mut found = Vec::new();
        let exprs: Vec<u32> = decl.exprs.iter().copied().chain(decl.proof).collect();
        compare::constants(&interner, &exprs, &mut HashSet::new(), &mut found);
        let used = found
            .into_iter()
            .filter(|n| x.decls.contains_key(n) && !decl.names.contains(n))
            .collect();
        uses.insert(key, used);
    }

    // Each block after every block it uses, so its dependencies' digests are known.
    let mut done: HashMap<u32, Done> = HashMap::new();
    let mut keys: Vec<u32> = uses.keys().copied().collect();
    keys.sort_by_key(|k| interner.show(*k));
    for root in keys {
        let mut stack = vec![(root, false)];
        let mut open = HashSet::new();
        while let Some((key, expanded)) = stack.pop() {
            if done.contains_key(&key) {
                continue;
            }
            let deps: BTreeSet<u32> = uses[&key].iter().map(first).collect();
            if !expanded {
                if !open.insert(key) {
                    return Err(format!("{} depends on itself", interner.show(key)));
                }
                stack.push((key, true));
                stack.extend(deps.iter().filter(|d| !done.contains_key(d)).map(|d| (*d, false)));
                continue;
            }
            let decl = block(&key);
            let mut named: Vec<(String, u32)> = deps.iter().map(|d| (interner.show(*d), *d)).collect();
            named.sort();
            let mut e = Enc::default()
                .tag(0x40)
                .text(&decl.kind)
                .digest(&tree(&decl.canon, &digests));
            e = match decl.proof {
                Some(p) => e.tag(0x01).digest(&digests[p as usize]),
                None => e.tag(0x00),
            };
            e = e.num(named.len() as u64);
            let mut axioms = BTreeSet::new();
            if decl.kind == "axiom" {
                axioms.insert(interner.show(key));
            }
            for (_, dep) in &named {
                let theirs = &done[dep];
                e = e.digest(&digests[*dep as usize]).digest(&theirs.digest);
                axioms.extend(theirs.axioms.iter().cloned());
            }
            done.insert(
                key,
                Done {
                    digest: e.finish(),
                    axioms,
                },
            );
            open.remove(&key);
        }
    }

    let mut out: Vec<(String, Value)> = done
        .iter()
        .map(|(key, d)| {
            let decl = block(key);
            let mut used: Vec<String> = uses[key].iter().map(|n| interner.show(*n)).collect();
            used.sort();
            used.dedup();
            let shown = interner.show(*key);
            let value = json!({
                "names": decl.names.iter().map(|n| interner.show(*n)).collect::<Vec<_>>(),
                "kind": decl.kind,
                "digest": format!("sha256:{}", hex(&d.digest)),
                "uses": used,
                "axioms": d.axioms.iter().collect::<Vec<_>>(),
            });
            (shown, value)
        })
        .collect();
    out.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(Value::from(out.into_iter().map(|(_, v)| v).collect::<Vec<_>>()).to_string())
}

#[cfg(test)]
mod tests {
    use super::report;
    use serde_json::Value;

    /// `axiom a : Sort <level of a>`, then `def b : Sort 0 := Sort 0` and `def c := b`, numbered from `offset`.
    fn export(offset: u64, a_level: u64, reversed: bool) -> String {
        let n = |i: u64| i + offset;
        let mut names = vec![
            format!(r#"{{"in":{},"str":{{"pre":0,"str":"a"}}}}"#, n(1)),
            format!(r#"{{"in":{},"str":{{"pre":0,"str":"b"}}}}"#, n(2)),
            format!(r#"{{"in":{},"str":{{"pre":0,"str":"c"}}}}"#, n(3)),
        ];
        if reversed {
            names.reverse();
        }
        let mut lines = names;
        lines.push(format!(r#"{{"il":{},"succ":0}}"#, n(1)));
        let level = if a_level == 0 { 0 } else { n(1) };
        lines.extend([
            format!(r#"{{"ie":{},"sort":0}}"#, n(1)),
            format!(r#"{{"ie":{},"sort":{}}}"#, n(2), level),
            format!(r#"{{"ie":{},"const":{{"name":{},"us":[]}}}}"#, n(3), n(1)),
            format!(r#"{{"ie":{},"app":{{"fn":{},"arg":{}}}}}"#, n(4), n(3), n(1)),
            format!(r#"{{"ie":{},"const":{{"name":{},"us":[]}}}}"#, n(5), n(2)),
        ]);
        let mut decls = vec![
            format!(
                r#"{{"axiom":{{"name":{},"levelParams":[],"type":{},"isUnsafe":false}}}}"#,
                n(1),
                n(2)
            ),
            format!(
                r#"{{"def":{{"name":{},"levelParams":[],"type":{},"value":{},"hints":"opaque","safety":"safe","all":[{}]}}}}"#,
                n(2),
                n(1),
                n(4),
                n(2)
            ),
            format!(
                r#"{{"def":{{"name":{},"levelParams":[],"type":{},"value":{},"hints":"opaque","safety":"safe","all":[{}]}}}}"#,
                n(3),
                n(1),
                n(5),
                n(3)
            ),
        ];
        if reversed {
            decls.reverse();
        }
        lines.extend(decls);
        lines.join("\n")
    }

    fn digests(text: &str) -> Vec<(String, String)> {
        let v: Value = serde_json::from_str(&report(text.as_bytes()).unwrap()).unwrap();
        v.as_array()
            .unwrap()
            .iter()
            .map(|d| {
                (
                    d["names"][0].as_str().unwrap().to_string(),
                    d["digest"].as_str().unwrap().to_string(),
                )
            })
            .collect()
    }

    #[test]
    fn the_same_declarations_have_the_same_digests_however_they_are_numbered() {
        assert_eq!(digests(&export(0, 0, false)), digests(&export(40, 0, true)));
    }

    #[test]
    fn a_change_to_what_a_declaration_uses_changes_its_digest() {
        let before = digests(&export(0, 0, false));
        let after = digests(&export(0, 1, false));
        // `a` changed, so `b`, which uses it, and `c`, which uses `b`, change too.
        for (x, y) in before.iter().zip(&after) {
            assert_eq!(x.0, y.0);
            assert_ne!(x.1, y.1, "{}", x.0);
        }
    }

    #[test]
    fn uses_and_axioms_are_reported() {
        let v: Value = serde_json::from_str(&report(export(0, 0, false).as_bytes()).unwrap()).unwrap();
        let c = &v[2];
        assert_eq!(c["names"], serde_json::json!(["c"]));
        assert_eq!(c["uses"], serde_json::json!(["b"]));
        assert_eq!(c["axioms"], serde_json::json!(["a"]));
        assert_eq!(v[0]["kind"], "axiom");
    }
}
