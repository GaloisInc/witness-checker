use std::collections::{HashMap, HashSet};
use crate::ir::circuit::{self, Wire, Label};
use crate::ir::migrate::{self, Migrate};


#[derive(Clone, Debug, Default)]
pub struct Stats<'a> {
    map: HashMap<Label<'a>, usize>,
    seen: HashSet<Wire<'a>>,
}

impl<'a> Stats<'a> {
    pub fn new() -> Stats<'a> {
        Stats::default()
    }

    pub fn add_one(&mut self, w: Wire<'a>) {
        if self.seen.insert(w) {
            *self.map.entry(w.label).or_insert(0) += 1;
        }
    }

    pub fn add(&mut self, ws: &[Wire<'a>]) {
        self.add_iter(ws.iter().cloned());
    }

    pub fn add_iter(&mut self, ws: impl IntoIterator<Item = Wire<'a>>) {
        for w in circuit::walk_wires(ws) {
            self.add_one(w);
        }
    }

    fn to_count_tree(&self) -> CountTree {
        let mut tree = CountTree::default();

        for (&label, &n) in &self.map {
            let mut cur = &mut tree;
            cur.count += n;
            for part in label.0.trim_start_matches("/").split("/") {
                let part = part.to_owned().into_boxed_str();
                cur = cur.children.entry(part).or_insert_with(CountTree::default);
                cur.count += n;
            }
        }

        tree
    }

    pub fn print(&self) {
        self.to_count_tree().print();
    }
}

impl<'a, 'b> Migrate<'a, 'b> for Stats<'a> {
    type Output = Stats<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Stats<'b> {
        Stats {
            map: v.visit(self.map),
            seen: self.seen.into_iter().filter_map(|w| v.visit_wire_weak(w)).collect(),
        }
    }
}


#[derive(Default)]
struct CountTree {
    count: usize,
    children: HashMap<Box<str>, CountTree>,
}

impl CountTree {
    pub fn print(&self) {
        self.print_inner("", "all gates");
    }

    fn print_inner(&self, indent: &str, label: &str) {
        eprintln!("{}- {:9} {}", indent, self.count, label);

        let next_indent = format!("{}  ", indent);

        let mut keys = self.children.keys().collect::<Vec<_>>();
        keys.sort();
        for k in keys {
            let v = self.children.get(k).unwrap();
            v.print_inner(&next_indent, k);
        }
    }
}

