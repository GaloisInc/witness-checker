use std::collections::HashMap;
use crate::ir::circuit::{self, Wire};

#[derive(Default)]
struct CountTree<'a> {
    count: usize,
    children: HashMap<&'a str, CountTree<'a>>,
}

impl CountTree<'_> {
    pub fn print(&self, indent: &str, label: &str) {
        eprintln!("{}- {:9} {}", indent, self.count, label);

        let next_indent = format!("{}  ", indent);

        let mut keys = self.children.keys().cloned().collect::<Vec<_>>();
        keys.sort();
        for k in keys {
            let v = self.children.get(&k).unwrap();
            v.print(&next_indent, k);
        }
    }
}

pub fn count_gates<'a>(wires: &[Wire<'a>]) {
    let mut tree = CountTree::default();

    for w in circuit::walk_wires(wires.iter().cloned()) {
        let mut cur = &mut tree;
        cur.count += 1;
        for part in w.label.0.trim_start_matches("/").split("/") {
            cur = cur.children.entry(part).or_insert_with(CountTree::default);
            cur.count += 1;
        }
    }

    tree.print("", "all gates");
}
