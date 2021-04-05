use std::collections::{HashMap, HashSet};
use zki_sieve::producers::builder::BuildGate;
use BuildGate::*;

#[derive(Default)]
pub struct IRProfiler {
    pub warnings_panic: bool,

    gates: HashSet<BuildGate>,
    notes: Vec<String>,

    duplicate_count: usize,
    duplicate_culprits: HashMap<String, usize>,
}

impl IRProfiler {
    pub fn annotate(&mut self, note: &str) {
        self.notes
            .push(format!("{}\t/ {}", self.current_note(), note));
    }

    pub fn deannotate(&mut self) {
        self.notes.pop().expect("More deannotate than annotate");
    }

    fn current_note(&self) -> &str {
        self.notes.last().map(|s| s.as_str()).unwrap_or("")
    }

    pub fn notify_gate(&mut self, gate: &BuildGate) {
        match gate {
            Instance(_) => return,
            Witness(_) => return,
            _ => {}
        };

        let new = self.gates.insert(gate.clone());
        if !new {
            self.duplicate_count += 1;
            let culprit = self.current_note().to_string();
            let count = self.duplicate_culprits.entry(culprit).or_insert(0);
            *count += 1;

            if self.warnings_panic {
                panic!(
                    "IRProfiler (with warnings_panic=true) found a duplicated gate {:?} in {}",
                    gate,
                    self.current_note()
                );
            }
        }
    }

    pub fn print_report(&self) {
        eprintln!(
            "IRProfiler found {}% of duplicates ({} / {} unique gates), created from these contexts:",
            100 * self.duplicate_count / self.gates.len(),
            self.duplicate_count,
            self.gates.len(),
        );
        for (culprit, count) in self.duplicate_culprits.iter() {
            eprintln!(
                "{} {:.2}%",
                culprit.as_str(),
                100f32 * *count as f32 / self.gates.len() as f32
            );
        }
        if !self.notes.is_empty() {
            eprintln!(
                "IRProfiler incorrect usage: More annotate than deannotate ({}).",
                self.current_note()
            );
        }
        eprintln!();
    }
}
