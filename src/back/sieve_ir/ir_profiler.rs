use std::collections::HashMap;
use zki_sieve::producers::builder::BuildGate;
use BuildGate::*;

#[derive(Default)]
pub struct IRProfiler {
    pub warnings_panic: bool,

    gates: HashMap<BuildGate, ()>,
    notes: Vec<String>,

    duplicate_count: usize,
    duplicate_culprits: HashMap<String, usize>,
}

impl IRProfiler {
    pub fn enter_note(&mut self, note: &str) {
        self.notes
            .push(format!("{}\t{}", self.current_note(), note));
    }

    pub fn exit_note(&mut self) {
        self.notes.pop();
    }

    fn current_note(&self) -> &str {
        self.notes.last().map(|s| s.as_str()).unwrap_or("")
    }

    pub fn notify_gate(&mut self, gate: &BuildGate) {
        match gate {
            BuildGate::Instance(_) => return,
            BuildGate::Witness(_) => return,
            _ => {}
        };

        let previous = self.gates.insert(gate.clone(), ());
        if previous.is_some() {
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
        println!(
            "IRProfiler found {}% of duplicates ({} / {} unique gates), created from these contexts:",
            100 * self.duplicate_count / self.gates.len(),
            self.duplicate_count,
            self.gates.len(),
        );
        for (culprit, count) in self.duplicate_culprits.iter() {
            println!("{}: {}%", culprit.as_str(), 100 * count / self.gates.len());
        }
        println!();
    }
}
