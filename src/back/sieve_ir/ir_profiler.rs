use std::collections::{HashMap, HashSet};
use zki_sieve::producers::builder::BuildGate;

#[derive(Default)]
pub struct IRProfiler {
    gates: HashMap<BuildGate, ()>,
    notes: Vec<String>,

    duplicate_count: usize,
    duplicate_culprits: HashSet<String>,
}

impl IRProfiler {
    pub fn enter_note(&mut self, note: &str) {
        self.notes
            .push(format!("{}\t{}", self.current_note(), note));
    }

    pub fn exit_note(&mut self) {
        self.notes.pop();
    }

    pub fn notify_gate(&mut self, gate: &BuildGate) {
        let previous = self.gates.insert(gate.clone(), ());
        if previous.is_some() {
            self.duplicate_count += 1;
            self.duplicate_culprits
                .insert(self.current_note().to_string());
        }
    }

    fn current_note(&self) -> &str {
        self.notes.last().map(|s| s.as_str()).unwrap_or("")
    }

    pub fn print_report(&self) {
        println!(
            "IRProfiler found {} duplicates out of {} unique gates ({}%) from these contexts:",
            self.duplicate_count,
            self.gates.len(),
            100 * self.duplicate_count / self.gates.len(),
        );
        for culprit in self.duplicate_culprits.iter() {
            println!("{}", culprit.as_str());
        }
        println!();
    }
}
