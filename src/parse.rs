use std::str::FromStr;
use crate::builder::Builder;
use crate::tiny_ram::{RamInstr, RamState, Opcode, RAM_REGS};

pub fn parse_instr(b: &mut Builder, s: &str) -> RamInstr {
    let words = s.split(" ").collect::<Vec<_>>();
    assert!(words.len() == 5);
    let opcode = match words[0] {
        "mov" => Opcode::Mov,
        "add" => Opcode::Add,
        "sub" => Opcode::Sub,
        "mull" => Opcode::Mull,
        o => panic!("unknown opcode {}", o),
    };
    let dest = u32::from_str(words[1]).unwrap();
    let op1 = u32::from_str(words[2]).unwrap();
    let op2 = u32::from_str(words[3]).unwrap();
    let imm = match words[4] {
        "reg" => false,
        "imm" => true,
        x => panic!("unknown operand kind {}", x),
    };
    RamInstr::new(b, opcode, dest, op1, op2, imm)
}

pub fn parse_state(b: &mut Builder, s: &str) -> RamState {
    let mut pc = 0;
    let mut regs = [0; RAM_REGS];
    let mut flag = false;

    for part in s.split(";") {
        let words = part.trim().split(" ").collect::<Vec<_>>();
        match words[0] {
            "pc" => {
                assert!(words.len() == 2);
                pc = u32::from_str(words[1]).unwrap();
            },
            "regs" => {
                assert!(words.len() == 1 + regs.len());
                for (word, reg) in words[1..].iter().cloned().zip(regs.iter_mut()) {
                    *reg = u32::from_str(word).unwrap();
                }
            },
            "flag" => {
                assert!(words.len() == 2);
                flag = u8::from_str(words[1]).unwrap() != 0;
            },
            x => panic!("unknown state part {}", x),
        }
    }

    RamState::new(b, pc, regs, flag)
}
