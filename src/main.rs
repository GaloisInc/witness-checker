use std::fs::File;
use std::io::{self, BufWriter};
use scale_isa;
use scale_isa::types as instr;  // For accessing Instruction smart constructors
use scale_isa::types::{
    Instruction, Imm, RegClearModp, RegClearRegint, RegSecretBit, RegSecretModp, RegSecretRegint,
};

#[derive(Clone, Default)]
struct Counter {
    next: u32,
}

impl Counter {
    pub fn next(&mut self) -> u32 {
        let cur = self.next;
        self.next += 1;
        cur
    }
}


#[allow(unused_variables)]
trait RegType: Copy + Eq {
    fn new(x: u32) -> Self;
    fn desc() -> &'static str;
    fn get_counter(b: &mut Builder) -> &mut Counter;

    fn ld(self, imm: Imm) -> Instruction {
        panic!("ld not supported for {}", Self::desc())
    }

    fn print(self) -> Instruction {
        panic!("print not supported for {}", Self::desc())
    }
}

impl RegType for RegClearModp {
    fn new(x: u32) -> Self { Self::new(x) }
    fn desc() -> &'static str { "clear-modp" }
    fn get_counter(b: &mut Builder) -> &mut Counter {
        &mut b.next_clear_modp
    }

    fn ld(self, imm: Imm) -> Instruction { instr::ldi(0, self, imm) }
    fn print(self) -> Instruction { instr::print_reg(0, self) }
}

impl RegType for RegClearRegint {
    fn new(x: u32) -> Self { Self::new(x) }
    fn desc() -> &'static str { "clear-regint" }
    fn get_counter(b: &mut Builder) -> &mut Counter {
        &mut b.next_clear_regint
    }

    fn ld(self, imm: Imm) -> Instruction { instr::ldint(0, self, imm) }
    fn print(self) -> Instruction { instr::print_int(0, self) }
}

impl RegType for RegSecretBit {
    fn new(x: u32) -> Self { Self::new(x) }
    fn desc() -> &'static str { "secret-bit" }
    fn get_counter(b: &mut Builder) -> &mut Counter {
        &mut b.next_secret_bit
    }

    fn ld(self, imm: Imm) -> Instruction { instr::ldsbit(0, self, imm) }
}

impl RegType for RegSecretModp {
    fn new(x: u32) -> Self { Self::new(x) }
    fn desc() -> &'static str { "secret-modp" }
    fn get_counter(b: &mut Builder) -> &mut Counter {
        &mut b.next_secret_modp
    }

    fn ld(self, imm: Imm) -> Instruction { instr::ldsi(0, self, imm) }
}

impl RegType for RegSecretRegint {
    fn new(x: u32) -> Self { Self::new(x) }
    fn desc() -> &'static str { "secret-regint" }
    fn get_counter(b: &mut Builder) -> &mut Counter {
        &mut b.next_secret_regint
    }

    fn ld(self, imm: Imm) -> Instruction { instr::ldsint(0, self, imm) }
}


#[derive(Default)]
struct Builder {
    instrs: Vec<Instruction>,
    next_clear_modp: Counter,
    next_clear_regint: Counter,
    next_secret_bit: Counter,
    next_secret_modp: Counter,
    next_secret_regint: Counter,
}

impl Builder {
    pub fn alloc_reg<R: RegType>(&mut self) -> R {
        let x = R::get_counter(self).next();
        R::new(x)
    }

    pub fn with_reg<R, F>(&mut self, f: F) -> R
    where R: RegType, F: FnOnce(&mut Self, R) {
        let r = self.alloc_reg();
        f(self, r);
        r
    }

    pub fn emit(&mut self, instr: Instruction) {
        self.instrs.push(instr);
    }

    pub fn finish(self) -> Vec<Instruction> {
        self.instrs
    }


    pub fn ld<R: RegType>(&mut self, x: u32) -> R {
        self.with_reg(|b, r: R| b.emit(r.ld(Imm::new(x))))
    }

    pub fn print<R: RegType>(&mut self, r: R) {
        self.emit(r.print());
    }
}


fn main() -> io::Result<()> {
    let mut b = Builder::default();

    {
        let r = b.ld::<RegClearModp>(1234);
        b.print(r);
    }

    let instrs = b.finish();
    let mut f = BufWriter::new(File::create("out.bc")?);
    for i in instrs {
        scale_isa::functions::write_instruction(&mut f, i)?;
    }

    Ok(())
}
