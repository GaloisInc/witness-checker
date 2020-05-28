use scale_isa;
use scale_isa::types as instr;  // For accessing Instruction smart constructors
use scale_isa::types::{
    Instruction, Imm, RegClearModp, RegClearRegint, RegSecretBit, RegSecretModp, RegSecretRegint,
};

#[derive(Clone, Default)]
pub struct Counter {
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
pub trait RegType: Copy + Eq {
    fn new(x: u32) -> Self;
    fn desc() -> &'static str;
    fn get_counter(b: &mut Builder) -> &mut Counter;

    fn ld(self, imm: Imm) -> Instruction {
        panic!("ld not supported for {}", Self::desc())
    }

    fn print(self) -> Instruction {
        panic!("print not supported for {}", Self::desc())
    }

    fn add(self, a: Self, b: Self) -> Instruction {
        panic!("add not supported for {}", Self::desc())
    }

    fn sub(self, a: Self, b: Self) -> Instruction {
        panic!("sub not supported for {}", Self::desc())
    }

    fn mul(self, a: Self, b: Self) -> Instruction {
        panic!("mul not supported for {}", Self::desc())
    }

    fn neg(self, a: Self) -> Instruction {
        panic!("neg not supported for {}", Self::desc())
    }

    fn and(self, a: Self, b: Self) -> Instruction {
        panic!("and not supported for {}", Self::desc())
    }

    fn or(self, a: Self, b: Self) -> Instruction {
        panic!("or not supported for {}", Self::desc())
    }

    fn xor(self, a: Self, b: Self) -> Instruction {
        panic!("xor not supported for {}", Self::desc())
    }

    fn not(self, a: Self) -> Instruction {
        panic!("not not supported for {}", Self::desc())
    }

    fn eqz(dest: RegSecretBit, a: Self) -> Instruction {
        panic!("eqz not supported for {}", Self::desc())
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
    fn and(self, a: Self, b: Self) -> Instruction { instr::andsb(0, self, a, b) }
    fn or(self, a: Self, b: Self) -> Instruction { instr::orsb(0, self, a, b) }
    fn xor(self, a: Self, b: Self) -> Instruction { instr::xorsb(0, self, a, b) }
    fn not(self, a: Self) -> Instruction { instr::negb(0, self, a) }
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
    fn add(self, a: Self, b: Self) -> Instruction { instr::addsint(0, self, a, b) }
    fn sub(self, a: Self, b: Self) -> Instruction { instr::subsint(0, self, a, b) }
    fn mul(self, a: Self, b: Self) -> Instruction { instr::mulsint(0, self, a, b) }
    fn neg(self, a: Self) -> Instruction { instr::neg(0, self, a) }
    fn and(self, a: Self, b: Self) -> Instruction { instr::andsint(0, self, a, b) }
    fn or(self, a: Self, b: Self) -> Instruction { instr::orsint(0, self, a, b) }
    fn xor(self, a: Self, b: Self) -> Instruction { instr::xorsint(0, self, a, b) }
    fn eqz(dest: RegSecretBit, a: Self) -> Instruction { instr::eqzsint(0, dest, a) }
}


pub trait Mux {
    fn mux(b: &mut Builder, cond: RegSecretBit, then: Self, else_: Self) -> Self;
}

impl Mux for RegSecretRegint {
    fn mux(b: &mut Builder, cond: RegSecretBit, then: Self, else_: Self) -> Self {
        // `cond` as a SecretRegint
        let cond_sr = b.sb_to_sr(cond);
        // `mask` is all-ones if `cond` is 1, otherwise zero.
        let cond_mask = b.neg(cond_sr);

        let one = b.ld(1);
        let not_cond_sr = b.sub(one, cond_sr);
        let not_cond_mask = b.neg(not_cond_sr);

        let then_masked = b.and(then, cond_mask);
        let else_masked = b.and(else_, not_cond_mask);
        b.or(then_masked, else_masked)
    }
}

impl Mux for RegSecretBit {
    fn mux(b: &mut Builder, cond: RegSecretBit, then: Self, else_: Self) -> Self {
        let then_masked = b.and(then, cond);
        let not_cond = b.not(cond);
        let else_masked = b.and(else_, not_cond);
        b.or(then_masked, else_masked)
    }
}

impl<T: Mux> Mux for Vec<T> {
    fn mux(b: &mut Builder, cond: RegSecretBit, then: Self, else_: Self) -> Self {
        assert!(then.len() == else_.len(), "can't mux vectors of unequal len");
        then.into_iter().zip(else_.into_iter()).map(|(x, y)| b.mux(cond, x, y)).collect()
    }
}


#[derive(Default)]
pub struct Builder {
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

    pub fn add<R: RegType>(&mut self, r1: R, r2: R) -> R {
        self.with_reg(|b, dest: R| b.emit(dest.add(r1, r2)))
    }

    pub fn sub<R: RegType>(&mut self, r1: R, r2: R) -> R {
        self.with_reg(|b, dest: R| b.emit(dest.sub(r1, r2)))
    }

    pub fn mul<R: RegType>(&mut self, r1: R, r2: R) -> R {
        self.with_reg(|b, dest: R| b.emit(dest.mul(r1, r2)))
    }

    pub fn neg<R: RegType>(&mut self, r: R) -> R {
        self.with_reg(|b, dest: R| b.emit(dest.neg(r)))
    }

    pub fn and<R: RegType>(&mut self, r1: R, r2: R) -> R {
        self.with_reg(|b, dest: R| b.emit(dest.and(r1, r2)))
    }

    pub fn or<R: RegType>(&mut self, r1: R, r2: R) -> R {
        self.with_reg(|b, dest: R| b.emit(dest.or(r1, r2)))
    }

    pub fn xor<R: RegType>(&mut self, r1: R, r2: R) -> R {
        self.with_reg(|b, dest: R| b.emit(dest.xor(r1, r2)))
    }

    pub fn not<R: RegType>(&mut self, r: R) -> R {
        self.with_reg(|b, dest: R| b.emit(dest.not(r)))
    }

    pub fn eqz<R: RegType>(&mut self, r1: R) -> RegSecretBit {
        self.with_reg(|b, dest| b.emit(R::eqz(dest, r1)))
    }

    pub fn eq<R: RegType>(&mut self, r1: R, r2: R) -> RegSecretBit {
        let diff = self.sub(r1, r2);
        self.eqz(diff)
    }

    pub fn sb_to_sr(&mut self, r: RegSecretBit) -> RegSecretRegint {
        let zero = self.ld(0);
        self.with_reg(|b, dest| b.emit(instr::sintsbit(0, dest, zero, r, Imm::new(0))))
    }

    // TODO: generalize
    pub fn reveal(&mut self, r: RegSecretRegint) -> RegClearRegint {
        self.with_reg(|b, dest| b.emit(instr::opensint(0, dest, r)))
    }


    pub fn mux<T: Mux>(&mut self, cond: RegSecretBit, then: T, else_: T) -> T {
        T::mux(self, cond, then, else_)
    }

    pub fn match_<T: Mux>(
        &mut self,
        scrutinee: RegSecretRegint,
        opts: impl Iterator<Item = usize>,
        default: T,
        mut f: impl FnMut(&mut Self, usize) -> T,
    ) -> T {
        let mut val = None;
        for opt in opts {
            let opt_sr = self.ld(opt as u32);
            let chosen = self.eq(scrutinee, opt_sr);

            let cur = f(self, opt);
            val = Some(match val {
                None => cur,
                Some(prev) => self.mux(chosen, cur, prev),
            });
        }

        val.unwrap_or_else(|| panic!("can't index in an empty collection"))
    }

    /// Index a collection with a secret regint, producing a secret result.
    pub fn index<T: Copy + Mux>(
        &mut self,
        arr: &[T],
        idx: RegSecretRegint,
    ) -> T {
        let mut val = None;
        for (i, &cur) in arr.iter().enumerate() {
            let i_sr = self.ld(i as u32);
            let chosen = self.eq(idx, i_sr);

            val = Some(match val {
                None => cur,
                Some(prev) => self.mux(chosen, cur, prev),
            });
        }

        val.unwrap_or_else(|| panic!("can't index in an empty collection"))
    }
}
