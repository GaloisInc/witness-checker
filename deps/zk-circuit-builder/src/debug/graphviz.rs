use std::fmt::{self, Write};
use crate::ir::circuit::{self, CircuitBase, Field, Wire, GateKind, Ty, TyKind};
use crate::eval::{self, Evaluator, CachingEvaluator, Value};

fn write_val(s: &mut String, v: Value) -> Result<(), fmt::Error> {
    match v {
        Value::SingleInteger(i) => {
            write!(s, "0x{:x}", i)?;
        },
        Value::SingleField(f) => {
            write!(s, "{:?}", f)?;
        },
        Value::Bundle(vs) => {
            for (i, v) in vs.into_iter().enumerate() {
                if i == 0 { write!(s, "[")?; } else { write!(s, ", ")?; }
                write_val(s, v)?;
            }
            write!(s, "]")?;
        },
    }
    Ok(())
}

fn write_ty(s: &mut String, ty: Ty) -> Result<(), fmt::Error> {
    match *ty {
        TyKind::Uint(sz) => { write!(s, "u{}", sz.bits())?; },
        TyKind::Int(sz) => { write!(s, "i{}", sz.bits())?; },
        TyKind::GF(field) => match field {
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F40b => { write!(s, "gf40b")?; },
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F45b => { write!(s, "gf45b")?; },
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F56b => { write!(s, "gf56b")?; },
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F63b => { write!(s, "gf63b")?; },
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F64b => { write!(s, "gf64b")?; },
        },
        TyKind::Bundle(tys) => {
            for (i, &ty) in tys.iter().enumerate() {
                if i == 0 { write!(s, "[")?; } else { write!(s, ", ")?; }
                write_ty(s, ty)?;
            }
            write!(s, "]")?;
        },
        TyKind::RawBits => { write!(s, "raw_bits")?; },
    }
    Ok(())
}

pub fn make_graph<'a>(
    c: &'a CircuitBase<'a>,
    ws: impl Iterator<Item = Wire<'a>>,
) -> Result<String, fmt::Error> {
    let mut ev = CachingEvaluator::<eval::RevealSecrets, ()>::new();

    let mut s = String::new();
    writeln!(s, "digraph {{")?;

    let mut all_ws = Vec::new();
    for w in circuit::walk_wires(ws) {
        all_ws.push(w);

        let mut label = String::new();
        match w.kind {
            GateKind::Lit(_, _) => write!(label, "Lit")?,
            GateKind::Secret(_) => write!(label, "Secret")?,
            GateKind::Erased(e) => write!(label, "Erased {:p}", e)?,
            GateKind::Argument(i, _) => write!(label, "Argument {}", i)?,
            GateKind::Unary(op, _) => write!(label, "{:?}", op)?,
            GateKind::Binary(op, _, _) => write!(label, "{:?}", op)?,
            GateKind::Shift(op, _, _) => write!(label, "{:?}", op)?,
            GateKind::Compare(op, _, _) => write!(label, "{:?}", op)?,
            GateKind::Mux(_, _, _) => write!(label, "Mux")?,
            GateKind::Cast(_, _) => write!(label, "Cast")?,
            GateKind::Pack(_) => write!(label, "Pack")?,
            GateKind::Extract(_, idx) => write!(label, "Extract {}", idx)?,
            GateKind::Gadget(gk, _) => write!(label, "Gadget {}", gk.name())?,
            GateKind::Call(f, _, _) => write!(label, "Call {}", f.name)?,
        }
        write!(label, " (")?;
        write_ty(&mut label, w.ty)?;
        write!(label, ")\n")?;

        write!(label, "{}\n", w.label)?;

        let val = ev.eval_wire(c, w);
        match val {
            Ok(val) => write_val(&mut label, val)?,
            _ => write!(label, "[eval failed]")?,
        }

        writeln!(s, "\"{:p}\" [ label = {:?} ];", w, label)?;

        let mut write_edges = |ws: &[_]| -> Result<(), fmt::Error> {
            for &w2 in ws {
                writeln!(s, "\"{:p}\" -> \"{:p}\";", w2, w)?;
            }
            Ok(())
        };

        match w.kind {
            GateKind::Lit(_, _) |
            GateKind::Secret(_) |
            GateKind::Erased(_) |
            GateKind::Argument(_, _) => {},
            GateKind::Unary(_, a) |
            GateKind::Cast(a, _) |
            GateKind::Extract(a, _) => write_edges(&[a])?,
            GateKind::Binary(_, a, b) |
            GateKind::Shift(_, a, b) |
            GateKind::Compare(_, a, b) => write_edges(&[a, b])?,
            GateKind::Mux(a, b, c) => write_edges(&[a, b, c])?,
            GateKind::Pack(ws) |
            GateKind::Gadget(_, ws) |
            GateKind::Call(_, ws, _) => write_edges(ws)?,
        }
    }

    writeln!(s, "}}")?;
    Ok(s)
}
