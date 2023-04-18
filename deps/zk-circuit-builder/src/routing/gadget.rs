use num_bigint::{BigInt, BigUint};
use crate::eval::{self, Value, EvalResult};
use crate::ir::circuit::{
    CircuitExt, CircuitBase, CircuitTrait, DynCircuitRef, Wire, Ty, TyKind, IntSize, GadgetKind,
    GadgetKindRef, Bits,
};
use crate::ir::typed::{Builder, BuilderExt as _, Repr, TWire};

/// Add two unsigned integers and check for overflow.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Permute {
    pub items: usize,
    /// Number of wires in each input item.
    pub wires_per_item: usize,
}
impl_gadget_kind_support!(Permute);

impl<'a> GadgetKind<'a> for Permute {
    fn transfer<'b>(&self, c: &CircuitBase<'b>) -> GadgetKindRef<'b> {
        c.intern_gadget_kind(self.clone())
    }

    fn typecheck(&self, c: &CircuitBase<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a> {
        // We expect a permutation argument, followed by `items` groups of `wires_per_item` wires.
        let perm_ty = arg_tys[0];
        assert_eq!(*perm_ty, TyKind::RawBits);

        let arg_tys = &arg_tys[1..];

        assert!(arg_tys.len() > 0, "expected at least one argument");
        assert_eq!(arg_tys.len(), self.items * self.wires_per_item);

        // Each block of input wires should have the same wire types.
        for (i, ty) in arg_tys.iter().copied().enumerate() {
            assert_eq!(ty, arg_tys[i % self.wires_per_item],
                "type mismatch at index {}", i);
        }

        let mut result_tys = Vec::with_capacity(self.items * self.wires_per_item);
        for _ in 0 .. self.items {
            result_tys.extend_from_slice(&arg_tys[..self.wires_per_item]);
        }

        c.ty_bundle(&result_tys)
    }

    fn decompose(&self, c: DynCircuitRef<'a, '_>, args: &[Wire<'a>]) -> Wire<'a> {
        todo!("decompose Permute")
    }

    fn eval_bits(
        &self,
        c: &CircuitBase<'a>,
        arg_tys: &[Ty<'a>],
        args: &[Result<Bits<'a>, eval::Error<'a>>],
        result_ty: Ty<'a>,
    ) -> Result<Bits<'a>, eval::Error<'a>> {
        let perm = args[0]?;
        let arg_tys = &arg_tys[1..];
        let args = &args[1..];

        let digits_per_item = arg_tys[..self.wires_per_item].iter()
            .map(|&ty| ty.digits()).sum::<usize>();
        let mut result_digits = Vec::with_capacity(self.items * digits_per_item);
        for i in 0..self.items {
            let idx = perm.0.get(i).copied().unwrap_or(0) as usize;
            let range = idx * self.wires_per_item .. (idx + 1) * self.wires_per_item;
            let input_tys = &arg_tys[range.clone()];
            let input_vals = &args[range];
            for (&ty, &val) in input_tys.iter().zip(input_vals.iter()) {
                let val = val?;
                let digits = ty.digits();
                if val.0.len() >= digits {
                    result_digits.extend_from_slice(&val.0[..digits]);
                } else {
                    result_digits.extend_from_slice(val.0);
                    for _ in val.0.len() .. digits {
                        result_digits.push(0);
                    }
                }
            }
        }
        debug_assert_eq!(result_digits.len(), self.items * digits_per_item);

        let bits = c.intern_bits(&result_digits);
        Ok(bits)
    }
}
