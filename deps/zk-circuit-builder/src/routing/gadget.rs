use crate::eval::{self};
use crate::ir::circuit::{
    CircuitExt, CircuitBase, CircuitTrait, DynCircuitRef, Wire, Ty, TyKind, GadgetKind,
    GadgetKindRef, Bits,
};
use crate::routing::benes::{self, BenesNetwork};

/// Permute a sequence of items according to secret flags.
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
        let m = self.items;
        let bn = BenesNetwork::new(m as u32, m as u32);
        let m_rounded = 2 * bn.layer_size;

        let out_to_inp = args[0];

        // Derive secret `BenesNetwork` flags from the secret routes.
        let num_flags = bn.num_layers * bn.layer_size;
        debug_assert_eq!(Bits::DIGIT_BITS, 32);
        let digits = (num_flags + Bits::DIGIT_BITS - 1) / Bits::DIGIT_BITS;
        let secret_deps = c.wire_list(&[out_to_inp]);
        let secret_swap_flags = c.secret_derived(Ty::raw_bits(), secret_deps, move |c, vals| {
            debug_assert_eq!(vals.len(), 1);
            let routes_bits = vals[0];

            let mut bn = benes::BenesNetwork::new(m as u32, m as u32);
            if m >= 2 {
                let routes = routes_bits.0.iter().enumerate().map(|(out, &inp)| {
                    benes::Route {
                        input: inp,
                        output: out as u32,
                        public: false,
                    }
                }).collect::<Vec<_>>();
                bn.set_routes(&routes);
            }

            let mut out = vec![0; digits];
            for (i, flags) in bn.flags.iter().enumerate() {
                let idx = i / Bits::DIGIT_BITS;
                let off = i % Bits::DIGIT_BITS;
                if flags.contains(benes::SwitchFlags::F_SWAP) {
                    out[idx] |= 1 << off;
                }
            }
            c.intern_bits(&out)
        });

        // The output of the most recent layer.  This always has `m_rounded * wires_per_item`
        // entries, though some entries may be `None`.
        let mut wires = args.iter().skip(1).copied().map(Some)
            .chain((args.len() - 1 .. m_rounded * self.wires_per_item).map(|_| None))
            .collect::<Vec<_>>();

        for l in 0 .. bn.num_layers {
            let mut new_wires = Vec::with_capacity(m_rounded * self.wires_per_item);
            let mut b_buf = Vec::with_capacity(self.wires_per_item);
            for i in 0 .. bn.layer_size {
                let [a_idx, b_idx] = bn.switch(l, i);
                for j in 0 .. self.wires_per_item {
                    let a = wires[a_idx as usize * self.wires_per_item + j];
                    let b = wires[b_idx as usize * self.wires_per_item + j];
                    let (a, b) = benes_switch(&c, a, b, &bn, secret_swap_flags, l, i);
                    new_wires.push(a);
                    b_buf.push(b);
                }
                new_wires.append(&mut b_buf);
            }
            wires = new_wires;
        }

        c.pack_iter(wires.into_iter().map(|opt_w| opt_w.unwrap()).take(m * self.wires_per_item))
    }

    fn eval_bits(
        &self,
        c: &CircuitBase<'a>,
        arg_tys: &[Ty<'a>],
        args: &[Result<Bits<'a>, eval::Error<'a>>],
        _result_ty: Ty<'a>,
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

fn benes_switch<'a>(
    c: &impl CircuitTrait<'a>,
    x: Option<Wire<'a>>,
    y: Option<Wire<'a>>,
    bn: &benes::BenesNetwork,
    secret_swap_flags: Wire<'a>,
    l: usize,
    i: usize,
) -> (Option<Wire<'a>>, Option<Wire<'a>>) {
    let public_flags = bn.flags(l, i);
    if public_flags.contains(benes::SwitchFlags::F_PUBLIC) {
        if public_flags.contains(benes::SwitchFlags::F_SWAP) {
            return (y, x);
        } else {
            return (x, y);
        }
    }

    let (x, y) = match (x, y) {
        (None, None) => return (None, None),
        (Some(x), None) => return (Some(x), Some(x)),
        (None, Some(y)) => return (Some(y), Some(y)),
        (Some(x), Some(y)) => (x, y),
    };

    let idx = bn.node_index(l, i);
    let secret_deps = c.wire_list(&[secret_swap_flags]);
    let swap = c.secret_derived(Ty::bool(), secret_deps, move |c, secret_vals| {
        debug_assert_eq!(secret_vals.len(), 1);
        let flag = secret_vals[0].get(idx);
        c.bits(Ty::bool(), flag)
    });
    let x2 = c.mux(swap, y.clone(), x.clone());
    let y2 = c.mux(swap, x, y);
    (Some(x2), Some(y2))
}

