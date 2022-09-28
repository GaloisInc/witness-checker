use arrayvec::ArrayVec;
use crate::gadget::bit_pack;
use crate::ir::typed::{Builder, BuilderExt, TWire};

pub struct Sha256<'a> {
    state: [TWire<'a, u32>; 8],
    k: [TWire<'a, u32>; 64],

    /// Message words.  Once this is full (16 words), we run the compression function.
    m: ArrayVec<[TWire<'a, u32>; 16]>,
    /// Message bytes.  Once this is full (4 bytes), we concatenate the bytes into a word and add
    /// it to `m`.
    bytes: ArrayVec<[TWire<'a, u8>; 4]>,

    /// Total number of bytes pushed so far.
    msg_len: usize,
}

impl<'a> Sha256<'a> {
    pub fn new(b: &impl Builder<'a>) -> Sha256<'a> {
        Sha256 {
            state: [
                b.lit(0x6a09e667),
                b.lit(0xbb67ae85),
                b.lit(0x3c6ef372),
                b.lit(0xa54ff53a),
                b.lit(0x510e527f),
                b.lit(0x9b05688c),
                b.lit(0x1f83d9ab),
                b.lit(0x5be0cd19),
            ],
            k: [
                b.lit(0x428a2f98), b.lit(0x71374491), b.lit(0xb5c0fbcf), b.lit(0xe9b5dba5),
                b.lit(0x3956c25b), b.lit(0x59f111f1), b.lit(0x923f82a4), b.lit(0xab1c5ed5),
                b.lit(0xd807aa98), b.lit(0x12835b01), b.lit(0x243185be), b.lit(0x550c7dc3),
                b.lit(0x72be5d74), b.lit(0x80deb1fe), b.lit(0x9bdc06a7), b.lit(0xc19bf174),
                b.lit(0xe49b69c1), b.lit(0xefbe4786), b.lit(0x0fc19dc6), b.lit(0x240ca1cc),
                b.lit(0x2de92c6f), b.lit(0x4a7484aa), b.lit(0x5cb0a9dc), b.lit(0x76f988da),
                b.lit(0x983e5152), b.lit(0xa831c66d), b.lit(0xb00327c8), b.lit(0xbf597fc7),
                b.lit(0xc6e00bf3), b.lit(0xd5a79147), b.lit(0x06ca6351), b.lit(0x14292967),
                b.lit(0x27b70a85), b.lit(0x2e1b2138), b.lit(0x4d2c6dfc), b.lit(0x53380d13),
                b.lit(0x650a7354), b.lit(0x766a0abb), b.lit(0x81c2c92e), b.lit(0x92722c85),
                b.lit(0xa2bfe8a1), b.lit(0xa81a664b), b.lit(0xc24b8b70), b.lit(0xc76c51a3),
                b.lit(0xd192e819), b.lit(0xd6990624), b.lit(0xf40e3585), b.lit(0x106aa070),
                b.lit(0x19a4c116), b.lit(0x1e376c08), b.lit(0x2748774c), b.lit(0x34b0bcb5),
                b.lit(0x391c0cb3), b.lit(0x4ed8aa4a), b.lit(0x5b9cca4f), b.lit(0x682e6ff3),
                b.lit(0x748f82ee), b.lit(0x78a5636f), b.lit(0x84c87814), b.lit(0x8cc70208),
                b.lit(0x90befffa), b.lit(0xa4506ceb), b.lit(0xbef9a3f7), b.lit(0xc67178f2),
            ],

            m: ArrayVec::new(),
            bytes: ArrayVec::new(),
            msg_len: 0,
        }
    }

    /// Add one byte of input.
    pub fn push_byte(&mut self, b: &impl Builder<'a>, w: TWire<'a, u8>) {
        self.bytes.push(w);
        self.msg_len += 1;

        if self.bytes.len() == 4 {
            self.build_word(b);
        }
    }

    /// Combine the bytes in `self.bytes` into a word, and push it onto `self.m`.
    fn build_word(&mut self, b: &impl Builder<'a>) {
        debug_assert_eq!(self.bytes.len(), 4);
        // Concatenate 4 bytes in big-endian order.
        let word_raw = bit_pack::concat_bits_raw(b.circuit(), &[
            self.bytes[3].repr,
            self.bytes[2].repr,
            self.bytes[1].repr,
            self.bytes[0].repr,
        ]);
        let word = TWire::<u32>::new(word_raw);
        self.m.push(word);
        self.bytes.clear();

        if self.m.len() == self.m.capacity() {
            self.process_block(b);
        }
    }

    /// Take a complete message block from `self.m` and compress it into the state.
    fn process_block(&mut self, bld: &impl Builder<'a>) {
        debug_assert_eq!(self.m.len(), self.m.capacity());
        let w = Self::message_schedule(bld, &self.m);
        let [a, b, c, d, e, f, g, h] = Self::compress(bld, &self.k, &w, self.state);

        self.state[0] = bld.add(self.state[0], a);
        self.state[1] = bld.add(self.state[1], b);
        self.state[2] = bld.add(self.state[2], c);
        self.state[3] = bld.add(self.state[3], d);
        self.state[4] = bld.add(self.state[4], e);
        self.state[5] = bld.add(self.state[5], f);
        self.state[6] = bld.add(self.state[6], g);
        self.state[7] = bld.add(self.state[7], h);

        self.m.clear();
    }

    fn message_schedule(bld: &impl Builder<'a>, m: &[TWire<'a, u32>]) -> [TWire<'a, u32>; 64] {
        debug_assert_eq!(m.len(), 16);
        let mut w = ArrayVec::<[TWire<'a, u32>; 64]>::new();
        for i in 0 .. 16 {
            w.push(m[i]);
        }
        for i in 16 .. 64 {
            let s0 = xor3(
                bld,
                rotr(bld, w[i - 15], 7),
                rotr(bld, w[i - 15], 18),
                bld.shr(w[i - 15], bld.lit(3)),
            );

            let s1 = xor3(
                bld,
                rotr(bld, w[i - 2], 17),
                rotr(bld, w[i - 2], 19),
                bld.shr(w[i - 2], bld.lit(10)),
            );

            w.push(add4(bld, w[i - 16], s0, w[i - 7], s1));
        }
        w.into_inner().unwrap()
    }

    fn compress(
        bld: &impl Builder<'a>,
        k: &[TWire<'a, u32>],
        w: &[TWire<'a, u32>],
        mut acc: [TWire<'a, u32>; 8],
    ) -> [TWire<'a, u32>; 8] {
        debug_assert_eq!(k.len(), 64);
        for (&ki, &wi) in k.iter().zip(w.iter()) {
            acc = Self::compress_one(bld, ki, wi, acc);
        }
        acc
    }

    fn compress_one(
        bld: &impl Builder<'a>,
        ki: TWire<'a, u32>,
        wi: TWire<'a, u32>,
        acc: [TWire<'a, u32>; 8],
    ) -> [TWire<'a, u32>; 8] {
        #![allow(bad_style)]
        let [a, b, c, d, e, f, g, h] = acc;
        let S1 = xor3(
            bld,
            rotr(bld, e, 6),
            rotr(bld, e, 11),
            rotr(bld, e, 25),
        );
        let temp1 = add5(bld, h, S1, ch(bld, e, f, g), ki, wi);

        let S0 = xor3(
            bld,
            rotr(bld, a, 2),
            rotr(bld, a, 13),
            rotr(bld, a, 22),
        );
        let temp2 = bld.add(S0, maj(bld, a, b, c));

        [
            bld.add(temp1, temp2),
            a,
            b,
            c,
            bld.add(d, temp1),
            e,
            f,
            g,
        ]
    }

    /// Process the final block and emit the hash.
    pub fn finish(&mut self, b: &impl Builder<'a>) -> TWire<'a, [u32; 8]> {
        self.pad_final_block(b);
        // `pad_final_block` should finish the block, so the message buffer should be empty
        // afterwards.
        debug_assert_eq!(self.msg_len % 64, 0);
        debug_assert_eq!(self.bytes.len(), 0);
        debug_assert_eq!(self.m.len(), 0);

        TWire::new(self.state)
    }

    fn pad_final_block(&mut self, b: &impl Builder<'a>) {
        let msg_len = self.msg_len;

        self.push_byte(b, b.lit(0x80));

        // Pad with zeros until msg_len is 8 short of a multiple of 64 bytes.
        while self.msg_len % 64 != 64 - 8 {
            self.push_byte(b, b.lit(0));
        }
        // Append the original message length in bits as a 64-bit integer.
        for &byte in (msg_len as u64 * 8).to_be_bytes().iter() {
            self.push_byte(b, b.lit(byte));
        }
    }
}

fn rotr<'a>(
    b: &impl Builder<'a>,
    x: TWire<'a, u32>,
    y: u8,
) -> TWire<'a, u32> {
    if y == 0 || y == 32 {
        return x;
    }
    b.or(
        b.shr(x, b.lit(y)),
        b.shl(x, b.lit(32 - y)),
    )
}

fn xor3<'a>(
    b: &impl Builder<'a>,
    x: TWire<'a, u32>,
    y: TWire<'a, u32>,
    z: TWire<'a, u32>,
) -> TWire<'a, u32> {
    b.xor(b.xor(x, y), z)
}

fn add4<'a>(
    b: &impl Builder<'a>,
    w: TWire<'a, u32>,
    x: TWire<'a, u32>,
    y: TWire<'a, u32>,
    z: TWire<'a, u32>,
) -> TWire<'a, u32> {
    b.add(b.add(b.add(w, x), y), z)
}

fn add5<'a>(
    b: &impl Builder<'a>,
    v: TWire<'a, u32>,
    w: TWire<'a, u32>,
    x: TWire<'a, u32>,
    y: TWire<'a, u32>,
    z: TWire<'a, u32>,
) -> TWire<'a, u32> {
    b.add(b.add(b.add(b.add(v, w), x), y), z)
}

fn ch<'a>(
    b: &impl Builder<'a>,
    x: TWire<'a, u32>,
    y: TWire<'a, u32>,
    z: TWire<'a, u32>,
) -> TWire<'a, u32> {
    b.xor(
        b.and(x, y),
        b.and(b.not(x), z),
    )
}

fn maj<'a>(
    b: &impl Builder<'a>,
    x: TWire<'a, u32>,
    y: TWire<'a, u32>,
    z: TWire<'a, u32>,
) -> TWire<'a, u32> {
    xor3(
        b,
        b.and(x, y),
        b.and(x, z),
        b.and(y, z),
    )
}


#[cfg(test)]
mod test {
    use crate::eval::{self, CachingEvaluator};
    use crate::ir::circuit::{Circuit, Arenas, FilterNil};
    use crate::ir::typed::{BuilderImpl, EvaluatorExt};
    use super::*;

    /// Test hashing the string "abc", using the individual helper functions manually.
    #[test]
    fn abc_parts() {
        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let mut h = Sha256::new(b);
        h.push_byte(b, b.lit(b'a'));
        h.push_byte(b, b.lit(b'b'));
        h.push_byte(b, b.lit(b'c'));
        h.push_byte(b, b.lit(0x80));
        for _ in 1..14 {
            h.m.push(b.lit(0_u32));
        }
        h.m.push(b.lit(0));
        h.m.push(b.lit(24));
        debug_assert_eq!(h.m.len(), 16);

        let w = Sha256::message_schedule(b, &h.m);
        assert_eq!(ev.eval_typed(&c, w[0]), Some(0b01100001011000100110001110000000));
        assert_eq!(ev.eval_typed(&c, w[1]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[2]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[3]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[4]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[5]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[6]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[7]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[8]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[9]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[10]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[11]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[12]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[13]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[14]), Some(0b00000000000000000000000000000000));
        assert_eq!(ev.eval_typed(&c, w[15]), Some(0b00000000000000000000000000011000));
        assert_eq!(ev.eval_typed(&c, w[16]), Some(0b01100001011000100110001110000000));
        assert_eq!(ev.eval_typed(&c, w[17]), Some(0b00000000000011110000000000000000));
        assert_eq!(ev.eval_typed(&c, w[18]), Some(0b01111101101010000110010000000101));
        assert_eq!(ev.eval_typed(&c, w[19]), Some(0b01100000000000000000001111000110));
        assert_eq!(ev.eval_typed(&c, w[20]), Some(0b00111110100111010111101101111000));
        assert_eq!(ev.eval_typed(&c, w[21]), Some(0b00000001100000111111110000000000));
        assert_eq!(ev.eval_typed(&c, w[22]), Some(0b00010010110111001011111111011011));
        assert_eq!(ev.eval_typed(&c, w[23]), Some(0b11100010111000101100001110001110));
        assert_eq!(ev.eval_typed(&c, w[24]), Some(0b11001000001000010101110000011010));
        assert_eq!(ev.eval_typed(&c, w[25]), Some(0b10110111001101100111100110100010));
        assert_eq!(ev.eval_typed(&c, w[26]), Some(0b11100101101111000011100100001001));
        assert_eq!(ev.eval_typed(&c, w[27]), Some(0b00110010011001100011110001011011));
        assert_eq!(ev.eval_typed(&c, w[28]), Some(0b10011101001000001001110101100111));
        assert_eq!(ev.eval_typed(&c, w[29]), Some(0b11101100100001110010011011001011));
        assert_eq!(ev.eval_typed(&c, w[30]), Some(0b01110000001000010011100010100100));
        assert_eq!(ev.eval_typed(&c, w[31]), Some(0b11010011101101111001011100111011));
        assert_eq!(ev.eval_typed(&c, w[32]), Some(0b10010011111101011001100101111111));
        assert_eq!(ev.eval_typed(&c, w[33]), Some(0b00111011011010001011101001110011));
        assert_eq!(ev.eval_typed(&c, w[34]), Some(0b10101111111101001111111111000001));
        assert_eq!(ev.eval_typed(&c, w[35]), Some(0b11110001000010100101110001100010));
        assert_eq!(ev.eval_typed(&c, w[36]), Some(0b00001010100010110011100110010110));
        assert_eq!(ev.eval_typed(&c, w[37]), Some(0b01110010101011111000001100001010));
        assert_eq!(ev.eval_typed(&c, w[38]), Some(0b10010100000010011110001100111110));
        assert_eq!(ev.eval_typed(&c, w[39]), Some(0b00100100011001000001010100100010));
        assert_eq!(ev.eval_typed(&c, w[40]), Some(0b10011111010001111011111110010100));
        assert_eq!(ev.eval_typed(&c, w[41]), Some(0b11110000101001100100111101011010));
        assert_eq!(ev.eval_typed(&c, w[42]), Some(0b00111110001001000110101001111001));
        assert_eq!(ev.eval_typed(&c, w[43]), Some(0b00100111001100110011101110100011));
        assert_eq!(ev.eval_typed(&c, w[44]), Some(0b00001100010001110110001111110010));
        assert_eq!(ev.eval_typed(&c, w[45]), Some(0b10000100000010101011111100100111));
        assert_eq!(ev.eval_typed(&c, w[46]), Some(0b01111010001010010000110101011101));
        assert_eq!(ev.eval_typed(&c, w[47]), Some(0b00000110010111000100001111011010));
        assert_eq!(ev.eval_typed(&c, w[48]), Some(0b11111011001111101000100111001011));
        assert_eq!(ev.eval_typed(&c, w[49]), Some(0b11001100011101100001011111011011));
        assert_eq!(ev.eval_typed(&c, w[50]), Some(0b10111001111001100110110000110100));
        assert_eq!(ev.eval_typed(&c, w[51]), Some(0b10101001100110010011011001100111));
        assert_eq!(ev.eval_typed(&c, w[52]), Some(0b10000100101110101101111011011101));
        assert_eq!(ev.eval_typed(&c, w[53]), Some(0b11000010000101000110001010111100));
        assert_eq!(ev.eval_typed(&c, w[54]), Some(0b00010100100001110100011100101100));
        assert_eq!(ev.eval_typed(&c, w[55]), Some(0b10110010000011110111101010011001));
        assert_eq!(ev.eval_typed(&c, w[56]), Some(0b11101111010101111011100111001101));
        assert_eq!(ev.eval_typed(&c, w[57]), Some(0b11101011111001101011001000111000));
        assert_eq!(ev.eval_typed(&c, w[58]), Some(0b10011111111000110000100101011110));
        assert_eq!(ev.eval_typed(&c, w[59]), Some(0b01111000101111001000110101001011));
        assert_eq!(ev.eval_typed(&c, w[60]), Some(0b10100100001111111100111100010101));
        assert_eq!(ev.eval_typed(&c, w[61]), Some(0b01100110100010110010111111111000));
        assert_eq!(ev.eval_typed(&c, w[62]), Some(0b11101110101010111010001011001100));
        assert_eq!(ev.eval_typed(&c, w[63]), Some(0b00010010101100011110110111101011));

        assert_eq!(ev.eval_typed(&c, h.state[0]), Some(0b01101010000010011110011001100111));
        assert_eq!(ev.eval_typed(&c, h.state[1]), Some(0b10111011011001111010111010000101));
        assert_eq!(ev.eval_typed(&c, h.state[2]), Some(0b00111100011011101111001101110010));
        assert_eq!(ev.eval_typed(&c, h.state[3]), Some(0b10100101010011111111010100111010));
        assert_eq!(ev.eval_typed(&c, h.state[4]), Some(0b01010001000011100101001001111111));
        assert_eq!(ev.eval_typed(&c, h.state[5]), Some(0b10011011000001010110100010001100));
        assert_eq!(ev.eval_typed(&c, h.state[6]), Some(0b00011111100000111101100110101011));
        assert_eq!(ev.eval_typed(&c, h.state[7]), Some(0b01011011111000001100110100011001));

        assert_eq!(ev.eval_typed(&c, h.k[0]), Some(0b01000010100010100010111110011000));
        assert_eq!(ev.eval_typed(&c, w[0]), Some(0b01100001011000100110001110000000));
        let acc1 = Sha256::compress_one(b, h.k[0], w[0], h.state);
        assert_eq!(ev.eval_typed(&c, acc1[0]), Some(0b01011101011010101110101111001101));
        assert_eq!(ev.eval_typed(&c, acc1[1]), Some(0b01101010000010011110011001100111));
        assert_eq!(ev.eval_typed(&c, acc1[2]), Some(0b10111011011001111010111010000101));
        assert_eq!(ev.eval_typed(&c, acc1[3]), Some(0b00111100011011101111001101110010));
        assert_eq!(ev.eval_typed(&c, acc1[4]), Some(0b11111010001010100100011000100010));
        assert_eq!(ev.eval_typed(&c, acc1[5]), Some(0b01010001000011100101001001111111));
        assert_eq!(ev.eval_typed(&c, acc1[6]), Some(0b10011011000001010110100010001100));
        assert_eq!(ev.eval_typed(&c, acc1[7]), Some(0b00011111100000111101100110101011));

        let acc = Sha256::compress(b, &h.k, &w, h.state);
        assert_eq!(ev.eval_typed(&c, acc[0]), Some(0b01010000011011100011000001011000));
        assert_eq!(ev.eval_typed(&c, acc[1]), Some(0b11010011100110100010000101100101));
        assert_eq!(ev.eval_typed(&c, acc[2]), Some(0b00000100110100100100110101101100));
        assert_eq!(ev.eval_typed(&c, acc[3]), Some(0b10111000010111100010110011101001));
        assert_eq!(ev.eval_typed(&c, acc[4]), Some(0b01011110111101010000111100100100));
        assert_eq!(ev.eval_typed(&c, acc[5]), Some(0b11111011000100100001001000010000));
        assert_eq!(ev.eval_typed(&c, acc[6]), Some(0b10010100100011010010010110110110));
        assert_eq!(ev.eval_typed(&c, acc[7]), Some(0b10010110000111110100100010010100));

        h.process_block(b);
        assert_eq!(ev.eval_typed(&c, h.state[0]), Some(0b10111010011110000001011010111111));
        assert_eq!(ev.eval_typed(&c, h.state[1]), Some(0b10001111000000011100111111101010));
        assert_eq!(ev.eval_typed(&c, h.state[2]), Some(0b01000001010000010100000011011110));
        assert_eq!(ev.eval_typed(&c, h.state[3]), Some(0b01011101101011100010001000100011));
        assert_eq!(ev.eval_typed(&c, h.state[4]), Some(0b10110000000000110110000110100011));
        assert_eq!(ev.eval_typed(&c, h.state[5]), Some(0b10010110000101110111101010011100));
        assert_eq!(ev.eval_typed(&c, h.state[6]), Some(0b10110100000100001111111101100001));
        assert_eq!(ev.eval_typed(&c, h.state[7]), Some(0b11110010000000000001010110101101));
    }

    #[test]
    fn abc() {
        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let mut h = Sha256::new(b);
        h.push_byte(b, b.lit(b'a'));
        h.push_byte(b, b.lit(b'b'));
        h.push_byte(b, b.lit(b'c'));
        let hash_wire = h.finish(b);
        let hash = ev.eval_typed(&c, hash_wire).unwrap();

        assert_eq!(hash[0], 0xba7816bf);
        assert_eq!(hash[1], 0x8f01cfea);
        assert_eq!(hash[2], 0x414140de);
        assert_eq!(hash[3], 0x5dae2223);
        assert_eq!(hash[4], 0xb00361a3);
        assert_eq!(hash[5], 0x96177a9c);
        assert_eq!(hash[6], 0xb410ff61);
        assert_eq!(hash[7], 0xf20015ad);
    }

    #[test]
    fn empty() {
        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let mut h = Sha256::new(b);
        let hash_wire = h.finish(b);
        let hash = ev.eval_typed(&c, hash_wire).unwrap();

        assert_eq!(hash[0], 0xe3b0c442);
        assert_eq!(hash[1], 0x98fc1c14);
        assert_eq!(hash[2], 0x9afbf4c8);
        assert_eq!(hash[3], 0x996fb924);
        assert_eq!(hash[4], 0x27ae41e4);
        assert_eq!(hash[5], 0x649b934c);
        assert_eq!(hash[6], 0xa495991b);
        assert_eq!(hash[7], 0x7852b855);
    }

    #[test]
    fn long() {
        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let mut h = Sha256::new(b);

        let s = "this is a very long input (more than 64 bytes) which takes up multiple blocks";
        assert!(s.len() > 64);
        for byte in s[..64].bytes() {
            h.push_byte(b, b.lit(byte));
        }
        assert_eq!(h.m.len(), 0);

        assert_eq!(ev.eval_typed(&c, h.state[0]), Some(0b00110000001110100111011101110111));
        assert_eq!(ev.eval_typed(&c, h.state[1]), Some(0b00110011000001011111101000000001));
        assert_eq!(ev.eval_typed(&c, h.state[2]), Some(0b00011100111100011010001100110100));
        assert_eq!(ev.eval_typed(&c, h.state[3]), Some(0b01110101000111100011000011110101));
        assert_eq!(ev.eval_typed(&c, h.state[4]), Some(0b10111101000001010101110010001111));
        assert_eq!(ev.eval_typed(&c, h.state[5]), Some(0b01101001011011101000101111001001));
        assert_eq!(ev.eval_typed(&c, h.state[6]), Some(0b01011111011000110001001000000011));
        assert_eq!(ev.eval_typed(&c, h.state[7]), Some(0b01001110010111101101101010011111));

        for byte in s[64..].bytes() {
            h.push_byte(b, b.lit(byte));
        }
        let hash_wire = h.finish(b);
        let hash = ev.eval_typed(&c, hash_wire).unwrap();

        assert_eq!(ev.eval_typed(&c, h.state[0]), Some(0b00111010100101011011111110010101));
        assert_eq!(ev.eval_typed(&c, h.state[1]), Some(0b11000010100011011011100101011100));
        assert_eq!(ev.eval_typed(&c, h.state[2]), Some(0b11001000010110100100110010101110));
        assert_eq!(ev.eval_typed(&c, h.state[3]), Some(0b01101110011011000110100000000111));
        assert_eq!(ev.eval_typed(&c, h.state[4]), Some(0b00011011000111111010100100010101));
        assert_eq!(ev.eval_typed(&c, h.state[5]), Some(0b00110110011011101100110000011001));
        assert_eq!(ev.eval_typed(&c, h.state[6]), Some(0b10001101011101111100110001110001));
        assert_eq!(ev.eval_typed(&c, h.state[7]), Some(0b00101100110000101001000001001111));

        assert_eq!(hash[0], 0x3a95bf95);
        assert_eq!(hash[1], 0xc28db95c);
        assert_eq!(hash[2], 0xc85a4cae);
        assert_eq!(hash[3], 0x6e6c6807);
        assert_eq!(hash[4], 0x1b1fa915);
        assert_eq!(hash[5], 0x366ecc19);
        assert_eq!(hash[6], 0x8d77cc71);
        assert_eq!(hash[7], 0x2cc2904f);
    }
}
