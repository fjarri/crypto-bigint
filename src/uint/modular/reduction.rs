use crate::{Limb, Uint, WideWord, Word};

/// Returns `(hi, lo)` such that `hi * R + lo = x * y + z + w`.
#[inline(always)]
const fn muladdcarry(x: Word, y: Word, z: Word, w: Word) -> (Word, Word) {
    let res = (x as WideWord) * (y as WideWord) + (z as WideWord) + (w as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
}

#[inline(always)]
const fn addcarry(z: Word, w: Word) -> (Word, Word) {
    let res = (z as WideWord).wrapping_add(w as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
}

/// Returns `(x..., x_hi) - (y...) mod (m...)`.
/// Assumes `-(m...) <= (x..., x_hi) - (y...) < (m...)`.
#[inline(always)]
pub(crate) const fn sub_mod_with_hi<const LIMBS: usize>(
    x_hi: Limb,
    x: &Uint<LIMBS>,
    y: &Uint<LIMBS>,
    m: &Uint<LIMBS>,
) -> Uint<LIMBS> {
    // Note: this is pretty much `Uint::sub_mod()`, but with `x_hi` added.

    debug_assert!(x_hi.0 <= 1);

    let (w, borrow) = x.sbb(y, Limb::ZERO);

    // The new `borrow = Word::MAX` iff `x_hi == 0` and `borrow == Word::MAX`.
    let borrow = (!x_hi.0.wrapping_neg()) & borrow.0;

    // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
    // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
    let mask = Uint::from_words([borrow; LIMBS]);

    w.wrapping_add(&m.bitand(&mask))
}

#[inline(always)]
const fn min(x: usize, y: usize) -> usize {
    // Unfortunately `core::cmp::min()` is not const
    if x < y {
        x
    } else {
        y
    }
}

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
pub const fn montgomery_reduction<const LIMBS: usize>(
    lower_upper: &(Uint<LIMBS>, Uint<LIMBS>),
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
    modulus_limbs: usize,
) -> Uint<LIMBS> {
    assert!(
        (modulus_limbs == LIMBS && modulus.limbs[LIMBS - 1].0 > 0)
            || (modulus_limbs < LIMBS && modulus.limbs[LIMBS - 1].0 == 0)
    );

    let (mut lower, mut upper) = *lower_upper;

    let mut meta_carry = Limb(0);
    let mut new_sum;

    let mut i = 0;
    while i < LIMBS {
        let u = lower.limbs[i].0.wrapping_mul(mod_neg_inv.0);

        let (mut carry, _) = muladdcarry(u, modulus.limbs[0].0, lower.limbs[i].0, 0);
        let mut new_limb;

        let mut j = 1;
        while j < min(modulus_limbs, LIMBS - i) {
            (carry, new_limb) = muladdcarry(u, modulus.limbs[j].0, lower.limbs[i + j].0, carry);
            lower.limbs[i + j] = Limb(new_limb);
            j += 1;
        }
        while j < LIMBS - i {
            (carry, new_limb) = addcarry(lower.limbs[i + j].0, carry);
            lower.limbs[i + j] = Limb(new_limb);
            j += 1;
        }
        while j < min(modulus_limbs, LIMBS) {
            (carry, new_limb) =
                muladdcarry(u, modulus.limbs[j].0, upper.limbs[i + j - LIMBS].0, carry);
            upper.limbs[i + j - LIMBS] = Limb(new_limb);
            j += 1;
        }
        while j < LIMBS {
            (carry, new_limb) = addcarry(upper.limbs[i + j - LIMBS].0, carry);
            upper.limbs[i + j - LIMBS] = Limb(new_limb);
            j += 1;
        }

        (new_sum, meta_carry) = upper.limbs[i].adc(Limb(carry), meta_carry);
        upper.limbs[i] = new_sum;

        i += 1;
    }

    // Division is simply taking the upper half of the limbs
    // Final reduction (at this point, the value is at most 2 * modulus,
    // so `meta_carry` is either 0 or 1)

    sub_mod_with_hi(meta_carry, &upper, modulus, modulus)
}

extern crate std;
pub fn montgomery_reduction2<const LIMBS: usize>(
    lower_upper: &(Uint<LIMBS>, Uint<LIMBS>),
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
    modulus_limbs: usize,
) -> Uint<LIMBS> {
    assert!(
        (modulus_limbs == LIMBS && modulus.limbs[LIMBS - 1].0 > 0)
            || (modulus_limbs < LIMBS && modulus.limbs[LIMBS - 1].0 == 0)
    );

    //let modulus_limbs = LIMBS;
    let (mut lower, mut upper) = *lower_upper;

    let mut meta_carry = Limb(0);
    let mut new_sum;

    let mut i = 0;
    while i < LIMBS {
        let u = lower.limbs[i].0.wrapping_mul(mod_neg_inv.0);

        let (mut carry, _) = muladdcarry(u, modulus.limbs[0].0, lower.limbs[i].0, 0);
        let mut new_limb;

        let mut j = 1;
        while j < min(modulus_limbs, LIMBS - i) {
            std::println!("full 1, i={i}, j={j}");
            (carry, new_limb) = muladdcarry(u, modulus.limbs[j].0, lower.limbs[i + j].0, carry);
            lower.limbs[i + j] = Limb(new_limb);
            j += 1;
        }
        while j < LIMBS - i {
            std::println!("red 1, i={i}, j={j}");
            (carry, new_limb) = addcarry(lower.limbs[i + j].0, carry);
            lower.limbs[i + j] = Limb(new_limb);
            j += 1;
        }
        while j < min(modulus_limbs, LIMBS) {
            std::println!("full 2, i={i}, j={j}");
            (carry, new_limb) =
                muladdcarry(u, modulus.limbs[j].0, upper.limbs[i + j - LIMBS].0, carry);
            upper.limbs[i + j - LIMBS] = Limb(new_limb);
            j += 1;
        }
        while j < LIMBS {
            std::println!("red 2, i={i}, j={j}");
            (carry, new_limb) = addcarry(upper.limbs[i + j - LIMBS].0, carry);
            upper.limbs[i + j - LIMBS] = Limb(new_limb);
            j += 1;
        }

        (new_sum, meta_carry) = upper.limbs[i].adc(Limb(carry), meta_carry);
        upper.limbs[i] = new_sum;

        i += 1;
    }

    // Division is simply taking the upper half of the limbs
    // Final reduction (at this point, the value is at most 2 * modulus,
    // so `meta_carry` is either 0 or 1)

    sub_mod_with_hi(meta_carry, &upper, modulus, modulus)
}

#[cfg(test)]
mod tests {
    use rand_core::OsRng;

    use super::*;
    use crate::{
        modular::runtime_mod::{DynResidue, DynResidueParams},
        NonZero, Random, U256,
    };

    extern crate std;

    #[test]
    fn foobar() {
        let x = U256::random(&mut OsRng);
        let p =
            (U256::random(&mut OsRng) | U256::ONE) & ((U256::ONE << 128).wrapping_sub(&U256::ONE));
        let x = x.rem(&NonZero::new(p).unwrap());

        let params = DynResidueParams::new(&p);
        let x_m = DynResidue::new(&x, params);
        std::println!("p = {}", p);
        std::println!("x = {}", x_m.retrieve());

        let product = x.mul_wide(&x);
        let z = montgomery_reduction2(
            &product,
            &params.modulus,
            params.mod_neg_inv,
            params.modulus_limbs,
        );
        std::println!("product = {} {}", product.0, product.1);
        std::println!("z = {}", z);
    }
}
