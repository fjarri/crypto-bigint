use crate::{Limb, Uint, WideWord, Word};

use super::reduction::montgomery_reduction;

pub(crate) const fn mul_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    b: &Uint<LIMBS>,
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
    modulus_limbs: usize,
) -> Uint<LIMBS> {
    //let product = a.mul_wide(b);
    //montgomery_reduction::<LIMBS>(&product, modulus, mod_neg_inv, modulus_limbs)
    mul_montgomery_form_combined(a, b, modulus, mod_neg_inv, modulus_limbs)
}

pub(crate) const fn square_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let product = a.square_wide();
    montgomery_reduction::<LIMBS>(&product, modulus, mod_neg_inv, LIMBS)
}

/// Returns the pair `(hi, lo)` of `x + y + z`.
/// That is, `hi * R + lo = x + y + z`,
/// where `0 <= x, y, z, lo < R`, `hi <= 2`, and `R = typemax(T) + 1`.
/// If `z <= 1`, `hi <= 1` (so it can be used as `new_carry, res = addcarry(x, y, carry)`).
#[inline(always)]
const fn addcarry(x: Word, y: Word, z: Word) -> (Word, Word) {
    let res = (x as WideWord)
        .wrapping_add(y as WideWord)
        .wrapping_add(z as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
}

/// Returns the pair `(hi, lo)` of `x + y * z + w`.
/// That is, `hi * R + lo = x + y * z + w`,
/// where `0 <= x, y, z, w, hi, lo < R`, and `R = Limb::MAX + 1`.
#[inline(always)]
const fn muladdcarry(x: Word, y: Word, z: Word, w: Word) -> (Word, Word) {
    let res = (z as WideWord)
        .wrapping_mul(y as WideWord)
        .wrapping_add(x as WideWord)
        .wrapping_add(w as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
}

/// Returns `x + y * z`, where `x` and `y` are multi-limb integers.
#[inline(always)]
const fn muladd_ml<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    y: &Uint<LIMBS>,
    z: Limb,
    y_limbs: usize,
) -> (Limb, Uint<LIMBS>) {
    let mut res = [0; LIMBS];
    let mut hi = 0;
    let mut lo;
    let mut i = 0;
    while i < y_limbs {
        (hi, lo) = muladdcarry(x.limbs[i].0, y.limbs[i].0, z.0, hi);
        res[i] = lo;
        i += 1;
    }
    while i < LIMBS {
        (hi, lo) = addcarry(x.limbs[i].0, 0, hi);
        res[i] = lo;
        i += 1;
    }

    (Limb(hi), Uint::from_words(res))
}

#[inline(always)]
const fn shift_by_one<const LIMBS: usize>(x: &Uint<LIMBS>, hi: Word) -> Uint<LIMBS> {
    let mut res = [0; LIMBS];
    let mut i = 0;
    while i < LIMBS - 1 {
        res[i] = x.limbs[i + 1].0;
        i += 1;
    }
    res[LIMBS - 1] = hi;
    Uint::from_words(res)
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

pub(crate) const fn mul_montgomery_form_combined<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    y: &Uint<LIMBS>,
    m: &Uint<LIMBS>,
    m_p: Limb,
    modulus_limbs: usize,
) -> Uint<LIMBS> {
    let mut a_lo = Uint::<LIMBS>::ZERO;
    let mut a_hi = 0;
    let mut i = 0;

    if modulus_limbs == LIMBS {
        while i < LIMBS {
            let u =
                (a_lo.limbs[0].wrapping_add(x.limbs[i].wrapping_mul(y.limbs[0]))).wrapping_mul(m_p);
            let (a_hi1, a_lo1) = muladd_ml(&a_lo, m, u, LIMBS);
            let (a_hi2, a_lo2) = muladd_ml(&a_lo1, y, x.limbs[i], LIMBS);
            let (hi, lo) = addcarry(a_hi, a_hi1.0, a_hi2.0);

            a_lo = shift_by_one(&a_lo2, lo);
            a_hi = hi;
            i += 1;
        }
    } else {
        while i < modulus_limbs {
            let u =
                (a_lo.limbs[0].wrapping_add(x.limbs[i].wrapping_mul(y.limbs[0]))).wrapping_mul(m_p);
            let (a_hi1, a_lo1) = muladd_ml(&a_lo, m, u, modulus_limbs);
            let (a_hi2, a_lo2) = muladd_ml(&a_lo1, y, x.limbs[i], modulus_limbs);
            let (hi, lo) = addcarry(a_hi, a_hi1.0, a_hi2.0);

            a_lo = shift_by_one(&a_lo2, lo);
            a_hi = hi;
            i += 1;
        }
        while i < LIMBS {
            let u = a_lo.limbs[0].wrapping_mul(m_p);
            let (a_hi1, a_lo1) = muladd_ml(&a_lo, m, u, modulus_limbs);
            let (hi, lo) = addcarry(a_hi, a_hi1.0, 0);

            a_lo = shift_by_one(&a_lo1, lo);
            a_hi = hi;
            i += 1;
        }
    }

    // Final reduction (at this point, the value is at most 2 * modulus)
    //let must_reduce = CtChoice::from_lsb(a_hi as Word).or(Uint::ct_gt(m, &a_lo).not());
    //a_lo.wrapping_sub(&Uint::ct_select(&Uint::ZERO, m, must_reduce))

    sub_mod_with_hi(Limb(a_hi), &a_lo, m, m)
}
