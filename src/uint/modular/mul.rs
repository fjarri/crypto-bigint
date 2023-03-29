use crate::{CtChoice, Limb, Uint, WideWord, Word};

use super::reduction::montgomery_reduction;

pub(crate) const fn mul_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    b: &Uint<LIMBS>,
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    //let product = a.mul_wide(b);
    //montgomery_reduction::<LIMBS>(&product, modulus, mod_neg_inv)
    mul_montgomery_form_combined(a, b, modulus, mod_neg_inv)
}

pub(crate) const fn square_montgomery_form<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let product = a.square_wide();
    montgomery_reduction::<LIMBS>(&product, modulus, mod_neg_inv)
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

/// Returns the pair `(new_borrow, res)` of `x - (y + borrow >> (sizeof(T) - 1))`.
/// `borrow` and `new_borrow` can be either `0` or `typemax(T)`,
/// the latter meaning that the borrow occurred during subtraction.
/// Note that it is not an analogue of `addhilo` for subtraction.
#[inline(always)]
const fn subborrow(x: Word, y: Word, borrow: Word) -> (Word, Word) {
    let res = (x as WideWord)
        .wrapping_sub((y as WideWord).wrapping_add((borrow >> (Word::BITS - 1)) as WideWord));
    ((res >> Word::BITS) as Word, res as Word)
}

/// Multiplies `x` and `y`, returning the most significant
/// and the least significant words as `(hi, lo)`.
#[inline(always)]
const fn mulhilo(x: Word, y: Word) -> (Word, Word) {
    let res = (x as WideWord).wrapping_mul(y as WideWord);
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

    /*
    let (hi, lo) = mulhilo(y, z);
    let (t, r1) = addcarry(x, lo, w);
    let (_, r2) = addcarry(hi, t, 0);
    (r2, r1)
    */
}

/// Returns `x + y * z`, where `x` and `y` are multi-limb integers.
#[inline(always)]
const fn muladd_ml<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    y: &Uint<LIMBS>,
    z: Limb,
) -> (Limb, Uint<LIMBS>) {
    let mut res = [0; LIMBS];
    let mut hi = 0;
    let mut lo;
    let mut i = 0;
    while i < LIMBS {
        (hi, lo) = muladdcarry(x.limbs[i].0, y.limbs[i].0, z.0, hi);
        res[i] = lo;
        i += 1;
    }

    (Limb(hi), Uint::from_words(res))
}

/// And extended version of `subborrow()` for two multi-limb integers `(x..., x_hi)`
/// and `(y..., y_hi)` (`x` and `y` represent lower limbs of the corresponding numbers).
/// Returned `borrow` is the same as for the single-limb `subborrow()`.
#[inline(always)]
const fn subborrow_ml<const LIMBS: usize>(
    x_hi: Limb,
    x: &Uint<LIMBS>,
    y: &Uint<LIMBS>,
) -> (Limb, Uint<LIMBS>) {
    let mut res = [0; LIMBS];
    let mut borrow = 0;
    let mut lo;
    let mut i = 0;
    while i < LIMBS {
        (borrow, lo) = subborrow(x.limbs[i].0, y.limbs[i].0, borrow);
        res[i] = lo;
        i += 1;
    }

    // Analagous to `subborrow(x_hi.0, 0, borrow).
    // That is, new `borrow = Word::MAX` iff `x_hi == 0` and `borrow == Word::MAX`.
    let borrow = (!x_hi.0.wrapping_neg()) & borrow;

    (Limb(borrow), Uint::from_words(res))
}

/// A multi-limb version of `addcarry`.
#[inline(always)]
const fn addcarry_ml<const LIMBS: usize>(x: &Uint<LIMBS>, y: &Uint<LIMBS>) -> (Limb, Uint<LIMBS>) {
    let mut res = [0; LIMBS];
    let mut hi = 0;
    let mut lo;
    let mut i = 0;
    while i < LIMBS {
        (hi, lo) = addcarry(x.limbs[i].0, y.limbs[i].0, hi);
        res[i] = lo;
        i += 1;
    }
    (Limb(hi), Uint::from_words(res))
}

/// Returns `(x..., x_hi) - (y..., y_hi) mod m`.
/// Assumes `-m <= (x..., x_hi) - (y..., y_hi) < m`.
#[inline(always)]
pub(crate) const fn submod_inner<const LIMBS: usize>(
    x_hi: Limb,
    x: &Uint<LIMBS>,
    y: &Uint<LIMBS>,
    m: &Uint<LIMBS>,
) -> Uint<LIMBS> {
    let (borrow, w) = subborrow_ml(x_hi, x, y);

    let mut masked_m = m.to_words();
    let mut i = 0;
    while i < LIMBS {
        masked_m[i] &= borrow.0;
        i += 1;
    }

    // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
    // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
    let (_, res) = addcarry_ml(&w, &Uint::from_words(masked_m));

    res
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

pub(crate) const fn mul_montgomery_form_combined<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    y: &Uint<LIMBS>,
    m: &Uint<LIMBS>,
    m_p: Limb,
) -> Uint<LIMBS> {
    let mut a_lo = Uint::<LIMBS>::ZERO;
    let mut a_hi = 0;

    let mut i = 0;
    while i < LIMBS {
        let u = (a_lo.limbs[0].wrapping_add(x.limbs[i].wrapping_mul(y.limbs[0]))).wrapping_mul(m_p);
        let (a_hi1, a_lo1) = muladd_ml(&a_lo, m, u);
        let (a_hi2, a_lo2) = muladd_ml(&a_lo1, y, x.limbs[i]);
        let (hi, lo) = addcarry(a_hi, a_hi1.0, a_hi2.0);

        a_lo = shift_by_one(&a_lo2, lo);
        a_hi = hi;
        i += 1;
    }

    // Final reduction (at this point, the value is at most 2 * modulus)
    //let must_reduce = CtChoice::from_lsb(a_hi as Word).or(Uint::ct_gt(m, &a_lo).not());
    //a_lo.wrapping_sub(&Uint::ct_select(&Uint::ZERO, m, must_reduce))

    submod_inner(Limb(a_hi), &a_lo, m, m)
}

// Variant 2

/// Adds wide numbers represented by pairs of (most significant word, least significant word)
/// and returns the result in the same format `(hi, lo)`.
#[inline(always)]
const fn addhilo(x_hi: Word, x_lo: Word, y_lo: Word) -> (Word, Word) {
    let res =
        (((x_hi as WideWord) << Word::BITS) | (x_lo as WideWord)).wrapping_add(y_lo as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
}

/// Calculates `x * y`, where `x` is a multi-precision number of length `N`,
/// and `y` is a single radix digit.
/// Returns the `N+1`-long result as tuple of the lowest digit
/// and a multi-precision number with the `N` highest digits.
#[inline(always)]
const fn _mul_by_single<const LIMBS: usize>(x: &Uint<LIMBS>, y: Word) -> (Word, Uint<LIMBS>) {
    let mut w = [0; LIMBS];
    let mut c = 0;
    let mut w_lo = 0;

    let mut j = 0;
    while j < LIMBS {
        let (mut hi, mut lo) = mulhilo(x.limbs[j].0, y);

        if j > 0 {
            (hi, lo) = addhilo(hi, lo, c);
            (hi, lo) = addhilo(hi, lo, w[j - 1]);
        }

        if j == 0 {
            w_lo = lo;
        } else {
            w[j - 1] = lo;
        }
        c = hi;

        j += 1;
    }

    w[LIMBS - 1] = c;

    (w_lo, Uint::from_words(w))
}

#[inline(always)]
const fn mul_by_single<const LIMBS: usize>(x: &Uint<LIMBS>, y: Word) -> (Word, Uint<LIMBS>) {
    let mut w = [0; LIMBS];

    let (mut c, w_lo) = mulhilo(x.as_words()[0], y);
    let mut j = 1;
    while j < LIMBS {
        let (hi, lo) = mulhilo(x.as_words()[j], y);
        let (hi, lo) = addhilo(hi, lo, c);
        let (hi, lo) = addhilo(hi, lo, w[j - 1]);
        w[j - 1] = lo;
        c = hi;
        j += 1;
    }

    w[LIMBS - 1] = c;

    (w_lo, Uint::from_words(w))
}

/// Given a MLUInt {x1, x2, ..., xN-1, xN} returns a tuple (x1, {x2, x3, ..., xN, 0}).
#[inline(always)]
const fn shift_by_one2<const LIMBS: usize>(x: &Uint<LIMBS>) -> (Word, Uint<LIMBS>) {
    let mut res = [0; LIMBS];
    let mut i = 0;
    let lo = x.as_words()[0];
    while i < LIMBS - 1 {
        res[i] = x.as_words()[i + 1];
        i += 1;
    }
    (lo, Uint::from_words(res))
}

/// Montgomery multiplication (or Montgomery reduction algorithm).
/// For `x = x' * R mod m` and `y = y' * R mod m`
/// calculates `x' * y' * R mod m`, where `R = typemax(MLUInt{N, T}) + 1`.
/// `m_prime` is the Montgomery coefficient (see [`get_montgomery_coeff`](@ref)).
const fn mul_montgomery_form_combined2<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    y: &Uint<LIMBS>,
    m: &Uint<LIMBS>,
    m_prime: Limb,
) -> Uint<LIMBS> {
    let m_prime = m_prime.0.wrapping_neg();
    let mut a = Uint::<LIMBS>::ZERO;
    let mut a_lo = 0;

    let mut i = 0;
    while i < LIMBS {
        let (p1_lo, p1) = mul_by_single(y, x.as_words()[i]);
        let mut t = p1_lo;

        if i > 0 {
            t = t.wrapping_add(a_lo);
            a = a.wrapping_add(&p1);
        } else {
            a = p1;
        }

        let u = t.wrapping_mul(m_prime);
        let (_p2_lo, p2) = mul_by_single(m, u);

        // a_lo + p1_lo - p2_lo is always zero mod radix (sizeof(T)+1)
        // We just want to know if we need to carry 1 or not to the higher limbs.
        // If i == 1, a_lo = 0, so the carry is also 0.
        if i > 0 {
            let c = Limb::ct_lt(Limb(a_lo.wrapping_add(p1_lo)), Limb(a_lo));
            let correction = c.select_uint(&Uint::<LIMBS>::ZERO, &Uint::<LIMBS>::ONE);
            a = a.wrapping_add(&correction);

            //if a_lo.wrapping_add(p1_lo) < a_lo {
            //    a = a.wrapping_add(&Uint::<LIMBS>::ONE);
            //}
        }

        // TODO: can `a` be greater than `m` at this point?
        a = a.sub_mod(&p2, &m);

        if i < LIMBS - 1 {
            (a_lo, a) = shift_by_one2(&a);
        }

        i += 1;
    }

    a
}

/*
const fn mul_montgomery_form_combined3<const LIMBS: usize>(
        x: &Uint<LIMBS>, y: &Uint<LIMBS>, m: &Uint<LIMBS>, m_prime: Limb) -> Uint<LIMBS> {

    let mut a = Uint::<LIMBS>::ZERO;
    let mut a_lo = 0;

    let mut i = 0;
    while i < LIMBS {

        // u_i = (a_0 + x_i * y_0) * m_prime mod R
        // a = (a + x_i * y + u_i * m) / R

        let (p1_lo, p1) = mul_by_single(y, x.as_words()[i]); // x_i * y
        let u = a_0.wrappind_add(p1_lo).wrapping_mul(m_prime.0); // u_i
        let (p2_lo, p2) = mul_by_single(m, u); // u_i * m

        // a_lo + p1_lo + p2_lo == 0 mod R





        let (p1_lo, p1) = mul_by_single(y, x.as_words()[i]);
        let mut t = p1_lo;

        if i > 0 {
            t = t.wrapping_add(a_lo);
            a = a.wrapping_add(&p1);
        }
        else {
            a = p1;
        }

        let u = t.wrapping_mul(m_prime.0);
        let (_p2_lo, p2) = mul_by_single(m, u);

        // a_lo + p1_lo - p2_lo is always zero mod radix (sizeof(T)+1)
        // We just want to know if we need to carry 1 or not to the higher limbs.
        // If i == 1, a_lo = 0, so the carry is also 0.
        if i > 1 {
            if a_lo.wrapping_add(p1_lo) < a_lo {
                a = a.wrapping_add(&Uint::<LIMBS>::ONE);
            }
        }

        // TODO: can `a` be greater than `m` at this point?
        a = a.sub_mod(&p2, &m);

        if i < LIMBS - 1 {
            (a_lo, a) = shift_by_one2(&a);
        }

        i += 1;
    }

    a
}
*/

#[cfg(test)]
mod tests {

    //use crate::{Limb, U256};

    /*
    #[test]
    fn mul_by_single_correctness() {
        let x =
            U256::from_be_hex("38139f27413adde026cb71d5a1dbe3d4066cb3040d1c091263530cab8b1c07f7");
        let y = Limb(3537770054);

        let (test_lo, test_hi) = mul_by_single(&x, y);
        let ref_hi =
            U256::from_be_hex("000000002e30be733c97bf652d5e766e0d7239e6a6d741a3a95fa9fcf1de51fa");
        let ref_lo = Limb(48367189963270026);
        assert_eq!(test_hi, ref_hi);
        assert_eq!(test_lo, ref_lo);
    }*/

    /*
    #[test]
    fn combined_mul() {
        let x = U256::random();
        let y = x.wrapping_add(&U256::ONE);
        let m = y.wrapping_add(&U256::ONE);

    }
    */
}
