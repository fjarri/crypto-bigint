use crate::{CtChoice, Limb, Uint, WideWord, Word};

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

#[inline(always)]
const fn muladdcarry(x: Word, y: Word, z: Word, w: Word) -> (Word, Word) {
    let res = (x as WideWord)
        .wrapping_mul(y as WideWord)
        .wrapping_add(z as WideWord)
        .wrapping_add(w as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
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

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
pub const fn montgomery_reduction<const LIMBS: usize>(
    lower_upper: &(Uint<LIMBS>, Uint<LIMBS>),
    modulus: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let (mut lower, mut upper) = *lower_upper;

    let mut meta_carry = 0;
    let mut new_sum;

    let mut i = 0;
    while i < LIMBS {
        let u = lower.limbs[i].0.wrapping_mul(mod_neg_inv.0);

        let (mut carry, _) = muladdcarry(u, modulus.limbs[0].0, lower.limbs[i].0, 0);
        let mut new_limb;

        let mut j = 1;
        while j < (LIMBS - i) {
            (carry, new_limb) = muladdcarry(u, modulus.limbs[j].0, lower.limbs[i + j].0, carry);
            lower.limbs[i + j] = Limb(new_limb);
            j += 1;
        }
        while j < LIMBS {
            (carry, new_limb) =
                muladdcarry(u, modulus.limbs[j].0, upper.limbs[i + j - LIMBS].0, carry);
            upper.limbs[i + j - LIMBS] = Limb(new_limb);
            j += 1;
        }

        (meta_carry, new_sum) = addcarry(upper.limbs[i].0, carry, meta_carry);
        upper.limbs[i] = Limb(new_sum);

        i += 1;
    }

    // Division is simply taking the upper half of the limbs
    // Final reduction (at this point, the value is at most 2 * modulus)
    //let must_reduce = CtChoice::from_lsb(meta_carry as Word).or(Uint::ct_gt(modulus, &upper).not());
    //upper = upper.wrapping_sub(&Uint::ct_select(&Uint::ZERO, modulus, must_reduce));
    //upper

    submod_inner(Limb(meta_carry), &upper, modulus, modulus)
}
