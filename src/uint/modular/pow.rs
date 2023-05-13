use crate::{Limb, Uint, Word};

use super::mul::{mul_montgomery_form, square_montgomery_form};

/// Performs modular exponentiation using Montgomery's ladder.
/// `exponent_bits` represents the number of bits to take into account for the exponent.
///
/// NOTE: this value is leaked in the time pattern.
pub const fn pow_montgomery_form<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    exponent: &Uint<LIMBS>,
    exponent_bits: usize,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    if exponent_bits == 0 {
        return *r; // 1 in Montgomery form
    }

    const WINDOW: usize = 4;
    const WINDOW_MASK: Word = (1 << WINDOW) - 1;

    // powers[i] contains x^i
    let mut powers = [*r; 1 << WINDOW];
    powers[1] = *x;
    let mut i = 2;
    while i < powers.len() {
        powers[i] = mul_montgomery_form(&powers[i - 1], x, modulus, mod_neg_inv);
        i += 1;
    }

    let starting_limb = (exponent_bits - 1) / Limb::BITS;
    let starting_bit_in_limb = (exponent_bits - 1) % Limb::BITS;
    let starting_window = starting_bit_in_limb / WINDOW;
    let starting_window_mask = (1 << (starting_bit_in_limb % WINDOW + 1)) - 1;

    let mut z = *r; // 1 in Montgomery form

    let mut limb_num = starting_limb + 1;
    while limb_num > 0 {
        limb_num -= 1;
        let w = exponent.as_limbs()[limb_num].0;

        let mut window_num = if limb_num == starting_limb {
            starting_window + 1
        } else {
            Limb::BITS / WINDOW
        };
        while window_num > 0 {
            window_num -= 1;

            let mut idx = (w >> (window_num * WINDOW)) & WINDOW_MASK;

            if limb_num == starting_limb && window_num == starting_window {
                idx &= starting_window_mask;
            } else {
                let mut i = 0;
                while i < WINDOW {
                    i += 1;
                    z = square_montgomery_form(&z, modulus, mod_neg_inv);
                }
            }

            // Constant-time lookup in the array of powers
            let mut power = powers[0];
            let mut i = 1;
            while i < 1 << WINDOW {
                let choice = Limb::ct_eq(Limb(i as Word), Limb(idx));
                power = Uint::<LIMBS>::ct_select(&power, &powers[i], choice);
                i += 1;
            }

            z = mul_montgomery_form(&z, &power, modulus, mod_neg_inv);
        }
    }

    z
}


pub const fn _pow_vartime<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    exponent: &Uint<LIMBS>,
    exponent_bits: usize,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    if exponent_bits == 0 {
        return *r; // 1 in Montgomery form
    }

    const WINDOW: usize = 4;
    const WINDOW_MASK: Word = (1 << WINDOW) - 1;

    // powers[i] contains x^i
    let mut powers = [*r; 1 << WINDOW];
    powers[1] = *x;
    let mut i = 2;
    while i < powers.len() {
        powers[i] = mul_montgomery_form(&powers[i - 1], x, modulus, mod_neg_inv);
        i += 1;
    }

    let starting_limb = (exponent_bits - 1) / Limb::BITS;
    let starting_bit_in_limb = (exponent_bits - 1) % Limb::BITS;
    let starting_window = starting_bit_in_limb / WINDOW;
    let starting_window_mask = (1 << (starting_bit_in_limb % WINDOW + 1)) - 1;

    let mut z = *r; // 1 in Montgomery form

    let mut limb_num = starting_limb + 1;
    while limb_num > 0 {
        limb_num -= 1;
        let w = exponent.as_limbs()[limb_num].0;

        let mut window_num = if limb_num == starting_limb {
            starting_window + 1
        } else {
            Limb::BITS / WINDOW
        };
        while window_num > 0 {
            window_num -= 1;

            let mut idx = (w >> (window_num * WINDOW)) & WINDOW_MASK;

            if limb_num == starting_limb && window_num == starting_window {
                idx &= starting_window_mask;
            } else {
                let mut i = 0;
                while i < WINDOW {
                    i += 1;
                    z = square_montgomery_form(&z, modulus, mod_neg_inv);
                }
            }

            z = mul_montgomery_form(&z, &powers[idx as usize], modulus, mod_neg_inv);
        }
    }

    z
}



pub fn pow_vartime<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    exponent: &Uint<LIMBS>,
    _exponent_bits: usize,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    const WINDOW: usize = 5;
    const WINDOW_MASK: Word = (1 << (WINDOW - 1)) - 1;

    let m = exponent.bits_vartime();

    if m == 0 {
        return *r; // 1 in Montgomery form
    }

    let mut powers = [*r; 1 << (WINDOW - 1)];

    let mut x_start = *x;
    for _ in 0..WINDOW-1 {
        x_start = square_montgomery_form(&x_start, modulus, mod_neg_inv);
    }
    // x_start = x^(2^(WINDOW-1))

    powers[0] = x_start;
    for i in 1..(1 << (WINDOW - 1)) {
        powers[i] = mul_montgomery_form(&powers[i - 1], x, modulus, mod_neg_inv);
    }

    let mut Q = *r;
    let mut i = m - 1;
    loop {
        if !exponent.bit_vartime(i) {
            Q = square_montgomery_form(&Q, modulus, mod_neg_inv);
            if i == 0 {
                break;
            }
            i -= 1;
        }
        else {
            if i < WINDOW - 1 {
                let mask = (1 << (i + 1)) - 1;
                let small_power = exponent.as_words()[0] & mask;
                let bits = Word::BITS - small_power.leading_zeros();

                for j in (0..bits).rev() {
                    Q = square_montgomery_form(&Q, modulus, mod_neg_inv);
                    if (small_power >> j) & 1 == 1 {
                        Q = mul_montgomery_form(&Q, &x, modulus, mod_neg_inv);
                    }
                }

                break;
            }
            else {
                let t = (exponent >> (i + 1 - WINDOW)).as_words()[0] & WINDOW_MASK;
                for _ in 0..WINDOW {
                    Q = square_montgomery_form(&Q, modulus, mod_neg_inv);
                }
                Q = mul_montgomery_form(&Q, &powers[t as usize], modulus, mod_neg_inv);
                if i == WINDOW - 1 {
                    break;
                }
                else {
                    i -= WINDOW;
                }
            }
        }
    }
    Q
}
extern crate std;



pub fn pow_vartime_primes<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    exponent: &Uint<LIMBS>,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let m = exponent.bits_vartime();

    if m == 0 {
        return *r; // 1 in Montgomery form
    }

    /*
    const WINDOW: usize = 8;
    const PRIMES_NUM: usize = 55;
    const precompute: [[u8; 3]; PRIMES_NUM-1] = [[1, 1, 0],[2, 1, 0],[3, 2, 0],[4, 2, 0],[5, 3, 1],[6, 2, 0],[7, 3, 1],[8, 2, 0],[9, 3, 1],[10, 4, 1],[11, 2, 0],[12, 4, 1],[13, 3, 1],[14, 2, 0],[15, 3, 1],[16, 4, 1],[17, 4, 1],[18, 2, 0],[19, 4, 1],[20, 3, 1],[21, 2, 0],[22, 4, 1],[23, 3, 1],[24, 4, 1],[25, 5, 1],[26, 3, 1],[27, 2, 0],[28, 3, 1],[29, 2, 0],[30, 3, 1],[31, 7, 1],[32, 3, 1],[33, 4, 1],[34, 2, 0],[35, 5, 3],[36, 2, 0],[37, 4, 1],[38, 4, 1],[39, 3, 1],[40, 4, 1],[41, 4, 1],[42, 2, 0],[43, 5, 3],[44, 2, 0],[45, 3, 1],[46, 2, 0],[47, 6, 1],[48, 6, 1],[49, 3, 1],[50, 2, 0],[51, 3, 1],[52, 4, 1],[53, 2, 0],[54, 5, 3]];
    const precompute2: [[u8; 3]; 1 << WINDOW] = [[1, 0, 0], [2, 0, 0],[3, 0, 0],[4, 0, 0],[4, 2, 0],[5, 0, 0],[5, 2, 0],[6, 0, 0],[6, 2, 0],[6, 3, 0],[6, 4, 0],[7, 0, 0],[7, 2, 0],[8, 0, 0],[8, 2, 0],[8, 3, 0],[8, 4, 0],[9, 0, 0],[9, 2, 0],[10, 0, 0],[10, 2, 0],[10, 3, 0],[10, 4, 0],[11, 0, 0],[11, 2, 0],[11, 3, 0],[11, 4, 0],[11, 4, 2],[11, 5, 0],[12, 0, 0],[12, 2, 0],[13, 0, 0],[13, 2, 0],[13, 3, 0],[13, 4, 0],[13, 4, 2],[13, 5, 0],[14, 0, 0],[14, 2, 0],[14, 3, 0],[14, 4, 0],[15, 0, 0],[15, 2, 0],[16, 0, 0],[16, 2, 0],[16, 3, 0],[16, 4, 0],[17, 0, 0],[17, 2, 0],[17, 3, 0],[17, 4, 0],[17, 4, 2],[17, 5, 0],[18, 0, 0],[18, 2, 0],[18, 3, 0],[18, 4, 0],[18, 4, 2],[18, 5, 0],[19, 0, 0],[19, 2, 0],[20, 0, 0],[20, 2, 0],[20, 3, 0],[20, 4, 0],[20, 4, 2],[20, 5, 0],[21, 0, 0],[21, 2, 0],[21, 3, 0],[21, 4, 0],[22, 0, 0],[22, 2, 0],[23, 0, 0],[23, 2, 0],[23, 3, 0],[23, 4, 0],[23, 4, 2],[23, 5, 0],[24, 0, 0],[24, 2, 0],[24, 3, 0],[24, 4, 0],[25, 0, 0],[25, 2, 0],[25, 3, 0],[25, 4, 0],[25, 4, 2],[25, 5, 0],[26, 0, 0],[26, 2, 0],[26, 3, 0],[26, 4, 0],[26, 4, 2],[26, 5, 0],[26, 5, 2],[26, 6, 0],[27, 0, 0],[27, 2, 0],[27, 3, 0],[27, 4, 0],[28, 0, 0],[28, 2, 0],[29, 0, 0],[29, 2, 0],[29, 3, 0],[29, 4, 0],[30, 0, 0],[30, 2, 0],[31, 0, 0],[31, 2, 0],[31, 3, 0],[31, 4, 0],[32, 0, 0],[32, 2, 0],[32, 3, 0],[32, 4, 0],[32, 4, 2],[32, 5, 0],[32, 5, 2],[32, 6, 0],[32, 6, 2],[31, 8, 0],[32, 6, 4],[32, 7, 0],[32, 7, 2],[32, 8, 0],[33, 0, 0],[33, 2, 0],[33, 3, 0],[33, 4, 0],[34, 0, 0],[34, 2, 0],[34, 3, 0],[34, 4, 0],[34, 4, 2],[34, 5, 0],[35, 0, 0],[35, 2, 0],[36, 0, 0],[36, 2, 0],[36, 3, 0],[36, 4, 0],[36, 4, 2],[36, 5, 0],[36, 5, 2],[36, 6, 0],[36, 6, 2],[35, 7, 0],[37, 0, 0],[37, 2, 0],[38, 0, 0],[38, 2, 0],[38, 3, 0],[38, 4, 0],[38, 4, 2],[38, 5, 0],[39, 0, 0],[39, 2, 0],[39, 3, 0],[39, 4, 0],[39, 4, 2],[39, 5, 0],[40, 0, 0],[40, 2, 0],[40, 3, 0],[40, 4, 0],[41, 0, 0],[41, 2, 0],[41, 3, 0],[41, 4, 0],[41, 4, 2],[41, 5, 0],[42, 0, 0],[42, 2, 0],[42, 3, 0],[42, 4, 0],[42, 4, 2],[42, 5, 0],[43, 0, 0],[43, 2, 0],[44, 0, 0],[44, 2, 0],[44, 3, 0],[44, 4, 0],[44, 4, 2],[44, 5, 0],[44, 5, 2],[44, 6, 0],[44, 6, 2],[43, 7, 0],[45, 0, 0],[45, 2, 0],[46, 0, 0],[46, 2, 0],[46, 3, 0],[46, 4, 0],[47, 0, 0],[47, 2, 0],[48, 0, 0],[48, 2, 0],[48, 3, 0],[48, 4, 0],[48, 4, 2],[48, 5, 0],[48, 5, 2],[48, 6, 0],[48, 6, 2],[47, 7, 0],[48, 6, 4],[48, 7, 0],[49, 0, 0],[49, 2, 0],[49, 3, 0],[49, 4, 0],[49, 4, 2],[49, 5, 0],[49, 5, 2],[49, 6, 0],[49, 6, 2],[47, 11, 0],[49, 6, 4],[49, 7, 0],[50, 0, 0],[50, 2, 0],[50, 3, 0],[50, 4, 0],[51, 0, 0],[51, 2, 0],[52, 0, 0],[52, 2, 0],[52, 3, 0],[52, 4, 0],[53, 0, 0],[53, 2, 0],[53, 3, 0],[53, 4, 0],[53, 4, 2],[53, 5, 0],[54, 0, 0],[54, 2, 0],[55, 0, 0],[55, 2, 0],[55, 3, 0],[55, 4, 0],[55, 4, 2],[55, 5, 0],[55, 5, 2],[55, 6, 0],[55, 6, 2],[54, 7, 0],[56, 0, 0],[56, 2, 0],[56, 3, 0],[56, 4, 0],[56, 4, 2]];
    */

    const WINDOW: usize = 6;
    const PRIMES_NUM: usize = 19;
    const precompute: [[u8; 3]; PRIMES_NUM-1] = [[1, 1, 0],[2, 1, 0],[3, 2, 0],[4, 2, 0],[5, 3, 1],[6, 2, 0],[7, 3, 1],[8, 2, 0],[9, 3, 1],[10, 4, 1],[11, 2, 0],[12, 4, 1],[13, 3, 1],[14, 2, 0],[15, 3, 1],[16, 4, 1],[17, 4, 1],[18, 2, 0]];
    const precompute2: [[u8; 3]; 1 << WINDOW] = [[1, 0, 0], [2, 0, 0],[3, 0, 0],[4, 0, 0],[4, 2, 0],[5, 0, 0],[5, 2, 0],[6, 0, 0],[6, 2, 0],[6, 3, 0],[6, 4, 0],[7, 0, 0],[7, 2, 0],[8, 0, 0],[8, 2, 0],[8, 3, 0],[8, 4, 0],[9, 0, 0],[9, 2, 0],[10, 0, 0],[10, 2, 0],[10, 3, 0],[10, 4, 0],[11, 0, 0],[11, 2, 0],[11, 3, 0],[11, 4, 0],[11, 4, 2],[11, 5, 0],[12, 0, 0],[12, 2, 0],[13, 0, 0],[13, 2, 0],[13, 3, 0],[13, 4, 0],[13, 4, 2],[13, 5, 0],[14, 0, 0],[14, 2, 0],[14, 3, 0],[14, 4, 0],[15, 0, 0],[15, 2, 0],[16, 0, 0],[16, 2, 0],[16, 3, 0],[16, 4, 0],[17, 0, 0],[17, 2, 0],[17, 3, 0],[17, 4, 0],[17, 4, 2],[17, 5, 0],[18, 0, 0],[18, 2, 0],[18, 3, 0],[18, 4, 0],[18, 4, 2],[18, 5, 0],[19, 0, 0],[19, 2, 0],[20, 0, 0],[20, 2, 0],[20, 3, 0]];

    /*
    const WINDOW: usize = 5;
    const PRIMES_NUM: usize = 12;
    const precompute: [[u8; 3]; PRIMES_NUM-1] = [[1, 1, 0],[2, 1, 0],[3, 2, 0],[4, 2, 0],[5, 3, 1],[6, 2, 0],[7, 3, 1],[8, 2, 0],[9, 3, 1],[10, 4, 1],[11, 2, 0]];
    const precompute2: [[u8; 3]; 1 << WINDOW] = [[1, 0, 0], [2, 0, 0],[3, 0, 0],[4, 0, 0],[4, 2, 0],[5, 0, 0],[5, 2, 0],[6, 0, 0],[6, 2, 0],[6, 3, 0],[6, 4, 0],[7, 0, 0],[7, 2, 0],[8, 0, 0],[8, 2, 0],[8, 3, 0],[8, 4, 0],[9, 0, 0],[9, 2, 0],[10, 0, 0],[10, 2, 0],[10, 3, 0],[10, 4, 0],[11, 0, 0],[11, 2, 0],[11, 3, 0],[11, 4, 0],[11, 4, 2],[11, 5, 0],[12, 0, 0],[12, 2, 0],[13, 0, 0]];
    */

    const WINDOW_MASK: Word = (1 << WINDOW) - 1;

    let mut powers = [Uint::<LIMBS>::ZERO; PRIMES_NUM+1];
    powers[0] = *r;
    powers[1] = *x;
    for i in 1..PRIMES_NUM {
        let decomp = precompute[i-1];
        let x1 = powers[decomp[0] as usize];
        let x2 = powers[decomp[1] as usize];
        let mut t = mul_montgomery_form(&x1, &x2, modulus, mod_neg_inv);
        if decomp[2] != 0 {
            let x3 = powers[decomp[2] as usize];
            t = mul_montgomery_form(&t, &x3, modulus, mod_neg_inv);
        }
        powers[i+1] = t;
    }

    //std::println!("{:?}", powers);


    let num_windows = (m - 1) / WINDOW + 1;
    let mut res = *r;

    //std::println!("exponent = {}", exponent);

    let power = (exponent >> ((num_windows - 1) * WINDOW)).as_words()[0] & WINDOW_MASK;
    //std::println!("i = {i}, power = {}", power);
    let decomp = precompute2[power as usize];
    //std::println!("decomp = {:?}", decomp);
    res = mul_montgomery_form(&res, &powers[decomp[0] as usize - 1], modulus, mod_neg_inv);
    if decomp[1] != 0 {
        res = mul_montgomery_form(&res, &powers[decomp[1] as usize - 1], modulus, mod_neg_inv);
    }
    if decomp[2] != 0 {
        res = mul_montgomery_form(&res, &powers[decomp[2] as usize - 1], modulus, mod_neg_inv);
    }

    for i in (0..num_windows-1).rev() {
        for _ in 0..WINDOW {
            res = square_montgomery_form(&res, modulus, mod_neg_inv);
        }
        let power = (exponent >> (i * WINDOW)).as_words()[0] & WINDOW_MASK;
        //std::println!("i = {i}, power = {}", power);
        let decomp = precompute2[power as usize];
        //std::println!("decomp = {:?}", decomp);
        res = mul_montgomery_form(&res, &powers[decomp[0] as usize - 1], modulus, mod_neg_inv);
        if decomp[1] != 0 {
            res = mul_montgomery_form(&res, &powers[decomp[1] as usize - 1], modulus, mod_neg_inv);
        }
        if decomp[2] != 0 {
            res = mul_montgomery_form(&res, &powers[decomp[2] as usize - 1], modulus, mod_neg_inv);
        }
    }

    res
}


pub fn pow_vartime_chain<const LIMBS: usize>(
    x: &Uint<LIMBS>,
    exponent: &Uint<LIMBS>,
    modulus: &Uint<LIMBS>,
    r: &Uint<LIMBS>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let m = exponent.bits_vartime();

    if m == 0 {
        return *r; // 1 in Montgomery form
    }

    std::println!("calculating chain");

    let chain = build_addition_chain(exponent);

    //std::println!("{:?}", chain);

    let mut powers = vec![Uint::ZERO; chain.len() + 1];

    std::println!("calculating result");

    powers[0] = *x;

    for (i, step) in chain.iter().enumerate() {
        match step {
            Step::Double { index } => {
                powers[i + 1] = square_montgomery_form(&powers[*index], modulus, mod_neg_inv);
            },
            Step::Add { left, right } => {
                powers[i + 1] = mul_montgomery_form(&powers[*left], &powers[*right], modulus, mod_neg_inv);
            }
        }
    }

    powers[chain.len()]
}






extern crate alloc;
use alloc::{vec, vec::Vec};
use core::ops::{Add, Mul};

use crate::NonZero;


/// A wrapper around an addition chain. Addition and multiplication operations are defined
/// according to the BBBD algorithm.
#[derive(Debug)]
pub(super) struct Chain<const L: usize>(Vec<Uint<L>>);

impl<const L: usize> Add<&Uint<L>> for Chain<L> {
    type Output = Self;

    fn add(mut self, k: &Uint<L>) -> Self {
        self.0.push(k.wrapping_add(self.0.last().expect("chain is not empty")));
        self
    }
}

impl<const L: usize> Mul<Chain<L>> for Chain<L> {
    type Output = Self;

    fn mul(mut self, mut other: Chain<L>) -> Self {
        let last = self.0.last().expect("chain is not empty");

        // The first element of every chain is 1, so we skip it to prevent duplicate
        // entries in the resulting chain.
        assert!(other.0.remove(0) == Uint::ONE);

        for w in other.0.iter_mut() {
            *w = w.wrapping_mul(last);
        }
        self.0.append(&mut other.0);

        self
    }
}

fn minchain<const L: usize>(n: &Uint<L>) -> Chain<L> {
    let log_n = n.bits() - 1;
    if n == &(Uint::ONE << log_n) {
        Chain((0..=log_n).map(|i| Uint::ONE << i).collect())
    } else if n == &Uint::from(3u32) {
        Chain(vec![Uint::ONE, Uint::from(2u32), *n])
    } else {
        // The minchain() algorithm on page 162 of HEHCC indicates that k should be set to
        // 2^(log(n) / 2) in the call to chain(). This is at odds with the definition of k
        // at the bottom of page 161; the latter gives the intended result.
        let k = n >> (log_n / 2); // NonZero::new(Uint::ONE << (log_n / 2)).unwrap();
        chain(n, &k)
    }
}

fn chain<const L: usize>(n: &Uint<L>, k: &Uint<L>) -> Chain<L> {
    let (q, r) = n.div_rem(&NonZero::new(*k).unwrap());
    if r == Uint::ZERO || r == Uint::ONE {
        // We handle the r = 1 case here to prevent unnecessary recursion.
        minchain(k) * minchain(&q) + &r
    } else {
        chain(k, &r) * minchain(&q) + &r
    }
}

/// Returns the shortest addition chain we can find for the given number, using all
/// available algorithms.
pub fn find_shortest_chain<const L: usize>(n: &Uint<L>) -> Vec<Uint<L>> {
    minchain(n).0
}

/// A single step in computing an addition chain.
#[derive(Debug, PartialEq)]
pub enum Step {
    Double { index: usize },
    Add { left: usize, right: usize },
}

/// Converts an addition chain into a series of steps.
pub fn build_steps<const L: usize>(chain: Vec<Uint<L>>) -> Option<Vec<Step>> {
    match chain.get(0) {
        Some(n) if n == &Uint::ONE => (),
        _ => return None,
    }

    let mut steps = vec![];

    for (i, val) in chain.iter().enumerate().skip(1) {
        // Find the pair of previous values that add to this one
        'search: for (j, left) in chain[..i].iter().enumerate() {
            for (k, right) in chain[..=j].iter().enumerate() {
                if val == &left.wrapping_add(&right) {
                    // Found the pair!
                    if j == k {
                        steps.push(Step::Double { index: j })
                    } else {
                        steps.push(Step::Add { left: j, right: k });
                    }
                    break 'search;
                }
            }
        }

        // We must always find a matching pair
        if steps.len() != i {
            return None;
        }
    }

    Some(steps)
}

/// Generates a series of steps that will compute an addition chain for the given number.
/// The addition chain is the shortest we can find using all available algorithms.
pub fn build_addition_chain<const L: usize>(n: &Uint<L>) -> Vec<Step> {
    build_steps(find_shortest_chain(n)).expect("chain is valid")
}
