use crate::{Limb, Uint, Word};

use super::{reduction::montgomery_reduction, Retrieve};

/// Additions between residues with a modulus set at runtime
mod runtime_add;
/// Multiplicative inverses of residues with a modulus set at runtime
mod runtime_inv;
/// Multiplications between residues with a modulus set at runtime
mod runtime_mul;
/// Negations of residues with a modulus set at runtime
mod runtime_neg;
/// Exponentiation of residues with a modulus set at runtime
mod runtime_pow;
/// Subtractions between residues with a modulus set at runtime
mod runtime_sub;

/// The parameters to efficiently go to and from the Montgomery form for a modulus provided at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DynResidueParams<const LIMBS: usize> {
    // The constant modulus
    pub(crate) modulus: Uint<LIMBS>,
    // Parameter used in Montgomery reduction
    r: Uint<LIMBS>,
    // R^2, used to move into Montgomery form
    r2: Uint<LIMBS>,
    // R^3, used to compute the multiplicative inverse
    r3: Uint<LIMBS>,
    // The lowest limbs of -(MODULUS^-1) mod R
    // We only need the LSB because during reduction this value is multiplied modulo 2**Limb::BITS.
    pub(crate) mod_neg_inv: Limb,
    pub(crate) modulus_limbs: usize,
}

impl<const LIMBS: usize> DynResidueParams<LIMBS> {
    /// Instantiates a new set of `ResidueParams` representing the given `modulus`.
    pub fn new(modulus: &Uint<LIMBS>) -> Self {
        let r = Uint::MAX.const_rem(modulus).0.wrapping_add(&Uint::ONE);
        let r2 = Uint::const_rem_wide(r.square_wide(), modulus).0;

        // Since we are calculating the inverse modulo (Word::MAX+1),
        // we can take the modulo right away and calculate the inverse of the first limb only.
        let modulus_lo = Uint::<1>::from_words([modulus.limbs[0].0]);
        let mod_neg_inv =
            Limb(Word::MIN.wrapping_sub(modulus_lo.inv_mod2k(Word::BITS as usize).limbs[0].0));

        // TODO: assuming here that `modulus` is nonzero. Can we do it?
        let modulus_limbs = (modulus.bits() - 1) / Limb::BITS + 1;
        //extern crate std;
        //std::println!("{}", modulus_limbs);
        debug_assert!(
            (modulus_limbs == LIMBS && modulus.limbs[LIMBS - 1].0 > 0)
                || (modulus_limbs < LIMBS && modulus.limbs[LIMBS - 1].0 == 0)
        );

        let r3 = montgomery_reduction(&r2.square_wide(), modulus, mod_neg_inv, modulus_limbs);

        Self {
            modulus: *modulus,
            r,
            r2,
            r3,
            mod_neg_inv,
            modulus_limbs,
        }
    }

    /// Returns the modulus which was used to initialize these parameters.
    pub const fn modulus(&self) -> &Uint<LIMBS> {
        &self.modulus
    }
}

/// A residue represented using `LIMBS` limbs. The odd modulus of this residue is set at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DynResidue<const LIMBS: usize> {
    montgomery_form: Uint<LIMBS>,
    residue_params: DynResidueParams<LIMBS>,
}

impl<const LIMBS: usize> DynResidue<LIMBS> {
    /// Instantiates a new `Residue` that represents this `integer` mod `MOD`.
    pub const fn new(integer: &Uint<LIMBS>, residue_params: DynResidueParams<LIMBS>) -> Self {
        let product = integer.mul_wide(&residue_params.r2);
        let montgomery_form = montgomery_reduction(
            &product,
            &residue_params.modulus,
            residue_params.mod_neg_inv,
            residue_params.modulus_limbs,
        );

        Self {
            montgomery_form,
            residue_params,
        }
    }

    /// Retrieves the integer currently encoded in this `Residue`, guaranteed to be reduced.
    pub const fn retrieve(&self) -> Uint<LIMBS> {
        montgomery_reduction(
            &(self.montgomery_form, Uint::ZERO),
            &self.residue_params.modulus,
            self.residue_params.mod_neg_inv,
            self.residue_params.modulus_limbs,
        )
    }

    /// Instantiates a new `Residue` that represents zero.
    pub const fn zero(residue_params: DynResidueParams<LIMBS>) -> Self {
        Self {
            montgomery_form: Uint::<LIMBS>::ZERO,
            residue_params,
        }
    }

    /// Instantiates a new `Residue` that represents 1.
    pub const fn one(residue_params: DynResidueParams<LIMBS>) -> Self {
        Self {
            montgomery_form: residue_params.r,
            residue_params,
        }
    }

    /// Returns the parameter struct used to initialize this residue.
    pub const fn params(&self) -> &DynResidueParams<LIMBS> {
        &self.residue_params
    }
}

impl<const LIMBS: usize> Retrieve for DynResidue<LIMBS> {
    type Output = Uint<LIMBS>;
    fn retrieve(&self) -> Self::Output {
        self.retrieve()
    }
}
