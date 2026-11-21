#![no_std]
#![forbid(unsafe_code)]
#![doc = include_str!("../README.md")]

#[cfg(feature = "std")]
extern crate std;

pub mod bounds;
pub mod field;
pub mod primality;
pub mod sieve;
pub mod uint;
pub mod wasm;

use core::fmt;

pub use bounds::{
    bach_bound_from_km, bach_witness_bound, lls_bound_from_km, lls_nonresidue_bound,
    ln_upper_scaled, progression_prime_bound, rh_next_prime_step_budget_u64, MAX_SIEVE_BITS,
};
pub use field::{
    euler_totient_u64, hash_to_prime_256, hash_to_prime_256_bounded, jacobi_prime_mod_odd,
    jacobi_u64, least_nonresidue, next_prime_bounded, prime_in_progression_u64, sqrt_mod_prime,
    DEFAULT_HASH_TO_PRIME_STEPS,
};
pub use primality::{
    is_prime, is_prime_u64, verify_miller_bach, CompositeWitness, PrimalityCertificate,
};
pub use sieve::{PrimeIter, MAX_SIEVE_LIMIT};
pub use uint::{MontCtx, Uint, U1024, U128, U2048, U256, U384, U4096, U512};
pub use wasm::{
    hash_to_prime_be_32, is_prime_be_32, is_prime_be_slice, sqrt_mod_prime_be, sqrt_mod_prime_be_32,
};

/// Error type for deterministic prime and finite-field operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// Malformed hexadecimal, decimal, or byte input.
    InvalidInput,
    /// Value exceeds target fixed-width limb capacity.
    Overflow,
    /// Input residue `a` does not satisfy `0 <= a < p`.
    OutOfRange,
    /// Modulus is even or below the required threshold.
    InvalidModulus,
    /// Modulus failed a compositeness or Euler criterion check.
    CompositeModulus,
    /// Progression residue `a` is not coprime to modulus `q`.
    NotCoprime,
    /// Candidate scan exceeded the configured deterministic step cap.
    StepBudgetExceeded,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::InvalidInput => "invalid numeric input",
            Self::Overflow => "integer overflow for target width",
            Self::OutOfRange => "input residue out of range for modulus",
            Self::InvalidModulus => "modulus must be odd and above threshold",
            Self::CompositeModulus => "modulus failed primality or Euler check",
            Self::NotCoprime => "progression residue is not coprime to modulus",
            Self::StepBudgetExceeded => "deterministic candidate step cap exceeded",
        };
        f.write_str(msg)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}
