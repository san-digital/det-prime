//! Big-endian byte-buffer wrappers, convenient for WebAssembly hosts and wire formats.
//! They work on any target.

use crate::field::{hash_to_prime_256, sqrt_mod_prime};
use crate::primality::is_prime;
use crate::uint::{Uint, U256, U512};
use crate::Error;

/// [`is_prime`] on a 32-byte big-endian number.
pub fn is_prime_be_32(bytes: &[u8; 32]) -> bool {
    match U256::from_be_bytes(bytes) {
        Ok(n) => is_prime(&n),
        Err(_) => false,
    }
}

/// [`is_prime`] on a big-endian number of up to 64 bytes (512 bits; leading zero bytes are ignored).
pub fn is_prime_be_slice(bytes: &[u8]) -> Result<bool, Error> {
    let n = U512::from_be_bytes(bytes)?;
    Ok(is_prime(&n))
}

/// [`hash_to_prime_256`] that writes the 255-bit prime as 32 big-endian bytes into
/// `out_prime` and returns the number of odd candidates tested.
pub fn hash_to_prime_be_32(digest: &[u8; 32], out_prime: &mut [u8; 32]) -> Result<u32, Error> {
    let (p, steps) = hash_to_prime_256(digest)?;
    p.write_be_bytes(out_prime)?;
    Ok(steps)
}

/// [`sqrt_mod_prime`] on 32-byte big-endian buffers.
///
/// Writes the canonical root `0 <= r <= (p - 1)/2` into `out_root` and returns `Ok(true)`
/// when `a` is a square mod `p`; clears `out_root` and returns `Ok(false)` when `a` is a
/// non-residue; returns `Err(_)` on an even or tiny modulus, `a >= p`, or a modulus detected
/// to be composite. `p` must be prime; see [`sqrt_mod_prime`] for what a composite `p` yields.
pub fn sqrt_mod_prime_be_32(
    a_bytes: &[u8; 32],
    p_bytes: &[u8; 32],
    out_root: &mut [u8; 32],
) -> Result<bool, Error> {
    let a = U256::from_be_bytes(a_bytes)?;
    let p = U256::from_be_bytes(p_bytes)?;
    match sqrt_mod_prime(&a, &p)? {
        Some(r) => {
            r.write_be_bytes(out_root)?;
            Ok(true)
        }
        None => {
            out_root.fill(0);
            Ok(false)
        }
    }
}

/// [`sqrt_mod_prime`] on big-endian byte slices, for any limb count `LIMBS`.
pub fn sqrt_mod_prime_be<const LIMBS: usize>(
    a_bytes: &[u8],
    p_bytes: &[u8],
    out_root: &mut [u8],
) -> Result<bool, Error> {
    let a = Uint::<LIMBS>::from_be_bytes(a_bytes)?;
    let p = Uint::<LIMBS>::from_be_bytes(p_bytes)?;
    match sqrt_mod_prime(&a, &p)? {
        Some(r) => {
            r.write_be_bytes(out_root)?;
            Ok(true)
        }
        None => {
            out_root.fill(0);
            Ok(false)
        }
    }
}
