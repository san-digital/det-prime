use std::hint::black_box;
use std::time::Instant;

use det_prime::{
    hash_to_prime_256, is_prime, is_prime_u64, least_nonresidue, prime_in_progression_u64,
    sqrt_mod_prime, U256,
};

fn main() {
    // 1. 64-bit deterministic primality
    let t0 = Instant::now();
    let mut count64 = 0u64;
    for k in 0..10_000u64 {
        if is_prime_u64(black_box(0xffff_ffff_ffff_ffc5u64.wrapping_sub(2 * k))) {
            count64 += 1;
        }
    }
    let dt64 = t0.elapsed();
    println!(
        "is_prime_u64 (10,000 odd 64-bit candidates): {:?} ({:.2} us/call, {} primes)",
        dt64,
        dt64.as_secs_f64() * 1e6 / 10_000.0,
        count64
    );

    // 2. 256-bit deterministic primality on secp256k1 field prime
    let secp =
        U256::from_hex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f").unwrap();
    let t1 = Instant::now();
    let ok = is_prime(black_box(&secp));
    let dt_secp = t1.elapsed();
    assert!(ok);
    println!("is_prime (256-bit secp256k1 prime): {:?}", dt_secp);

    // 3. 256-bit composite rejection (random-looking odd non-prime)
    let comp =
        U256::from_hex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc31").unwrap();
    let t2 = Instant::now();
    for _ in 0..1_000 {
        assert!(!is_prime(black_box(&comp)));
    }
    let dt_comp = t2.elapsed();
    println!(
        "is_prime (256-bit odd composite, 1,000 calls): {:?} ({:.2} us/call)",
        dt_comp,
        dt_comp.as_secs_f64() * 1e6 / 1_000.0
    );

    // 4. Deterministic VDF / Fiat-Shamir hash_to_prime_256
    let digest = [0x42u8; 32];
    let t3 = Instant::now();
    let (p_hash, steps) = hash_to_prime_256(black_box(&digest)).unwrap();
    let dt_hash = t3.elapsed();
    assert_eq!(p_hash.bits(), 255);
    println!(
        "hash_to_prime_256 (255-bit challenge prime, {} odd steps): {:?}",
        steps, dt_hash
    );

    // 5. Deterministic Tonelli-Shanks on Stark252 (2-adicity 192)
    let stark =
        U256::from_hex("0800000000000011000000000000000000000000000000000000000000000001").unwrap();
    let z = least_nonresidue(&stark).unwrap();
    assert_eq!(z, 3);
    let sq = U256::from_u64(9);
    let t4 = Instant::now();
    for _ in 0..100 {
        let r = sqrt_mod_prime(black_box(&sq), black_box(&stark))
            .unwrap()
            .unwrap();
        black_box(r);
    }
    let dt_sqrt = t4.elapsed();
    println!(
        "sqrt_mod_prime (Stark252, 2-adicity 192, 100 calls): {:?} ({:.2} ms/call)",
        dt_sqrt,
        dt_sqrt.as_secs_f64() * 1e3 / 100.0
    );

    // 6. Prime in arithmetic progression (NTT-friendly prime p == 1 mod 2^20)
    let t5 = Instant::now();
    let (ntt_p, ntt_steps) = prime_in_progression_u64(1 << 20, 1).unwrap();
    let dt_ntt = t5.elapsed();
    println!(
        "prime_in_progression_u64 (q = 2^20, a = 1 -> p = {}, {} steps): {:?}",
        ntt_p, ntt_steps, dt_ntt
    );
}
