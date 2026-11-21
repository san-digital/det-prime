use det_prime::{
    is_prime, least_nonresidue, sqrt_mod_prime, verify_miller_bach, CompositeWitness, Error, U128,
    U256, U512,
};

#[test]
fn rejects_arnault_46_digit_11_base_strong_pseudoprime() {
    // Francois Arnault (1995): 46-digit composite strong pseudoprime to all 11 primes 2..=31.
    let n11 = U256::from_decimal("1195068768795265792518361315725116351898245581").unwrap();
    assert!(!is_prime(&n11));
    assert_eq!(
        verify_miller_bach(&n11),
        Err(CompositeWitness::StrongWitness(37))
    );
}

#[test]
fn rejects_sorenson_webster_12_and_13_base_strong_pseudoprimes() {
    // Sorenson and Webster (2017): smallest strong pseudoprime to the first 12 primes (2..=37).
    let psi_12 = U128::from_decimal("318665857834031151167461").unwrap();
    assert!(psi_12.as_u64().is_none());
    assert!(!is_prime(&psi_12));
    assert_eq!(
        verify_miller_bach(&psi_12),
        Err(CompositeWitness::StrongWitness(41))
    );

    // Smallest strong pseudoprime to the first 13 primes (2..=41).
    let psi_13 = U128::from_decimal("3317044064679887385961981").unwrap();
    assert!(!is_prime(&psi_13));
    assert_eq!(
        verify_miller_bach(&psi_13),
        Err(CompositeWitness::StrongWitness(43))
    );
}

#[test]
fn rejects_jiang_deng_9_to_11_base_strong_pseudoprime() {
    // Jiang and Deng (2014): psi_9 = psi_10 = psi_11 = 3825123056546413051,
    // smallest strong pseudoprime to the first 9, 10, and 11 primes (2..=31).
    let psi_9 = U128::from_decimal("3825123056546413051").unwrap();
    assert!(!det_prime::is_prime_u64(3_825_123_056_546_413_051));
    assert!(!is_prime(&psi_9));
    assert_eq!(
        verify_miller_bach(&psi_9),
        Err(CompositeWitness::StrongWitness(37))
    );
}

#[test]
fn rejects_251_bit_chernick_carmichael_in_primality_and_field_ops() {
    // 251-bit Carmichael number C = (6m + 1)(12m + 1)(18m + 1) with m = 2^80 + 15770.
    // Passes Fermat's test a^(C - 1) == 1 (mod C) for all coprime bases and has no small factors.
    let carm = U256::from_decimal(
        "2289833795952786091229564300348384801661184049187983124796226138314273151449",
    )
    .unwrap();
    assert!(!is_prime(&carm));
    assert_eq!(
        verify_miller_bach(&carm),
        Err(CompositeWitness::StrongWitness(2))
    );
    assert_eq!(least_nonresidue(&carm), Err(Error::CompositeModulus));
    assert_eq!(
        sqrt_mod_prime(&U256::from_u64(4), &carm),
        Err(Error::CompositeModulus)
    );
}

#[test]
fn rejects_large_prime_squares_and_composite_mersennes() {
    // Square of Mersenne prime M_127 = (2^127 - 1)^2 = 2^254 - 2^128 + 1.
    // Has only one prime factor (2^127 - 1), well beyond any trial-division table.
    let m127_sq = U256::from_decimal(
        "28948022309329048855892746252171976962977213799489202546401021394546514198529",
    )
    .unwrap();
    assert!(!is_prime(&m127_sq));
    assert_eq!(
        verify_miller_bach(&m127_sq),
        Err(CompositeWitness::StrongWitness(2))
    );

    // M_67 = 2^67 - 1 = 193707721 * 761838257287 (Cole's composite Mersenne).
    let m67 = U128::from_decimal("147573952589676412927").unwrap();
    assert!(!is_prime(&m67));

    // M_257 = 2^257 - 1 is composite.
    let mut m257_bytes = [0xffu8; 33];
    m257_bytes[0] = 0x01;
    let m257 = U512::from_be_bytes(&m257_bytes).unwrap();
    assert!(!is_prime(&m257));
}
