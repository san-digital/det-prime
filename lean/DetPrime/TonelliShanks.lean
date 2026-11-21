import DetPrime.PrimeWitness

/-!
# Deterministic Tonelli-Shanks and Prime Non-Residue Reduction

Machine-checked invariants backing `least_nonresidue` and `sqrt_mod_prime` in `src/field.rs`:
1. `squaresSubgroup` and `prime_nonresidue_witness`: If any coprime integer `1 <= a <= B` is a
   quadratic non-residue modulo prime `p`, then some prime `q <= B` is a quadratic non-residue.
2. `sqrt_three_mod_four`: Exact correctness of the `p % 4 = 3` square-root branch `a^((p+1)/4)`.
3. `tonelli_shanks_init`, `tonelli_shanks_step`, and `tonelli_shanks_done`: Initialization,
   strictly decreasing 2-adic order step invariant, and postcondition for Tonelli-Shanks.
-/

namespace DetPrime

/-- Subgroup of quadratic residues inside `(ZMod p)^x` for prime `p`. -/
def squaresSubgroup (p : ℕ) [Fact p.Prime] : Subgroup (ZMod p)ˣ where
  carrier := { u : (ZMod p)ˣ | IsSquare (u : ZMod p) }
  one_mem' := by
    change IsSquare ((1 : (ZMod p)ˣ) : ZMod p)
    rw [Units.val_one]
    exact IsSquare.one
  mul_mem' {u v} hu hv := by
    change IsSquare (((u * v : (ZMod p)ˣ) : ZMod p))
    rw [Units.val_mul]
    exact IsSquare.mul hu hv
  inv_mem' {u} hu := by
    change IsSquare (((u⁻¹ : (ZMod p)ˣ) : ZMod p))
    rcases hu with ⟨x, hx⟩
    refine ⟨x⁻¹, ?_⟩
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hx
      exact Units.ne_zero u hx
    have hmul : (u : ZMod p) * (x⁻¹ * x⁻¹) = 1 := by
      rw [hx]
      calc (x * x) * (x⁻¹ * x⁻¹) = (x * x⁻¹) * (x * x⁻¹) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ hx0, mul_one]
    calc (((u⁻¹ : (ZMod p)ˣ) : ZMod p))
        = (((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * ((u : ZMod p) * (x⁻¹ * x⁻¹)) := by rw [hmul, mul_one]
      _ = ((((u⁻¹ * u : (ZMod p)ˣ) : ZMod p))) * (x⁻¹ * x⁻¹) := by rw [Units.val_mul, mul_assoc]
      _ = x⁻¹ * x⁻¹ := by rw [inv_mul_cancel, Units.val_one, one_mul]

/-- Prime non-residue reduction: if some `1 <= a <= B` coprime to `p` is a quadratic
non-residue mod `p`, then some prime `q <= B` coprime to `p` is a quadratic non-residue mod `p`. -/
theorem prime_nonresidue_witness {p B a : ℕ} [Fact p.Prime]
    (ha1 : 1 ≤ a) (haB : a ≤ B) (hcop : a.Coprime p)
    (hnonsq : ¬ IsSquare (a : ZMod p)) :
    ∃ q : ℕ, q.Prime ∧ q ≤ B ∧ q.Coprime p ∧ ¬ IsSquare (q : ZMod p) := by
  have hnot_mem : ZMod.unitOfCoprime a hcop ∉ squaresSubgroup p := by
    intro hmem
    have hsq : IsSquare ((ZMod.unitOfCoprime a hcop : (ZMod p)ˣ) : ZMod p) := hmem
    rw [ZMod.coe_unitOfCoprime] at hsq
    exact hnonsq hsq
  obtain ⟨q, hq_prime, hq_le, hq_cop, hq_not⟩ :=
    prime_witness_of_coprime_witness (squaresSubgroup p) ha1 haB hcop hnot_mem
  refine ⟨q, hq_prime, hq_le, hq_cop, ?_⟩
  intro hq_sq
  apply hq_not
  change IsSquare ((ZMod.unitOfCoprime q hq_cop : (ZMod p)ˣ) : ZMod p)
  rwa [ZMod.coe_unitOfCoprime]

/-- Correctness of the `p % 4 = 3` square-root formula `r = a^((p + 1) / 4)`. -/
theorem sqrt_three_mod_four {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    {a : ZMod p} (hsq : IsSquare a) :
    (a ^ ((p + 1) / 4)) ^ 2 = a := by
  have hp_prime : p.Prime := Fact.out
  by_cases ha0 : a = 0
  · subst ha0
    have hpos : 0 < (p + 1) / 4 := by omega
    rw [zero_pow hpos.ne', zero_pow (by norm_num)]
  · rcases hsq with ⟨x, rfl⟩
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at ha0
      exact ha0 rfl
    have hexp : 2 * (2 * ((p + 1) / 4)) = (p - 1) + 2 := by omega
    calc ((x * x) ^ ((p + 1) / 4)) ^ 2
        = (x ^ 2) ^ (2 * ((p + 1) / 4)) := by rw [← sq, ← pow_mul, mul_comm]
      _ = x ^ (2 * (2 * ((p + 1) / 4))) := by rw [← pow_mul]
      _ = x ^ ((p - 1) + 2) := by rw [hexp]
      _ = x ^ (p - 1) * (x * x) := by rw [pow_add, sq]
      _ = x * x := by rw [ZMod.pow_card_sub_one_eq_one hx0, one_mul]

/-- Initialization invariant for Tonelli-Shanks on odd prime `p` with `p - 1 = q * 2^s`. -/
theorem tonelli_shanks_init {p q s : ℕ} [Fact p.Prime]
    (hodd_p : Odd p) (hodd_q : Odd q) (hs : 1 ≤ s) (hdecomp : p - 1 = q * 2 ^ s)
    {a z : ZMod p} (ha0 : a ≠ 0) (hsq_a : IsSquare a) (hnonsq_z : ¬ IsSquare z) :
    let r := a ^ ((q + 1) / 2)
    let t := a ^ q
    let c := z ^ q
    r ^ 2 = a * t ∧ t ^ (2 ^ (s - 1)) = 1 ∧ c ^ (2 ^ (s - 1)) = -1 := by
  have hp_prime : p.Prime := Fact.out
  dsimp only
  have hq_exp : 2 * ((q + 1) / 2) = q + 1 := by
    rcases hodd_q with ⟨k, rfl⟩
    omega
  have hr_eq : (a ^ ((q + 1) / 2)) ^ 2 = a * a ^ q := by
    rw [← pow_mul, mul_comm, hq_exp, pow_succ']
  have hhalf : q * 2 ^ (s - 1) = (p - 1) / 2 := by
    have hs_eq : 2 ^ s = 2 * 2 ^ (s - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hs, pow_succ']
    rw [hdecomp, hs_eq, ← mul_assoc, mul_comm q 2, mul_assoc]
    exact (Nat.mul_div_cancel_left _ (by norm_num)).symm
  have ht_eq : (a ^ q) ^ (2 ^ (s - 1)) = 1 := by
    rw [← pow_mul, hhalf]
    rcases hsq_a with ⟨x, rfl⟩
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at ha0
      exact ha0 rfl
    have h2 : 2 * ((p - 1) / 2) = p - 1 := by
      rcases hodd_p with ⟨k, rfl⟩
      omega
    rw [← sq, ← pow_mul, h2, ZMod.pow_card_sub_one_eq_one hx0]
  have hc_eq : (z ^ q) ^ (2 ^ (s - 1)) = -1 := by
    rw [← pow_mul, hhalf]
    have hp_div : (p - 1) / 2 = p / 2 := by
      rcases hodd_p with ⟨k, rfl⟩
      omega
    rw [hp_div]
    have hz_cast : (((z.val : ℕ) : ℤ) : ZMod p) = z := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hnonsq_val : ¬ IsSquare ((((z.val : ℕ) : ℤ) : ZMod p)) := by
      rwa [hz_cast]
    have hjac : jacobiSym ((z.val : ℕ) : ℤ) p = -1 :=
      (ZMod.nonsquare_iff_jacobiSym_eq_neg_one).mpr hnonsq_val
    rw [← jacobiSym.legendreSym.to_jacobiSym] at hjac
    have heuler := legendreSym.eq_pow p ((z.val : ℕ) : ℤ)
    rw [hjac, Int.cast_neg, Int.cast_one, hz_cast] at heuler
    exact heuler.symm
  exact ⟨hr_eq, ht_eq, hc_eq⟩

/-- Loop step invariant for Tonelli-Shanks: updates `(r, c, t, m)` to `(r', c', t', i)`
with `i < m` while preserving `r'^2 = a * t'`, `c'^(2^(i-1)) = -1`, and `t'^(2^(i-1)) = 1`. -/
theorem tonelli_shanks_step {F : Type*} [CommRing F]
    {a r t c : F} {m i : ℕ}
    (hi_pos : 1 ≤ i) (hi_lt : i < m)
    (h_inv : r ^ 2 = a * t)
    (hc_ord : c ^ (2 ^ (m - 1)) = -1)
    (ht_half : t ^ (2 ^ (i - 1)) = -1) :
    let b := c ^ (2 ^ (m - i - 1))
    let r' := r * b
    let c' := b ^ 2
    let t' := t * c'
    r' ^ 2 = a * t' ∧ c' ^ (2 ^ (i - 1)) = -1 ∧ t' ^ (2 ^ (i - 1)) = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · calc (r * c ^ (2 ^ (m - i - 1))) ^ 2
        = r ^ 2 * (c ^ (2 ^ (m - i - 1))) ^ 2 := by ring
      _ = a * (t * (c ^ (2 ^ (m - i - 1))) ^ 2) := by rw [h_inv]; ring
  · have hexp : 2 ^ (m - i - 1) * 2 * 2 ^ (i - 1) = 2 ^ (m - 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega
    rw [← pow_mul, ← pow_mul, ← mul_assoc, hexp, hc_ord]
  · have hc' : ((c ^ (2 ^ (m - i - 1))) ^ 2) ^ (2 ^ (i - 1)) = -1 := by
      have hexp : 2 ^ (m - i - 1) * 2 * 2 ^ (i - 1) = 2 ^ (m - 1) := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      rw [← pow_mul, ← pow_mul, ← mul_assoc, hexp, hc_ord]
    rw [mul_pow, ht_half, hc', neg_one_mul, neg_neg]

/-- Termination postcondition: when `t = 1`, `r` is a modular square root of `a`. -/
theorem tonelli_shanks_done {F : Type*} [CommRing F] {a r t : F}
    (h_inv : r ^ 2 = a * t) (ht1 : t = 1) : r ^ 2 = a := by
  rw [h_inv, ht1, mul_one]

end DetPrime
