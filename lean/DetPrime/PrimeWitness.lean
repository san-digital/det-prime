import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Prime-Base Witness Reduction, Solovay-Strassen, and Monier-Rabin Soundness

Machine-checked finite-algebra theorems backing `src/primality.rs`:
1. `prime_witness_of_coprime_witness`: For any subgroup `H <= (ZMod n)^x`, if a coprime
   integer `1 <= a <= B` lies outside `H`, then some prime factor `p <= B` of `a` also
   lies outside `H`.
2. `eulerJacobiSubgroup`: The Euler-Jacobi liars `{u | u^((n-1)/2) = J(u | n)}` form a
   subgroup of `(ZMod n)^x` for every integer `n > 1`.
3. `odd_composite_exists_euler_jacobi_witness` (Solovay-Strassen): For every odd composite
   `n > 1`, `eulerJacobiSubgroup n` is a proper subgroup of `(ZMod n)^x`.
4. `strong_liar_mem_euler_jacobi` (Monier-Rabin / Pomerance-Selfridge-Wagstaff): Every
   strong probable prime base coprime to an odd integer `n > 1` lies in `eulerJacobiSubgroup n`.
5. `prime_is_strong_probable_prime`: Every prime `p` passes `IsStrongProbablePrime`
   for all coprime bases (zero false negatives).
-/

namespace DetPrime

open scoped NumberTheorySymbols

theorem unitOfCoprime_mul {n x y : ℕ} (hx : x.Coprime n) (hy : y.Coprime n) :
    ZMod.unitOfCoprime (x * y) (hx.mul_left hy) =
      ZMod.unitOfCoprime x hx * ZMod.unitOfCoprime y hy := by
  ext
  simp [ZMod.coe_unitOfCoprime]

private theorem list_prod_unitOfCoprime_mem {n : ℕ} (H : Subgroup (ZMod n)ˣ) :
    ∀ (L : List ℕ) (hcop : L.prod.Coprime n),
      (∀ p ∈ L, ∀ hp : p.Coprime n, ZMod.unitOfCoprime p hp ∈ H) →
      ZMod.unitOfCoprime L.prod hcop ∈ H
  | [], hcop, _ => by
      have h1 : ZMod.unitOfCoprime [].prod hcop = 1 := by
        ext
        simp [List.prod_nil]
      rw [h1]
      exact H.one_mem
  | p :: ps, hcop, hall => by
      simp only [List.prod_cons] at hcop ⊢
      have hp : p.Coprime n := hcop.coprime_dvd_left (dvd_mul_right p ps.prod)
      have hps : ps.prod.Coprime n := hcop.coprime_dvd_left (dvd_mul_left ps.prod p)
      have hmul : ZMod.unitOfCoprime (p * ps.prod) hcop =
          ZMod.unitOfCoprime p hp * ZMod.unitOfCoprime ps.prod hps := by
        ext; simp [ZMod.coe_unitOfCoprime]
      rw [hmul]
      exact H.mul_mem
        (hall p List.mem_cons_self hp)
        (list_prod_unitOfCoprime_mem H ps hps (fun q hq hqn => hall q (List.mem_cons_of_mem p hq) hqn))

/-- Multiplicative prime-witness reduction: if any coprime integer `1 <= a <= B` lies
outside a subgroup `H <= (ZMod n)^x`, then some prime `p <= B` coprime to `n` lies outside `H`. -/
theorem prime_witness_of_coprime_witness {n B : ℕ} (H : Subgroup (ZMod n)ˣ)
    {a : ℕ} (ha1 : 1 ≤ a) (haB : a ≤ B) (hcop : a.Coprime n)
    (hnot : ZMod.unitOfCoprime a hcop ∉ H) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ∃ hp : p.Coprime n, ZMod.unitOfCoprime p hp ∉ H := by
  by_contra hno
  push Not at hno
  have ha0 : a ≠ 0 := by omega
  have hprod_eq : a.primeFactorsList.prod = a := Nat.prod_primeFactorsList ha0
  have hcopL : a.primeFactorsList.prod.Coprime n := by rwa [hprod_eq]
  have hall : ∀ p ∈ a.primeFactorsList, ∀ hp : p.Coprime n, ZMod.unitOfCoprime p hp ∈ H := by
    intro p hp_mem hp_cop
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactorsList hp_mem
    have hp_dvd : p ∣ a := Nat.dvd_of_mem_primeFactorsList hp_mem
    have hp_le : p ≤ B := le_trans (Nat.le_of_dvd (by omega) hp_dvd) haB
    exact hno p hp_prime hp_le hp_cop
  have hmem := list_prod_unitOfCoprime_mem H a.primeFactorsList hcopL hall
  have heq : ZMod.unitOfCoprime a.primeFactorsList.prod hcopL = ZMod.unitOfCoprime a hcop := by
    ext; simp [ZMod.coe_unitOfCoprime, hprod_eq]
  rw [heq] at hmem
  exact hnot hmem

/-- The Jacobi symbol on `(ZMod n)^x` is multiplicative for `1 < n`. -/
theorem jacobiSym_unit_mul {n : ℕ} [Fact (1 < n)] (u v : (ZMod n)ˣ) :
    J((((u * v : (ZMod n)ˣ) : ZMod n).val : ℤ) | n) =
      J(((u : ZMod n).val : ℤ) | n) * J(((v : ZMod n).val : ℤ) | n) := by
  have hval : ((u * v : (ZMod n)ˣ) : ZMod n).val = ((u : ZMod n).val * (v : ZMod n).val) % n := by
    rw [Units.val_mul, ZMod.val_mul]
  rw [hval, Int.natCast_emod, ← jacobiSym.mod_left, Int.natCast_mul, jacobiSym.mul_left]

/-- The Euler-Jacobi liar subgroup `{u in (ZMod n)^x | u^((n - 1)/2) = J(u | n)}` for `1 < n`. -/
def eulerJacobiSubgroup (n : ℕ) [Fact (1 < n)] : Subgroup (ZMod n)ˣ where
  carrier := { u : (ZMod n)ˣ |
    ((u : ZMod n) ^ ((n - 1) / 2)) = (J(((u : ZMod n).val : ℤ) | n) : ZMod n) }
  one_mem' := by
    change ((1 : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2) =
      (J((((1 : (ZMod n)ˣ) : ZMod n).val : ℤ) | n) : ZMod n)
    rw [Units.val_one, one_pow, ZMod.val_one n]
    simp
  mul_mem' {u v} hu hv := by
    change ((u : ZMod n) ^ ((n - 1) / 2)) = (J(((u : ZMod n).val : ℤ) | n) : ZMod n) at hu
    change ((v : ZMod n) ^ ((n - 1) / 2)) = (J(((v : ZMod n).val : ℤ) | n) : ZMod n) at hv
    change (((u * v : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2)) =
      (J((((u * v : (ZMod n)ˣ) : ZMod n).val : ℤ) | n) : ZMod n)
    rw [jacobiSym_unit_mul, Int.cast_mul, Units.val_mul, mul_pow, hu, hv]
  inv_mem' {u} hu := by
    change ((u : ZMod n) ^ ((n - 1) / 2)) = (J(((u : ZMod n).val : ℤ) | n) : ZMod n) at hu
    change (((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2)) =
      (J((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℤ) | n) : ZMod n)
    have hmulJ := jacobiSym_unit_mul u u⁻¹
    rw [mul_inv_cancel, Units.val_one, ZMod.val_one n, Nat.cast_one, jacobiSym.one_left] at hmulJ
    have hcastJ : (J(((u : ZMod n).val : ℤ) | n) : ZMod n) *
        (J((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℤ) | n) : ZMod n) = 1 := by
      rw [← Int.cast_mul, ← hmulJ, Int.cast_one]
    have hpow_mul : ((u : ZMod n) ^ ((n - 1) / 2)) *
        (((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2)) = 1 := by
      rw [← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
    rw [hu] at hpow_mul
    calc (((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2))
        = (((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2)) *
            ((J(((u : ZMod n).val : ℤ) | n) : ZMod n) *
              (J((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℤ) | n) : ZMod n)) := by
          rw [hcastJ, mul_one]
      _ = ((J(((u : ZMod n).val : ℤ) | n) : ZMod n) *
            (((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2))) *
            (J((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℤ) | n) : ZMod n) := by ring
      _ = (J((((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ℤ) | n) : ZMod n) := by
          rw [hpow_mul, one_mul]

/-- Every element of `eulerJacobiSubgroup n` for odd `n > 1` is a Fermat liar (`u^(n-1) = 1`). -/
theorem fermat_eq_one_of_mem_eulerJacobi {n : ℕ} [Fact (1 < n)] (hodd : Odd n)
    {u : (ZMod n)ˣ} (hu : u ∈ eulerJacobiSubgroup n) :
    (u : ZMod n) ^ (n - 1) = 1 := by
  have hn_pos : 1 < n := Fact.out
  have h2 : 2 * ((n - 1) / 2) = n - 1 := by
    rcases hodd with ⟨k, rfl⟩
    omega
  have hcop : Int.gcd ((u : ZMod n).val : ℤ) n = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ZMod.val_coe_unit_coprime u
  have hsq : J(((u : ZMod n).val : ℤ) | n) ^ 2 = 1 := jacobiSym.sq_one hcop
  have hpow : (u : ZMod n) ^ (n - 1) = ((u : ZMod n) ^ ((n - 1) / 2)) ^ 2 := by
    rw [← pow_mul, mul_comm, h2]
  rw [hpow, hu, ← Int.cast_pow, hsq, Int.cast_one]

private theorem one_add_sq_zero_pow {R : Type*} [CommRing R] {y : R} (hy : y * y = 0) :
    ∀ k : ℕ, (1 + y) ^ k = 1 + (k : R) * y
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ, one_add_sq_zero_pow hy k]
      push_cast
      linear_combination (k : R) * hy

private theorem squarefree_mul_witness {p m : ℕ} [Fact (1 < p * m)]
    (hp_prime : p.Prime) (hm1 : 1 < m) (hcop_pm : p.Coprime m)
    (hp_odd : Odd p) (hm_odd : Odd m) :
    ∃ u : (ZMod (p * m))ˣ, u ∉ eulerJacobiSubgroup (p * m) := by
  have hp_ne2 : p ≠ 2 := by
    intro hp2
    rcases hp_odd with ⟨k, hk⟩
    omega
  have _ : Fact p.Prime := ⟨hp_prime⟩
  have _ : NeZero p := ⟨hp_prime.ne_zero⟩
  have _ : NeZero m := ⟨by omega⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp_ne2
  obtain ⟨z0, hz0⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
  have hz0_ne : z0 ≠ 0 := by
    rintro rfl
    exact hz0 IsSquare.zero
  let crt := ZMod.chineseRemainder hcop_pm
  let x_val : ZMod (p * m) := crt.symm (z0, 1)
  let x_inv : ZMod (p * m) := crt.symm (z0⁻¹, 1)
  have hmul1 : x_val * x_inv = 1 := by
    dsimp [x_val, x_inv]
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel₀ hz0_ne, mul_one]
    exact map_one crt.symm
  have hmul2 : x_inv * x_val = 1 := (mul_comm x_inv x_val).trans hmul1
  let u : (ZMod (p * m))ˣ := ⟨x_val, x_inv, hmul1, hmul2⟩
  refine ⟨u, ?_⟩
  intro hu_mem
  have hpair : crt (u : ZMod (p * m)) = (z0, 1) := crt.apply_symm_apply (z0, 1)
  have hcast_p : ZMod.castHom (dvd_mul_right p m) (ZMod p) (u : ZMod (p * m)) = z0 := by
    have hp_fst := congr_arg Prod.fst hpair
    simpa [crt, ZMod.chineseRemainder] using hp_fst
  have hcast_m : ZMod.castHom (dvd_mul_left m p) (ZMod m) (u : ZMod (p * m)) = 1 := by
    have hm_snd := congr_arg Prod.snd hpair
    simpa [crt, ZMod.chineseRemainder] using hm_snd
  have hval_cast_p : (((u : ZMod (p * m)).val : ℤ) : ZMod p) = z0 := by
    rw [Int.cast_natCast, ← ZMod.cast_eq_val]
    simpa using hcast_p
  have hnonsq_u : ¬ IsSquare ((((u : ZMod (p * m)).val : ℤ) : ZMod p)) := by
    rwa [hval_cast_p]
  have hJp : J(((u : ZMod (p * m)).val : ℤ) | p) = -1 :=
    (ZMod.nonsquare_iff_jacobiSym_eq_neg_one).mpr hnonsq_u
  have hval_cast_m : (((u : ZMod (p * m)).val : ℕ) : ZMod m) = (1 : ZMod m) := by
    have hc : ZMod.castHom (dvd_mul_left m p) (ZMod m)
        (((u : ZMod (p * m)).val : ℕ) : ZMod (p * m)) = (1 : ZMod m) := by
      simpa [ZMod.natCast_zmod_val] using hcast_m
    simpa using hc
  have hmod_m : ((u : ZMod (p * m)).val : ℤ) % (m : ℤ) = (1 : ℤ) % (m : ℤ) := by
    have hnat : (u : ZMod (p * m)).val % m = 1 % m := by
      rw [← ZMod.val_natCast, ← ZMod.val_natCast m 1, hval_cast_m, Nat.cast_one]
    exact_mod_cast hnat
  have hJm : J(((u : ZMod (p * m)).val : ℤ) | m) = 1 := by
    rw [jacobiSym.mod_left' hmod_m, jacobiSym.one_left]
  have hJn : J(((u : ZMod (p * m)).val : ℤ) | p * m) = -1 := by
    rw [jacobiSym.mul_right' _ hp_prime.ne_zero (by omega), hJp, hJm, neg_one_mul]
  have hpow_eq : (u : ZMod (p * m)) ^ ((p * m - 1) / 2) = -1 := by
    have hm_ej : (u : ZMod (p * m)) ^ ((p * m - 1) / 2) =
        (J(((u : ZMod (p * m)).val : ℤ) | p * m) : ZMod (p * m)) := hu_mem
    rw [hm_ej, hJn, Int.cast_neg, Int.cast_one]
  let phi_m := ZMod.castHom (dvd_mul_left m p) (ZMod m)
  have hphi := congr_arg phi_m hpow_eq
  rw [map_pow, hcast_m, one_pow, map_neg, map_one] at hphi
  have h2zero : ((2 : ℕ) : ZMod m) = 0 := by
    have : (1 : ZMod m) + 1 = 0 := by linear_combination hphi
    simpa [one_add_one_eq_two] using this
  have hm_dvd_2 : m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 m).mp h2zero
  have hm_le_2 : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm_dvd_2
  rcases hm_odd with ⟨k, hk⟩
  omega

/-- Solovay-Strassen properness: for every odd composite `n > 1`, there exists a unit
in `(ZMod n)^x` outside `eulerJacobiSubgroup n`. -/
theorem odd_composite_exists_euler_jacobi_witness {n : ℕ} [Fact (1 < n)]
    (hodd : Odd n) (hcomp : ¬ n.Prime) :
    ∃ u : (ZMod n)ˣ, u ∉ eulerJacobiSubgroup n := by
  have hn1 : 1 < n := Fact.out
  have _ : NeZero n := ⟨by omega⟩
  by_cases hsqf : Squarefree n
  · obtain ⟨p, hp_prime, m, hpm⟩ : ∃ p, p.Prime ∧ ∃ m, p * m = n :=
      ⟨n.minFac, Nat.minFac_prime (by omega), n / n.minFac, Nat.mul_div_cancel' (Nat.minFac_dvd n)⟩
    subst hpm
    have hm1 : 1 < m := by
      rcases eq_or_ne m 0 with rfl | hm0
      · simp at hn1
      · rcases eq_or_ne m 1 with rfl | hm_ne1
        · rw [mul_one] at hcomp
          exact absurd hp_prime hcomp
        · omega
    have hcop_pm : p.Coprime m := Nat.coprime_of_squarefree_mul hsqf
    have hp_odd : Odd p := (Nat.odd_mul.mp hodd).1
    have hm_odd : Odd m := (Nat.odd_mul.mp hodd).2
    exact squarefree_mul_witness hp_prime hm1 hcop_pm hp_odd hm_odd
  · rw [Nat.squarefree_iff_prime_squarefree] at hsqf
    push Not at hsqf
    obtain ⟨p, hp_prime, k, hnk⟩ := hsqf
    let m : ℕ := p * k
    have hpm : p * m = n := by
      dsimp [m]
      linarith
    have hp_pos : 0 < p := hp_prime.pos
    have hm_pos : 0 < m := by
      by_contra hm0
      have hm_z : m = 0 := by omega
      rw [hm_z, mul_zero] at hpm
      omega
    have hm_lt : m < n := by
      have hp2 : 2 ≤ p := hp_prime.two_le
      have h2m : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp2
      omega
    have hn_dvd_mm : n ∣ m * m := by
      refine ⟨k, ?_⟩
      dsimp [m]
      rw [hnk]
      ring
    let y : ZMod n := (m : ZMod n)
    have hy_ne : y ≠ 0 := by
      intro hy0
      have hndvd : n ∣ m := (ZMod.natCast_eq_zero_iff m n).mp hy0
      have := Nat.le_of_dvd hm_pos hndvd
      omega
    have hy_sq : y * y = 0 := by
      change ((m : ZMod n) * (m : ZMod n)) = 0
      rw [← Nat.cast_mul]
      exact (ZMod.natCast_eq_zero_iff (m * m) n).mpr hn_dvd_mm
    let u : (ZMod n)ˣ :=
      ⟨1 + y, 1 - y, by linear_combination -hy_sq, by linear_combination -hy_sq⟩
    refine ⟨u, ?_⟩
    intro hu_mem
    have hfermat := fermat_eq_one_of_mem_eulerJacobi hodd hu_mem
    have hpow := one_add_sq_zero_pow hy_sq (n - 1)
    change (1 + y) ^ (n - 1) = 1 at hfermat
    rw [hpow] at hfermat
    have hn1_cast : ((n - 1 : ℕ) : ZMod n) = -1 := by
      have : ((n - 1 : ℕ) : ZMod n) + 1 = ((n - 1 + 1 : ℕ) : ZMod n) := by push_cast; ring
      have hn_eq : n - 1 + 1 = n := by omega
      rw [hn_eq, ZMod.natCast_self] at this
      linear_combination this
    rw [hn1_cast] at hfermat
    have : y = 0 := by linear_combination -hfermat
    exact hy_ne this

/-- Strong probable prime predicate matching `strong_probable_prime_mont` in `src/primality.rs`. -/
def IsStrongProbablePrime (n d s a : ℕ) : Prop :=
  (a : ZMod n) ^ d = 1 ∨ ∃ r < s, (a : ZMod n) ^ (d * 2 ^ r) = -1

/-- Every prime `p` passes `IsStrongProbablePrime` for every coprime base `a`. -/
theorem prime_is_strong_probable_prime {p d s a : ℕ}
    (hp : p.Prime) (hdecomp : p - 1 = d * 2 ^ s) (hcop : a.Coprime p) :
    IsStrongProbablePrime p d s a := by
  have _ : Fact p.Prime := ⟨hp⟩
  have ha_ne : (a : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp h0
    have h1 : p ∣ a.gcd p := Nat.dvd_gcd hdvd (dvd_refl p)
    rw [hcop] at h1
    exact absurd (Nat.le_of_dvd one_pos h1) (not_le_of_gt hp.one_lt)
  have hfermat : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha_ne
  rw [hdecomp] at hfermat
  suffices ∀ k : ℕ, (a : ZMod p) ^ (d * 2 ^ k) = 1 →
      (a : ZMod p) ^ d = 1 ∨ ∃ r < k, (a : ZMod p) ^ (d * 2 ^ r) = -1 from
    this s hfermat
  intro k
  induction k with
  | zero =>
      intro h0
      left
      simpa using h0
  | succ k ih =>
      intro hsucc
      have hsq : ((a : ZMod p) ^ (d * 2 ^ k)) ^ 2 = 1 := by
        rw [← pow_mul, mul_assoc, ← pow_succ]
        exact hsucc
      rcases sq_eq_one_iff.mp hsq with hpos | hneg
      · rcases ih hpos with hd | ⟨r, hr, hr_eq⟩
        · exact Or.inl hd
        · exact Or.inr ⟨r, Nat.lt_succ_of_lt hr, hr_eq⟩
      · exact Or.inr ⟨k, Nat.lt_succ_self k, hneg⟩

private theorem neg_one_pow_div_two_pow_list (r : ℕ) :
    ∀ (L : List ℕ),
      (∀ m ∈ L, 1 ≤ m ∧ 2 ^ (r + 1) ∣ m - 1) →
      1 ≤ L.prod ∧ 2 ^ (r + 1) ∣ L.prod - 1 ∧
        (L.map (fun m => (-1 : ℤ) ^ ((m - 1) / 2 ^ (r + 1)))).prod =
          (-1 : ℤ) ^ ((L.prod - 1) / 2 ^ (r + 1))
  | [], _ => by simp
  | m :: ms, hall => by
      obtain ⟨hm1, hm_dvd⟩ := hall m List.mem_cons_self
      obtain ⟨hms1, hms_dvd, ih_eq⟩ :=
        neg_one_pow_div_two_pow_list r ms (fun x hx => hall x (List.mem_cons_of_mem m hx))
      rcases hm_dvd with ⟨km, hkm⟩
      rcases hms_dvd with ⟨kms, hkms⟩
      have hm_eq : m = 1 + 2 ^ (r + 1) * km := by omega
      have hms_eq : ms.prod = 1 + 2 ^ (r + 1) * kms := by omega
      have hprod_ge : 1 ≤ (m :: ms).prod := by
        simp only [List.prod_cons]
        exact Nat.mul_le_mul hm1 hms1
      have hprod_sub : m * ms.prod - 1 =
          2 ^ (r + 1) * (km + kms + 2 ^ (r + 1) * km * kms) := by
        rw [hm_eq, hms_eq]
        have hexp : (1 + 2 ^ (r + 1) * km) * (1 + 2 ^ (r + 1) * kms) =
            1 + 2 ^ (r + 1) * (km + kms + 2 ^ (r + 1) * km * kms) := by ring
        omega
      have hpow_pos : 0 < 2 ^ (r + 1) := by positivity
      have hdiv_m : (m - 1) / 2 ^ (r + 1) = km := by
        rw [hkm, Nat.mul_div_cancel_left _ hpow_pos]
      have hdiv_ms : (ms.prod - 1) / 2 ^ (r + 1) = kms := by
        rw [hkms, Nat.mul_div_cancel_left _ hpow_pos]
      have hdiv_prod : (m * ms.prod - 1) / 2 ^ (r + 1) =
          km + kms + 2 ^ (r + 1) * km * kms := by
        rw [hprod_sub, Nat.mul_div_cancel_left _ hpow_pos]
      refine ⟨hprod_ge, ⟨km + kms + 2 ^ (r + 1) * km * kms, by simpa [List.prod_cons] using hprod_sub⟩, ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [ih_eq, hdiv_m, hdiv_ms, hdiv_prod, pow_add, pow_add]
      have heven : Even (2 ^ (r + 1) * km * kms) := by
        refine ⟨2 ^ r * km * kms, ?_⟩
        rw [pow_succ']
        ring
      rw [Even.neg_one_pow heven, mul_one]

/-- Monier-Rabin / Pomerance-Selfridge-Wagstaff inclusion: every strong probable prime base
coprime to an odd integer `n > 1` belongs to `eulerJacobiSubgroup n`. -/
theorem strong_liar_mem_euler_jacobi {n d s a : ℕ} [Fact (1 < n)]
    (hodd_n : Odd n) (hodd_d : Odd d) (hdecomp : n - 1 = d * 2 ^ s)
    (hcop : a.Coprime n) (hspp : IsStrongProbablePrime n d s a) :
    ZMod.unitOfCoprime a hcop ∈ eulerJacobiSubgroup n := by
  have hn1 : 1 < n := Fact.out
  have hs_pos : 1 ≤ s := by
    by_contra hs0
    have hs_z : s = 0 := by omega
    rw [hs_z, pow_zero, mul_one] at hdecomp
    rcases hodd_n with ⟨kn, hkn⟩
    rcases hodd_d with ⟨kd, hkd⟩
    omega
  have hhalf : (n - 1) / 2 = d * 2 ^ (s - 1) := by
    have hs_eq : 2 ^ s = 2 * 2 ^ (s - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hs_pos, pow_succ']
    rw [hdecomp, hs_eq, ← mul_assoc, mul_comm d 2, mul_assoc]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  let u := ZMod.unitOfCoprime a hcop
  have hu_coe : (u : ZMod n) = (a : ZMod n) := ZMod.coe_unitOfCoprime a hcop
  have ha_jac : J(((a : ZMod n).val : ℤ) | n) = J((a : ℤ) | n) := by
    rw [ZMod.val_natCast, Int.natCast_emod, ← jacobiSym.mod_left]
  change (u : ZMod n) ^ ((n - 1) / 2) = (J(((u : ZMod n).val : ℤ) | n) : ZMod n)
  rw [hu_coe, ha_jac, hhalf]
  have hcop_int : Int.gcd (a : ℤ) n = 1 := by
    rwa [Int.gcd_natCast_natCast]
  rcases hspp with hd_one | ⟨r, hr_lt, hr_neg⟩
  · -- Case 1: a^d = 1 in ZMod n.
    have hlhs : (a : ZMod n) ^ (d * 2 ^ (s - 1)) = 1 := by
      rw [pow_mul, hd_one, one_pow]
    have hmod_n : ((a : ℤ) ^ d) % (n : ℤ) = (1 : ℤ) % (n : ℤ) := by
      have hnat_cast : (((a ^ d : ℕ) : ZMod n)) = (1 : ZMod n) := by
        simpa using hd_one
      have hnat_mod : (a ^ d) % n = 1 % n := by
        rw [← ZMod.val_natCast, ← ZMod.val_natCast n 1, hnat_cast, Nat.cast_one]
      simpa [Int.natCast_pow] using congr_arg (Nat.cast (R := ℤ)) hnat_mod
    have hJpow : J((a : ℤ) | n) ^ d = 1 := by
      rw [← jacobiSym.pow_left, jacobiSym.mod_left' hmod_n, jacobiSym.one_left]
    have hJone : J((a : ℤ) | n) = 1 := by
      rcases jacobiSym.eq_one_or_neg_one hcop_int with h1 | hneg1
      · exact h1
      · exfalso
        rw [hneg1, Odd.neg_one_pow hodd_d] at hJpow
        norm_num at hJpow
    rw [hlhs, hJone, Int.cast_one]
  · -- Case 2: a^(d * 2^r) = -1 in ZMod n for some r < s.
    have hr_le : r ≤ s - 1 := by omega
    have hlhs : (a : ZMod n) ^ (d * 2 ^ (s - 1)) = (-1 : ZMod n) ^ (2 ^ (s - 1 - r)) := by
      have hexp : d * 2 ^ (s - 1) = (d * 2 ^ r) * 2 ^ (s - 1 - r) := by
        rw [mul_assoc, ← pow_add, show r + (s - 1 - r) = s - 1 by omega]
      rw [hexp, pow_mul, hr_neg]
    have hp_prop : ∀ p (hp_mem : p ∈ n.primeFactorsList),
        (1 ≤ p ∧ 2 ^ (r + 1) ∣ p - 1) ∧
          @legendreSym p ⟨Nat.prime_of_mem_primeFactorsList hp_mem⟩ (a : ℤ) =
            (-1 : ℤ) ^ ((p - 1) / 2 ^ (r + 1)) := by
      intro p hp_mem
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactorsList hp_mem
      have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp_mem
      have _ : Fact p.Prime := ⟨hp_prime⟩
      have hp_odd : Odd p := by
        rcases hp_dvd with ⟨q, hq⟩
        rw [hq] at hodd_n
        exact (Nat.odd_mul.mp hodd_n).1
      have hp_ge3 : 3 ≤ p := by
        rcases hp_odd with ⟨k, hk⟩
        have := hp_prime.two_le
        omega
      let phi := ZMod.castHom hp_dvd (ZMod p)
      have hmod_p : (a : ZMod p) ^ (d * 2 ^ r) = -1 := by
        have h := congr_arg phi hr_neg
        simpa [map_pow, map_neg, map_one] using h
      set x : ZMod p := (a : ZMod p) ^ d
      have hx_r : x ^ (2 ^ r) = -1 := by
        dsimp [x]
        rw [← pow_mul]
        exact hmod_p
      have hx_r1 : x ^ (2 ^ (r + 1)) = 1 := by
        rw [pow_succ, pow_mul, hx_r, neg_one_sq]
      have ha_ne0 : (a : ZMod p) ≠ 0 := by
        intro ha0
        have hd_pos : 0 < d * 2 ^ r := by
          rcases hodd_d with ⟨kd, hkd⟩
          exact mul_pos (by omega) (by positivity)
        rw [ha0, zero_pow hd_pos.ne'] at hmod_p
        have h10 : (1 : ZMod p) = 0 := by linear_combination hmod_p
        exact one_ne_zero h10
      have hx_fermat : x ^ (p - 1) = 1 := by
        dsimp [x]
        rw [← pow_mul, mul_comm, pow_mul, ZMod.pow_card_sub_one_eq_one ha_ne0, one_pow]
      have hord_dvd_2r1 : orderOf x ∣ 2 ^ (r + 1) := orderOf_dvd_of_pow_eq_one hx_r1
      obtain ⟨j, hj_le, hord_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord_dvd_2r1
      have hj_eq : j = r + 1 := by
        by_contra hj_ne
        have hj_le_r : j ≤ r := by omega
        have hpow_dvd : 2 ^ j ∣ 2 ^ r := Nat.pow_dvd_pow 2 hj_le_r
        rw [← hord_eq] at hpow_dvd
        rcases hpow_dvd with ⟨c, hc⟩
        have hx_one : x ^ (2 ^ r) = 1 := by
          rw [hc, pow_mul, pow_orderOf_eq_one, one_pow]
        rw [hx_r] at hx_one
        have h2z : ((2 : ℕ) : ZMod p) = 0 := by
          have : (1 : ZMod p) + 1 = 0 := by linear_combination hx_one.symm
          simpa [one_add_one_eq_two] using this
        have hp_dvd_2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2z
        have := Nat.le_of_dvd (by norm_num) hp_dvd_2
        omega
      rw [hj_eq] at hord_eq
      have h2r1_dvd : 2 ^ (r + 1) ∣ p - 1 := by
        rw [← hord_eq]
        exact orderOf_dvd_of_pow_eq_one hx_fermat
      set k := (p - 1) / 2 ^ (r + 1)
      have hpk : p - 1 = 2 ^ (r + 1) * k := (Nat.mul_div_cancel' h2r1_dvd).symm
      have hp_half : p / 2 = 2 ^ r * k := by
        have hp_eq : p = 1 + 2 * (2 ^ r * k) := by
          have : 2 ^ (r + 1) * k = 2 * (2 ^ r * k) := by rw [pow_succ']; ring
          omega
        omega
      have heuler : ((legendreSym p (a : ℤ) : ℤ) : ZMod p) = (a : ZMod p) ^ (2 ^ r * k) := by
        have h := legendreSym.eq_pow p (a : ℤ)
        simpa [hp_half] using h
      have heuler_d : ((legendreSym p (a : ℤ) : ℤ) : ZMod p) ^ d = (-1 : ZMod p) ^ k := by
        rw [heuler, ← pow_mul, show 2 ^ r * k * d = (d * 2 ^ r) * k by ring, pow_mul, hmod_p]
      have hcop_pa : Int.gcd (a : ℤ) p = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact hcop.coprime_dvd_right hp_dvd
      have hleg_pm1 : legendreSym p (a : ℤ) = 1 ∨ legendreSym p (a : ℤ) = -1 := by
        rw [jacobiSym.legendreSym.to_jacobiSym]
        exact jacobiSym.eq_one_or_neg_one hcop_pa
      have hleg_pow_d : ((legendreSym p (a : ℤ) : ℤ) : ZMod p) ^ d =
          ((legendreSym p (a : ℤ) : ℤ) : ZMod p) := by
        rcases hleg_pm1 with h1 | hm1
        · rw [h1, Int.cast_one, one_pow]
        · rw [hm1, Int.cast_neg, Int.cast_one, Odd.neg_one_pow hodd_d]
      rw [hleg_pow_d] at heuler_d
      have h1_ne_neg1 : (1 : ZMod p) ≠ -1 := by
        intro h1m1
        have h2z : ((2 : ℕ) : ZMod p) = 0 := by
          have : (1 : ZMod p) + 1 = 0 := by linear_combination h1m1
          simpa [one_add_one_eq_two] using this
        have hp_dvd_2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2z
        have := Nat.le_of_dvd (by norm_num) hp_dvd_2
        omega
      have hleg_eq : legendreSym p (a : ℤ) = (-1 : ℤ) ^ k := by
        rcases Nat.even_or_odd k with hk_even | hk_odd
        · rw [Even.neg_one_pow hk_even]
          rw [Even.neg_one_pow hk_even] at heuler_d
          rcases hleg_pm1 with hl1 | hlm1
          · exact hl1
          · rw [hlm1, Int.cast_neg, Int.cast_one] at heuler_d
            exact absurd heuler_d.symm h1_ne_neg1
        · rw [Odd.neg_one_pow hk_odd]
          rw [Odd.neg_one_pow hk_odd] at heuler_d
          rcases hleg_pm1 with hl1 | hlm1
          · rw [hl1, Int.cast_one] at heuler_d
            exact absurd heuler_d h1_ne_neg1
          · exact hlm1
      exact ⟨⟨by omega, h2r1_dvd⟩, hleg_eq⟩
    have hn0 : n ≠ 0 := by omega
    have hlist := neg_one_pow_div_two_pow_list r n.primeFactorsList (fun p hp => (hp_prop p hp).1)
    have hprod_n : n.primeFactorsList.prod = n := Nat.prod_primeFactorsList hn0
    have hjac_prod : J((a : ℤ) | n) = (-1 : ℤ) ^ ((n - 1) / 2 ^ (r + 1)) := by
      unfold jacobiSym
      have hpmap_eq :
          (n.primeFactorsList.pmap (fun p pp => @legendreSym p ⟨pp⟩ (a : ℤ))
            (fun _ pf => Nat.prime_of_mem_primeFactorsList pf)) =
          n.primeFactorsList.map (fun p => (-1 : ℤ) ^ ((p - 1) / 2 ^ (r + 1))) := by
        rw [List.pmap_eq_map_attach]
        conv_rhs => rw [← List.attach_map_subtype_val n.primeFactorsList, List.map_map]
        refine List.map_congr_left ?_
        rintro ⟨p, hp_mem⟩ _
        exact (hp_prop p hp_mem).2
      rw [hpmap_eq, hlist.2.2, hprod_n]
    have hdiv_n : (n - 1) / 2 ^ (r + 1) = d * 2 ^ (s - 1 - r) := by
      have hs_split : d * 2 ^ s = 2 ^ (r + 1) * (d * 2 ^ (s - 1 - r)) := by
        have : s = (r + 1) + (s - 1 - r) := by omega
        conv_lhs => rw [this, pow_add]
        ring
      rw [hdecomp, hs_split, Nat.mul_div_cancel_left _ (by positivity)]
    rw [hlhs, hjac_prod, hdiv_n]
    rcases eq_or_lt_of_le hr_le with rfl | hr_lt_s1
    · simp only [Nat.sub_self, pow_zero, mul_one, pow_one]
      rw [Odd.neg_one_pow hodd_d, Int.cast_neg, Int.cast_one]
    · have hexp_pos : 1 ≤ s - 1 - r := by omega
      have heven_lhs : Even (2 ^ (s - 1 - r)) := by
        refine ⟨2 ^ (s - 1 - r - 1), ?_⟩
        conv_lhs => rw [← Nat.sub_add_cancel hexp_pos, pow_succ']
        ring
      have heven_rhs : Even (d * 2 ^ (s - 1 - r)) := heven_lhs.mul_left d
      rw [Even.neg_one_pow heven_lhs, Even.neg_one_pow heven_rhs, Int.cast_one]

end DetPrime
