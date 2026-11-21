import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Certified Integer Logarithm and Witness Bounds

Exact Lean 4 counterparts of the pure-integer upper bounds in `src/bounds.rs`:
- `lnUpperScaled` matches `det_prime::ln_upper_scaled`
- `bachBoundFromKm` matches `det_prime::bach_bound_from_km`
- `llsBoundFromKm` matches `det_prime::lls_bound_from_km`

We prove that whenever `2 <= n` and `n < 2^k * (17 + m) / 16` with `m <= 15`:
1. `Real.log n < lnUpperScaled k m / 10^10`
2. Every natural number `a` with `(a : Real) <= 2 * (Real.log n)^2` satisfies
   `a <= bachBoundFromKm k m`.
3. Every natural number `a` with `(a : Real) <= (Real.log n)^2` satisfies
   `a <= llsBoundFromKm k m`.
-/

namespace DetPrime

def ln2ScaledHi : ℕ := 6931471808

def logScale : ℕ := 10000000000

def logScaleSq : ℕ := logScale * logScale

def lnUpperScaled (k m : ℕ) : ℕ :=
  let mc := min m 15
  let fracLeft := 625000000 * (mc + 1)
  let fracRight := ln2ScaledHi - 312500000 * (15 - mc)
  ln2ScaledHi * k + min fracLeft fracRight

def bachBoundFromKm (k m : ℕ) : ℕ :=
  (2 * lnUpperScaled k m * lnUpperScaled k m) / logScaleSq

def llsBoundFromKm (k m : ℕ) : ℕ :=
  (lnUpperScaled k m * lnUpperScaled k m) / logScaleSq

theorem log_two_lt_scaled : Real.log 2 < (ln2ScaledHi : ℝ) / (logScale : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold ln2ScaledHi logScale
  norm_num at h ⊢
  exact h

theorem log_mantissa_le_left (m : ℕ) :
    Real.log (((17 : ℝ) + m) / 16) ≤ ((m : ℝ) + 1) / 16 := by
  have hpos : (0 : ℝ) < ((17 : ℝ) + m) / 16 := by positivity
  have hle := Real.log_le_sub_one_of_pos hpos
  linarith

theorem log_mantissa_le_right (m : ℕ) :
    Real.log (((17 : ℝ) + m) / 16) ≤ Real.log 2 - ((15 : ℝ) - m) / 32 := by
  have hsplit : ((17 : ℝ) + m) / 16 = 2 * (((17 : ℝ) + m) / 32) := by ring
  have hpos : (0 : ℝ) < ((17 : ℝ) + m) / 32 := by positivity
  rw [hsplit, Real.log_mul (by norm_num) hpos.ne']
  have hle := Real.log_le_sub_one_of_pos hpos
  linarith

theorem mantissa_frac_bound (m : ℕ) (hm : m ≤ 15) :
    Real.log (((17 : ℝ) + m) / 16) ≤
      (min (625000000 * (m + 1)) (ln2ScaledHi - 312500000 * (15 - m)) : ℕ) / (logScale : ℝ) := by
  unfold ln2ScaledHi logScale
  by_cases hmin : 625000000 * (m + 1) ≤ 6931471808 - 312500000 * (15 - m)
  · rw [Nat.min_eq_left hmin]
    push_cast
    have hl := log_mantissa_le_left m
    linarith
  · rw [Nat.min_eq_right (le_of_not_ge hmin)]
    have hsub : 312500000 * (15 - m) ≤ 6931471808 := by omega
    rw [Nat.cast_sub hsub]
    push_cast
    rw [Nat.cast_sub hm]
    push_cast
    have hr := log_mantissa_le_right m
    have hlog2 := Real.log_two_lt_d9
    linarith

theorem lnUpperScaled_strict_bound {n k m : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ 15)
    (hupper : (n : ℝ) < (2 : ℝ) ^ k * (((17 : ℝ) + m) / 16)) :
    Real.log n < (lnUpperScaled k m : ℝ) / (logScale : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact Nat.cast_pos.mpr this
  have hrhs_pos : (0 : ℝ) < (2 : ℝ) ^ k * (((17 : ℝ) + m) / 16) := by positivity
  have hlog_lt : Real.log n < Real.log ((2 : ℝ) ^ k * (((17 : ℝ) + m) / 16)) :=
    Real.log_lt_log hn_pos hupper
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog_lt
  have hfrac := mantissa_frac_bound m hm
  have hlog2 := log_two_lt_scaled
  have hk_le : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * ((ln2ScaledHi : ℝ) / (logScale : ℝ)) := by
    exact mul_le_mul_of_nonneg_left (le_of_lt hlog2) (Nat.cast_nonneg k)
  unfold lnUpperScaled
  rw [Nat.min_eq_left hm, Nat.cast_add, Nat.cast_mul]
  unfold ln2ScaledHi logScale at hk_le hfrac ⊢
  linarith

theorem bachBound_sound {n k m a : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ 15)
    (hupper : (n : ℝ) < (2 : ℝ) ^ k * (((17 : ℝ) + m) / 16))
    (ha : (a : ℝ) ≤ 2 * (Real.log n) ^ 2) :
    a ≤ bachBoundFromKm k m := by
  have hln_lt := lnUpperScaled_strict_bound hn hm hupper
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hln_pos : 0 < Real.log n := Real.log_pos hn1
  have hsq_lt : (Real.log n) ^ 2 < ((lnUpperScaled k m : ℝ) / (logScale : ℝ)) ^ 2 :=
    sq_lt_sq' (by linarith) hln_lt
  have ha_lt : (a : ℝ) < 2 * (((lnUpperScaled k m : ℝ) / (logScale : ℝ)) ^ 2) := by
    linarith
  have hscale_pos : (0 : ℝ) < (logScale : ℝ) ^ 2 := by unfold logScale; norm_num
  have hmul_lt : (a : ℝ) * (logScale : ℝ) ^ 2 < 2 * (lnUpperScaled k m : ℝ) ^ 2 := by
    have hdiv : 2 * (((lnUpperScaled k m : ℝ) / (logScale : ℝ)) ^ 2) * (logScale : ℝ) ^ 2 =
        2 * (lnUpperScaled k m : ℝ) ^ 2 := by
      have hne : (logScale : ℝ) ≠ 0 := by unfold logScale; norm_num
      field_simp [hne]
    nlinarith [mul_lt_mul_of_pos_right ha_lt hscale_pos]
  have hnat_lt : a * logScaleSq < 2 * lnUpperScaled k m * lnUpperScaled k m := by
    unfold logScaleSq
    have hcast : ((a * (logScale * logScale) : ℕ) : ℝ) <
        ((2 * lnUpperScaled k m * lnUpperScaled k m : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_lt.mp hcast
  unfold bachBoundFromKm
  exact (Nat.le_div_iff_mul_le (by unfold logScaleSq logScale; norm_num)).mpr (le_of_lt hnat_lt)

theorem llsBound_sound {n k m a : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ 15)
    (hupper : (n : ℝ) < (2 : ℝ) ^ k * (((17 : ℝ) + m) / 16))
    (ha : (a : ℝ) ≤ (Real.log n) ^ 2) :
    a ≤ llsBoundFromKm k m := by
  have hln_lt := lnUpperScaled_strict_bound hn hm hupper
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hln_pos : 0 < Real.log n := Real.log_pos hn1
  have hsq_lt : (Real.log n) ^ 2 < ((lnUpperScaled k m : ℝ) / (logScale : ℝ)) ^ 2 :=
    sq_lt_sq' (by linarith) hln_lt
  have ha_lt : (a : ℝ) < ((lnUpperScaled k m : ℝ) / (logScale : ℝ)) ^ 2 :=
    lt_of_le_of_lt ha hsq_lt
  have hscale_pos : (0 : ℝ) < (logScale : ℝ) ^ 2 := by unfold logScale; norm_num
  have hmul_lt : (a : ℝ) * (logScale : ℝ) ^ 2 < (lnUpperScaled k m : ℝ) ^ 2 := by
    have hne : (logScale : ℝ) ≠ 0 := by unfold logScale; norm_num
    have hdiv : ((lnUpperScaled k m : ℝ) / (logScale : ℝ)) ^ 2 * (logScale : ℝ) ^ 2 =
        (lnUpperScaled k m : ℝ) ^ 2 := by
      field_simp [hne]
    nlinarith [mul_lt_mul_of_pos_right ha_lt hscale_pos]
  have hnat_lt : a * logScaleSq < lnUpperScaled k m * lnUpperScaled k m := by
    unfold logScaleSq
    have hcast : ((a * (logScale * logScale) : ℕ) : ℝ) <
        ((lnUpperScaled k m * lnUpperScaled k m : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_lt.mp hcast
  unfold llsBoundFromKm
  exact (Nat.le_div_iff_mul_le (by unfold logScaleSq logScale; norm_num)).mpr (le_of_lt hnat_lt)

-- Spot-check that Lean's `bachBoundFromKm 255 15` matches Rust's `bach_witness_bound(&(2^256 - 1))`.
theorem bachBound_u256_max : bachBoundFromKm 255 15 = 62973 := by rfl

end DetPrime
