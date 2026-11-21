import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import DetPrime.LogBounds
import DetPrime.PrimeWitness
import DetPrime.TonelliShanks

/-!
# End-to-End Analytic-to-Algorithmic Soundness Bridge

Connects the analytic hypotheses of Alpoge's `Statements.lean` (`DirichletLNonvanishingRightOfHalf`
and `RiemannZetaZerosOnLine`) and published explicit analytic number theory bounds:
- Bach (1990), Mathematics of Computation 55(191), Theorem 2
- Lamzouri, Li, and Soundararajan (2015), Mathematics of Computation 84(295), Corollaries 1.1 & 1.2
- Carneiro, Milinovich, and Soundararajan (2019), Commentarii Mathematici Helvetici 94(3), Theorem 5

to the exact integer logarithm enclosures (`DetPrime.LogBounds`), subgroup and prime-base
reductions (`DetPrime.PrimeWitness`), and Tonelli-Shanks invariants (`DetPrime.TonelliShanks`)
implemented in the Rust library.
-/

namespace DetPrime

/-- Non-trivial zeros of the Riemann zeta function lie on the critical line `Re(s) = 1/2`.
Matches `RiemannZetaZerosOnLine` in `Statements.lean` verbatim. -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- Non-vanishing of Dirichlet L-functions in the open half-plane `Re(s) > 1/2`
(away from the simple pole at `s = 1` for trivial characters).
Matches `DirichletLNonvanishingRightOfHalf` in `Statements.lean` verbatim. -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Bach (1990, Theorem 2): Under `DirichletLNonvanishingRightOfHalf`, for every integer `n >= 2`
and every proper subgroup `H` of `(ZMod n)^x`, there is a positive integer `a <= 2 * (ln n)^2`
coprime to `n` whose residue class lies outside `H`. -/
def BachSubgroupBound : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ (n : ℕ), 2 ≤ n → ∀ (H : Subgroup (ZMod n)ˣ), (∃ u : (ZMod n)ˣ, u ∉ H) →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) ≤ 2 * (Real.log n) ^ 2 ∧
        ∃ ha : a.Coprime n, ZMod.unitOfCoprime a ha ∉ H

/-- Lamzouri, Li, and Soundararajan (2015, Corollary 1.1): Under `DirichletLNonvanishingRightOfHalf`,
for every prime `p >= 5`, there exists a quadratic non-residue `1 <= a <= (ln p)^2` coprime to `p`. -/
def LLSNonresidueBound : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) ≤ (Real.log p) ^ 2 ∧ a.Coprime p ∧ ¬ IsSquare (a : ZMod p)

/-- Lamzouri, Li, and Soundararajan (2015, Corollary 1.2): Under `DirichletLNonvanishingRightOfHalf`,
for every modulus `q > 3` and coprime residue `a`, the least prime `p == a (mod q)` satisfies
`p <= (phi(q) * ln q)^2`. -/
def LLSProgressionBound : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ (q a : ℕ), 3 < q → a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p % q = a % q ∧
        (p : ℝ) ≤ (Nat.totient q : ℝ) ^ 2 * (Real.log q) ^ 2

/-- Carneiro, Milinovich, and Soundararajan (2019, Theorem 5): Under `RiemannZetaZerosOnLine`,
for every `x >= 4`, there is a prime `p >= x` within `(22/25) * sqrt(x) * ln(x)`. -/
def CMSPrimeGapBound : Prop :=
  RiemannZetaZerosOnLine →
    ∀ (x : ℕ), 4 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x ≤ p ∧
        (p : ℝ) - (x : ℝ) ≤ (22 / 25 : ℝ) * Real.sqrt x * Real.log x

/-- End-to-end composite witness theorem: every odd composite `n > 1` bounded by
`2^k * (17 + m) / 16` (`m <= 15`) possesses a PRIME strong-pseudoprime witness
`p <= bachBoundFromKm k m` coprime to `n`. -/
theorem miller_bach_composite_has_prime_witness
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hBach : BachSubgroupBound)
    {n d s k m : ℕ} [Fact (1 < n)]
    (hodd_n : Odd n) (hodd_d : Odd d) (hdecomp : n - 1 = d * 2 ^ s)
    (hcomp : ¬ n.Prime) (hm : m ≤ 15)
    (hupper : (n : ℝ) < (2 : ℝ) ^ k * (((17 : ℝ) + m) / 16)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ bachBoundFromKm k m ∧ p.Coprime n ∧ ¬ IsStrongProbablePrime n d s p := by
  have hn2 : 2 ≤ n := by have : 1 < n := Fact.out; omega
  have hex_ej := odd_composite_exists_euler_jacobi_witness hodd_n hcomp
  obtain ⟨a, ha1, ha_real, ha_cop, ha_not_ej⟩ :=
    hBach hGRH n hn2 (eulerJacobiSubgroup n) hex_ej
  have ha_bound : a ≤ bachBoundFromKm k m := bachBound_sound hn2 hm hupper ha_real
  obtain ⟨p, hp_prime, hp_le, hp_cop, hp_not_ej⟩ :=
    prime_witness_of_coprime_witness (eulerJacobiSubgroup n) ha1 ha_bound ha_cop ha_not_ej
  refine ⟨p, hp_prime, hp_le, hp_cop, ?_⟩
  intro hspp
  exact hp_not_ej (strong_liar_mem_euler_jacobi hodd_n hodd_d hdecomp hp_cop hspp)

/-- Exact bidirectional soundness and completeness of deterministic prime-base Miller-Bach
up to the pure-integer bound `bachBoundFromKm k m`. -/
theorem miller_bach_prime_iff_all_prime_bases
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hBach : BachSubgroupBound)
    {n d s k m : ℕ} [Fact (1 < n)]
    (hodd_n : Odd n) (hodd_d : Odd d) (hdecomp : n - 1 = d * 2 ^ s)
    (hm : m ≤ 15)
    (hupper : (n : ℝ) < (2 : ℝ) ^ k * (((17 : ℝ) + m) / 16)) :
    n.Prime ↔
      ∀ p : ℕ, p.Prime → p ≤ bachBoundFromKm k m → p.Coprime n → IsStrongProbablePrime n d s p := by
  constructor
  · intro hn_prime p _ _ hp_cop
    exact prime_is_strong_probable_prime hn_prime hdecomp hp_cop
  · intro hall
    by_contra hcomp
    obtain ⟨p, hp_prime, hp_le, hp_cop, hnot_spp⟩ :=
      miller_bach_composite_has_prime_witness hGRH hBach hodd_n hodd_d hdecomp hcomp hm hupper
    exact hnot_spp (hall p hp_prime hp_le hp_cop)

/-- End-to-end prime non-residue theorem backing `least_nonresidue` and `sqrt_mod_prime`:
every prime `p >= 5` bounded by `2^k * (17 + m) / 16` (`m <= 15`) possesses a PRIME
quadratic non-residue `q <= llsBoundFromKm k m` coprime to `p`. -/
theorem least_nonresidue_has_prime_witness
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hLLS : LLSNonresidueBound)
    {p k m : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hm : m ≤ 15)
    (hupper : (p : ℝ) < (2 : ℝ) ^ k * (((17 : ℝ) + m) / 16)) :
    ∃ q : ℕ, q.Prime ∧ q ≤ llsBoundFromKm k m ∧ q.Coprime p ∧ ¬ IsSquare (q : ZMod p) := by
  have hp2 : 2 ≤ p := by omega
  obtain ⟨a, ha1, ha_real, ha_cop, ha_nonsq⟩ := hLLS hGRH p hp5
  have ha_bound : a ≤ llsBoundFromKm k m := llsBound_sound hp2 hm hupper ha_real
  exact prime_nonresidue_witness ha1 ha_bound ha_cop ha_nonsq

end DetPrime
