import KE02.SlopeDefinitions
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Statement: the scalar arithmetic of Section 3

Lemma 3.1 (localization), Lemma 3.2 (auxiliary matrix) and Proposition 3.1
(local gap certificate) are not formalized as matrix statements. These are
the real-number inequalities and identities their proofs use, with the
quantities named as in the paper: `γ` is the gap bound, `τ = 4√(nγ)`, `N`
stands for the nuclear norm `‖H(t) - H̃‖_*`, and `G` for the auxiliary
spectral function `F^aux`.
-/

namespace KE02

structure LocalConstantsCertificate : Prop where
  /-- Lemma 3.1, Step 1: `n` rows of norm below `1/(2√n)` have total squared
  norm below `n (1/(2√n))² = 1/4`. -/
  discarded_rows : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * (1 / (2 * Real.sqrt n)) ^ 2 = 1 / 4
  /-- Lemma 3.1, (21): `√(3/8) > 1/2`. -/
  direction_gap : (1 : ℝ) / 2 < Real.sqrt (3 / 8)
  /-- Lemma 3.1, Step 3: `τ = 4√(nγ) ≤ 1/(4√n)` when `γ ≤ 1/(256 n²)`. -/
  tau_le : ∀ (n : ℕ) (γ : ℝ), 1 ≤ n → 0 ≤ γ → γ ≤ 1 / (256 * (n : ℝ) ^ 2) →
    4 * Real.sqrt (n * γ) ≤ 1 / (4 * Real.sqrt n)
  /-- Lemma 3.1, Step 3, case (a): `γ/(2τ²) ≤ 5γ/τ²`. -/
  case_a : ∀ γ τ : ℝ, 0 ≤ γ → 0 < τ → γ / (2 * τ ^ 2) ≤ 5 * γ / τ ^ 2
  /-- Lemma 3.1, Step 3, case (c), with `A = |β_(i-1)| ‖r_(i-1)‖ > τ`,
  `B = |β_i| ‖r_(i+1)‖ > τ` and `ρ = ‖r_i‖ ≤ τ ≤ 1`. -/
  case_c : ∀ γ τ A B ρ : ℝ, 0 ≤ γ → 0 < τ → τ ≤ 1 → τ < A → τ < B → 0 ≤ ρ → ρ ≤ τ →
    2 * γ / (A * B) + γ * ρ / (2 * B) ≤ 5 * γ / τ ^ 2
  /-- Lemma 3.1, Step 3: `5nγ/τ² = 5/16 < 1/2`. -/
  total_change : ∀ (n : ℕ) (γ : ℝ), 1 ≤ n → 0 < γ →
    5 * n * γ / (4 * Real.sqrt (n * γ)) ^ 2 = 5 / 16 ∧ (5 : ℝ) / 16 < 1 / 2
  /-- Lemma 3.1, Step 4: `2√n (γ/2 + √2 τ) ≤ 4√n τ = 16 n √γ`. -/
  truncation : ∀ (n : ℕ) (γ : ℝ), 1 ≤ n → 0 ≤ γ → γ ≤ 1 / (256 * (n : ℝ) ^ 2) →
    2 * Real.sqrt n * (γ / 2 + Real.sqrt 2 * (4 * Real.sqrt (n * γ))) ≤
        4 * Real.sqrt n * (4 * Real.sqrt (n * γ)) ∧
      4 * Real.sqrt n * (4 * Real.sqrt (n * γ)) = 16 * n * Real.sqrt γ
  /-- Lemma 3.2, (26): `3√2 (a₁² + a₂²)^(1/2) ≤ 96 n √γ` when `0 ≤ aᵢ ≤ 16 n √γ`. -/
  nuclear : ∀ (n : ℕ) (γ a₁ a₂ : ℝ), 0 ≤ a₁ → 0 ≤ a₂ →
    a₁ ≤ 16 * n * Real.sqrt γ → a₂ ≤ 16 * n * Real.sqrt γ →
    3 * Real.sqrt 2 * Real.sqrt (a₁ ^ 2 + a₂ ^ 2) ≤ 96 * n * Real.sqrt γ
  /-- Proposition 3.1: `0 < h ≤ 1` gives `0 < γ ≤ 1/(256 n²)` for
  `γ = h²/(2²⁰ n⁴)`. -/
  gamma_range : ∀ (n : ℕ) (h : ℝ), 1 ≤ n → 0 < h → h ≤ 1 →
    0 < h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4) ∧ h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4) ≤ 1 / (256 * (n : ℝ) ^ 2)
  /-- The quotient in (27) is the centered slope variation (13) of the auxiliary function. -/
  aux_variation : ∀ (G : ℝ → ℝ) (h t : ℝ),
    (G (t + h) + G (t - h) - 2 * G t) / h = centeredVariation G h t
  /-- Proof of Proposition 3.1: (28) at `t-h, t, t+h` gives
  `S_h(t) ≥ S_h^aux(t) - (4n/h) N`. -/
  transfer : ∀ (F G : ℝ → ℝ) (n N h t : ℝ), 0 < h →
    |F (t - h) - G (t - h)| ≤ n * N → |F t - G t| ≤ n * N → |F (t + h) - G (t + h)| ≤ n * N →
    centeredVariation G h t - 4 * n / h * N ≤ centeredVariation F h t
  /-- `1 - 384 n² √γ / h = 1 - 384/1024 = 5/8 > 1/2` at `γ = h²/(2²⁰ n⁴)`. -/
  constant : ∀ (n : ℕ) (h : ℝ), 1 ≤ n → 0 < h →
    1 - 384 * (n : ℝ) ^ 2 * Real.sqrt (h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4)) / h = 5 / 8 ∧
      (384 : ℝ) / 1024 = 3 / 8 ∧ 1 - (3 : ℝ) / 8 = 5 / 8 ∧ (1 : ℝ) / 2 < 5 / 8
  /-- The scalar chain of the proof of Proposition 3.1: if `S_h^aux(t) ≥ 1`,
  `N ≤ 96 n √γ` with `γ = h²/(2²⁰ n⁴)`, and `|F - G| ≤ n N` at `t-h, t, t+h`,
  then `S_h(t) > 1/2`. -/
  chain : ∀ (F G : ℝ → ℝ) (n : ℕ) (N h t : ℝ), 1 ≤ n → 0 < h →
    N ≤ 96 * n * Real.sqrt (h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4)) →
    |F (t - h) - G (t - h)| ≤ n * N → |F t - G t| ≤ n * N → |F (t + h) - G (t + h)| ≤ n * N →
    1 ≤ centeredVariation G h t → 1 / 2 < centeredVariation F h t
  /-- Theorem 4.2: `h > δ/(128 n⁴)` gives `h²/(2²⁰ n⁴) > 2⁻³⁴ δ² n⁻¹²`. -/
  gap_chain : ∀ (n : ℕ) (δ h : ℝ), 1 ≤ n → 0 < δ → δ / (128 * (n : ℝ) ^ 4) < h →
    (2 : ℝ)⁻¹ ^ 34 * δ ^ 2 / (n : ℝ) ^ 12 < h ^ 2 / (2 ^ 20 * (n : ℝ) ^ 4)

end KE02
