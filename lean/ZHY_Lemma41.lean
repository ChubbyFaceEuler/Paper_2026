/-
  Lean 4 formalisation of Lemma 4.1 and supporting results
  from the ZHY covariance estimation paper.

  Yang Wu Azzollini (2016, 2026)
  "Exact Finite-Sample Variance of the Weighted ZHY Estimator"

  This file contains:
    1. The model setup (bivariate Brownian motion, asynchronous observation)
    2. Lemma 4.1: characterisation of unbiased cross-product estimators
    3. A sketch of Theorem 1 (Overlap Variance Decomposition)

  Dependencies: Mathlib4
  Status: Proof sketches -- some sorries mark steps requiring
          additional Mathlib lemmas or more detailed argument.

  To compile:
    lake update
    lake build
-/

import Mathlib.Probability.Variance
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.Distributions.Gaussian

open BigOperators MeasureTheory ProbabilityTheory

-- ============================================================
-- Section 1: Model Setup
-- ============================================================

/--
  Index types for return intervals.
  Asset X has m return intervals, asset Y has n return intervals.
-/
variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- Overlap length between return interval i of X and interval j of Y. -/
noncomputable def τ (i : Fin m) (j : Fin n) : ℝ := sorry
-- In practice: τ i j = max 0 (min (t_{i+1}) (u_{j+1}) - max (t_i) (u_j))

/-- Interval length for asset X. -/
noncomputable def τX (i : Fin m) : ℝ := sorry

/-- Interval length for asset Y. -/
noncomputable def τY (j : Fin n) : ℝ := sorry

-- Model parameters (constant on activity clock)
variable (σ₁ σ₂ σ₁₂ : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)

/-- Return of asset X over interval i. -/
noncomputable def R (i : Fin m) : Ω → ℝ := sorry

/-- Return of asset Y over interval j. -/
noncomputable def S (j : Fin n) : Ω → ℝ := sorry

-- Key model property: E[R_i * S_j] = σ₁₂ * τ i j
axiom E_RS (i : Fin m) (j : Fin n) :
    𝔼[R i * S j] = σ₁₂ * τ i j

-- ============================================================
-- Section 2: Lemma 4.1
-- ============================================================

/--
  A cross-product estimator is a linear combination of products R_i * S_j.
  It is parameterised by coefficients c : Fin m → Fin n → ℝ.
-/
noncomputable def crossProductEstimator
    (c : Fin m → Fin n → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, ∑ j, c i j * (R i ω * S j ω)

/--
  The expected value of a cross-product estimator.
  By linearity of expectation and E_RS.
-/
lemma E_crossProductEstimator (c : Fin m → Fin n → ℝ)
    [IsProbabilityMeasure (ℙ : Measure Ω)] :
    𝔼[crossProductEstimator c] = σ₁₂ * ∑ i, ∑ j, c i j * τ i j := by
  simp [crossProductEstimator]
  rw [integral_sum]; swap; · sorry -- integrability
  congr 1; ext i
  rw [integral_sum]; swap; · sorry -- integrability
  congr 1; ext j
  rw [integral_const_mul]
  rw [E_RS]
  ring

/--
  **Lemma 4.1**: Characterisation of unbiased cross-product estimators.

  A cross-product estimator with coefficients c is unbiased for σ₁₂
  if and only if ∑_{i,j} c_{ij} * τ_{ij} = 1.

  In particular, only pairs (i,j) with τ_{ij} > 0 (overlapping intervals)
  contribute to an unbiased estimator.
-/
theorem lemma41_unbiased_iff (c : Fin m → Fin n → ℝ)
    [IsProbabilityMeasure (ℙ : Measure Ω)] :
    (∀ σ₁₂ : ℝ, 𝔼[crossProductEstimator c] = σ₁₂) ↔
    ∑ i, ∑ j, c i j * τ i j = 1 := by
  constructor
  · intro h
    -- h says: for all σ₁₂, σ₁₂ * (∑ c_ij τ_ij) = σ₁₂
    -- Taking σ₁₂ = 1 gives ∑ c_ij τ_ij = 1
    have h1 := h 1
    simp [E_crossProductEstimator] at h1
    linarith
  · intro hsum σ₁₂
    rw [E_crossProductEstimator]
    rw [hsum]
    ring

/--
  Corollary: Terms with τ_{ij} = 0 do not affect unbiasedness.
  Non-overlapping pairs are irrelevant.
-/
corollary nonOverlapping_irrelevant
    (c c' : Fin m → Fin n → ℝ)
    (h : ∀ i j, τ i j > 0 → c i j = c' i j) :
    (∑ i, ∑ j, c i j * τ i j) = (∑ i, ∑ j, c' i j * τ i j) := by
  congr 1; ext i; congr 1; ext j
  by_cases hij : τ i j > 0
  · rw [h i j hij]
  · push_neg at hij
    have : τ i j ≤ 0 := hij
    -- τ i j ≥ 0 by construction (overlap length is non-negative)
    have hnn : τ i j ≥ 0 := sorry -- from definition of τ as max(0,...)
    have : τ i j = 0 := le_antisymm this hnn
    simp [this]

-- ============================================================
-- Section 3: Theorem 1 sketch
-- ============================================================

/--
  Key covariance formula from Isserlis' theorem (Wick's theorem):
  For zero-mean jointly Gaussian variables,
    Cov(R_i * S_j, R_k * S_l) = σ₁₂² * τ_{il} * τ_{kj}
  when (i,j) ≠ (k,l).

  This is the central calculation in the proof of Theorem 1.
-/
axiom cov_RS_RS (i k : Fin m) (j l : Fin n) (h : (i,j) ≠ (k,l)) :
    cov (R i * S j) (R k * S l) = σ₁₂^2 * τ i l * τ k j

/--
  Variance formula for a single cross-product:
    Var(R_i * S_j) = σ₁² σ₂² τ_i^X τ_j^Y + σ₁₂² τ_{ij}²
-/
axiom var_RS (i : Fin m) (j : Fin n) :
    variance (R i * S j) = σ₁^2 * σ₂^2 * τX i * τY j + σ₁₂^2 * (τ i j)^2

/--
  **Theorem 1 sketch**: Overlap Variance Decomposition.

  For the normalised weighted ZHY estimator with weight matrix w,
    Var(σ̂₁₂ | τ) = σ₁²σ₂² A₁(w) + σ₁₂² A₂(w)

  where A₁ and A₂ are as defined in equations (3.1)-(3.2) of the paper.

  The proof expands Var(∑_{ij} w_{ij} R_i S_j) using bilinearity of
  covariance, applies var_RS and cov_RS_RS, and collects terms.
  The third case (i≠k, j≠l) vanishes because disjoint intervals
  cannot both overlap with two other disjoint intervals simultaneously.
-/
theorem theorem1_sketch (w : Fin m → Fin n → ℝ)
    (Tw : ∑ i, ∑ j, w i j * τ i j ≠ 0) :
    True := by
  -- Full proof requires:
  -- 1. Expand variance of sum using bilinearity
  -- 2. Apply var_RS for diagonal terms
  -- 3. Apply cov_RS_RS for off-diagonal terms
  -- 4. Split off-diagonal sum into three cases: i=k j≠l, j=l i≠k, i≠k j≠l
  -- 5. Show case i≠k j≠l vanishes (disjoint intervals cannot doubly overlap)
  -- 6. Collect terms and divide by T(w)²
  trivial

-- ============================================================
-- Section 4: Setup for Theorem 4 (Asynchronous Gauss-Markov)
-- at rho = 0
-- ============================================================

/--
  At σ₁₂ = 0, the observations R and S are independent.
  The joint covariance matrix is block-diagonal.
  Fisher information for σ₁₂ at σ₁₂=0:

    I(σ₁₂)|_{σ₁₂=0} = ∑_{ij} τ_{ij}² / (σ₁² τ_i^X · σ₂² τ_j^Y)

  This equals 1/(σ₁²σ₂² A₁*) where A₁* is the minimum of A₁
  achieved at the optimal weights w*_{ij} = τ_{ij}/(τ_i^X τ_j^Y).
-/
theorem fisher_info_at_zero_equals_inv_varA1star :
    -- Fisher information at rho=0
    let FI := ∑ i : Fin m, ∑ j : Fin n,
              (τ i j)^2 / (σ₁^2 * τX i * σ₂^2 * τY j)
    -- Minimum A₁ at optimal weights
    let A1star := 1 / (∑ i : Fin m, ∑ j : Fin n,
                       (τ i j)^2 / (τX i * τY j))
    -- Claim: 1/FI = σ₁²σ₂² A₁*
    FI * (σ₁^2 * σ₂^2 * A1star) = 1 := by
  simp only []
  field_simp
  ring

