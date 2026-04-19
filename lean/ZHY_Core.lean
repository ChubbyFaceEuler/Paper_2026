/-
  ZHY Covariance Estimator: Lean 4 Formalisation
  ===============================================
  Yang Wu Azzollini (Oxford DPhil 2016, revised 2026)

  "Exact Finite-Sample Variance of the Weighted ZHY Estimator"

  Theorems proved (zero sorries):
    · Lemma 4.1  -- characterisation of unbiased cross-product estimators
    · Corollary  -- non-overlapping pairs irrelevant to unbiasedness
    · Proposition -- Fisher information equality at ρ = 0
-/

import Mathlib

open BigOperators Finset

-- ============================================================
-- Section 1: Setup and Notation
-- ============================================================

variable {m n : ℕ}

/-
  τ i j = overlap length between return interval i of X and j of Y.
  Key property: τ i j ≥ 0.
-/
variable (τ : Fin m → Fin n → ℝ)
variable (hτ_nn : ∀ i j, 0 ≤ τ i j)

-- Integrated covariance to be estimated.
variable (σ₁₂ : ℝ)

-- ============================================================
-- Section 2: Cross-Product Estimators
-- ============================================================

/-- Expected value of cross-product estimator given H_expect: E[R_i S_j] = σ₁₂ · τ i j. -/
noncomputable def estimatorExpectation (c : Fin m → Fin n → ℝ) : ℝ :=
  σ₁₂ * ∑ i, ∑ j, c i j * τ i j

-- ============================================================
-- Section 3: Lemma 4.1
-- ============================================================

/--
  **Lemma 4.1**: A cross-product estimator c is unbiased for σ₁₂ for all σ₁₂
  if and only if Σ_ij c_ij · τ_ij = 1.
-/
theorem lemma41_unbiased_iff (c : Fin m → Fin n → ℝ) :
    (∀ σ : ℝ, estimatorExpectation τ σ c = σ) ↔
    ∑ i, ∑ j, c i j * τ i j = 1 := by
  constructor
  · intro h
    have h1 := h 1
    simp [estimatorExpectation] at h1
    linarith
  · intro hsum σ
    simp [estimatorExpectation, hsum]

/-- Non-overlapping pairs are irrelevant to unbiasedness. -/
theorem nonOverlapping_irrelevant
    (c c' : Fin m → Fin n → ℝ)
    (h : ∀ i j, 0 < τ i j → c i j = c' i j)
    (hτ_nn : ∀ i j, 0 ≤ τ i j) :
    ∀ σ : ℝ, estimatorExpectation τ σ c = estimatorExpectation τ σ c' := by
  intro σ
  unfold estimatorExpectation
  congr 1
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases hij : 0 < τ i j
  · rw [h i j hij]
  · push_neg at hij
    have hzero : τ i j = 0 := le_antisymm hij (hτ_nn i j)
    simp [hzero]

-- ============================================================
-- Section 4: Unbiasedness of ZHY Estimator
-- ============================================================

/-- The normalised ZHY estimator with weights w is unbiased. -/
theorem zhy_unbiased
    (w : Fin m → Fin n → ℝ) (Tw : ℝ)
    (hTw : Tw = ∑ i, ∑ j, τ i j * w i j)
    (hTw_pos : 0 < Tw) :
    ∑ i, ∑ j, (w i j / Tw) * τ i j = 1 := by
  have hTw_ne : Tw ≠ 0 := ne_of_gt hTw_pos
  calc ∑ i : Fin m, ∑ j : Fin n, w i j / Tw * τ i j
      = ∑ i : Fin m, ∑ j : Fin n, (w i j * τ i j) / Tw := by
          congr 1; ext i; congr 1; ext j; ring
    _ = (∑ i : Fin m, ∑ j : Fin n, w i j * τ i j) / Tw := by
          simp [Finset.sum_div]
    _ = Tw / Tw := by
          congr 1; rw [hTw]; congr 1; ext i; congr 1; ext j; ring
    _ = 1 := div_self hTw_ne

-- ============================================================
-- Section 5: Optimal A₁ Weights
-- ============================================================

/-- A₁(w) = [Σ_ij w_ij² · τX_i · τY_j] / T(w)² -/
noncomputable def A1 (τX : Fin m → ℝ) (τY : Fin n → ℝ)
    (w : Fin m → Fin n → ℝ) (Tw : ℝ) : ℝ :=
  (∑ i, ∑ j, w i j ^ 2 * τX i * τY j) / Tw ^ 2

/--
  At optimal weights w*_ij = τ_ij / (τX_i · τY_j):
  T(w*) = Θ = Σ_ij τ_ij² / (τX_i · τY_j).
-/
theorem A1_optimal_explicit
    (τX : Fin m → ℝ) (τY : Fin n → ℝ)
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (hτ_nn : ∀ i j, 0 ≤ τ i j) :
    let w_opt := fun i j => τ i j / (τX i * τY j)
    let Tw_opt := ∑ i : Fin m, ∑ j : Fin n, τ i j * w_opt i j
    let Θ := ∑ i : Fin m, ∑ j : Fin n, τ i j ^ 2 / (τX i * τY j)
    Tw_opt = Θ := by
  show ∑ i : Fin m, ∑ j : Fin n, τ i j * (τ i j / (τX i * τY j)) =
       ∑ i : Fin m, ∑ j : Fin n, τ i j ^ 2 / (τX i * τY j)
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have hXi : τX i ≠ 0 := ne_of_gt (hτX i)
  have hYj : τY j ≠ 0 := ne_of_gt (hτY j)
  field_simp [hXi, hYj, sq]

-- ============================================================
-- Section 6: Fisher Information Equality at ρ = 0
-- ============================================================

/-- At ρ=0: FI · Var_min = 1 (Cramér-Rao lower bound achieved). -/
theorem CR_equality_at_zero
    (σ₁sq σ₂sq : ℝ) (hσ₁ : 0 < σ₁sq) (hσ₂ : 0 < σ₂sq)
    (τX : Fin m → ℝ) (τY : Fin n → ℝ)
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (hτ_nn : ∀ i j, 0 ≤ τ i j) :
    let Θ := ∑ i : Fin m, ∑ j : Fin n, τ i j ^ 2 / (τX i * τY j)
    let FI := ∑ i : Fin m, ∑ j : Fin n,
              τ i j ^ 2 / (σ₁sq * τX i * (σ₂sq * τY j))
    let Var_min := σ₁sq * σ₂sq / Θ
    (hΘ : 0 < Θ) → FI * Var_min = 1 := by
  intro Θ FI Var_min hΘ
  have hσ : σ₁sq * σ₂sq > 0 := mul_pos hσ₁ hσ₂
  have hFI : FI = Θ / (σ₁sq * σ₂sq) := by
    show ∑ i : Fin m, ∑ j : Fin n,
           τ i j ^ 2 / (σ₁sq * τX i * (σ₂sq * τY j)) =
         (∑ i : Fin m, ∑ j : Fin n, τ i j ^ 2 / (τX i * τY j)) / (σ₁sq * σ₂sq)
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _
    have hXi : τX i ≠ 0 := ne_of_gt (hτX i)
    have hYj : τY j ≠ 0 := ne_of_gt (hτY j)
    field_simp
  have key : FI * Var_min = Θ / (σ₁sq * σ₂sq) * (σ₁sq * σ₂sq / Θ) := by
    simp only [hFI, Var_min]
  rw [key]
  field_simp [ne_of_gt hΘ, ne_of_gt hσ]

/-
  Summary of what is proved (zero sorries):
  1. lemma41_unbiased_iff     [Lemma 4.1]
  2. nonOverlapping_irrelevant [Corollary]
  3. zhy_unbiased              [Paper §3]
  4. A1_optimal_explicit       [Paper §4.1]
  5. CR_equality_at_zero       [Theorem 4, paper §4.4]
-/
