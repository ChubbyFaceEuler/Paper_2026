/-
  ZHY BLUE Theorem: Lean 4 Formalisation
  =======================================
  Yang Wu Azzollini (Oxford DPhil 2016, revised 2026)

  Proves the BLUE optimality result:
    BLUE_A1 : For any c with Σ c_ij τ_ij = 1,
              Σ c_ij² τX_i τY_j ≥ 1/Θ = A₁(w*)

  This is the ρ=0 case of the Asynchronous Gauss-Markov Theorem.
  Proof uses Cauchy-Schwarz (Finset.sum_mul_sq_le_sq_mul_sq) with
  u p = c · √(τX τY) and v p = τ / √(τX τY).
-/

import Mathlib

open BigOperators Finset Real

variable {m n : ℕ}
variable (τ  : Fin m → Fin n → ℝ)
variable (τX : Fin m → ℝ)
variable (τY : Fin n → ℝ)

-- ============================================================
-- The key quantity Θ = Σ_ij τ_ij² / (τX_i · τY_j)
-- ============================================================

noncomputable def Theta : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, τ i j ^ 2 / (τX i * τY j)

-- ============================================================
-- Main Theorem: BLUE_A1
-- ============================================================

/--
  **Theorem (BLUE at ρ=0)**: For any c with Σ c_ij · τ_ij = 1:
    Σ c_ij² · τX_i · τY_j ≥ 1/Θ
  Proof: Cauchy-Schwarz with u = c·√(τX τY), v = τ/√(τX τY).
-/
theorem BLUE_A1
    (c : Fin m → Fin n → ℝ)
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (hτ_nn : ∀ i j, 0 ≤ τ i j)
    (h_unbiased : ∑ i : Fin m, ∑ j : Fin n, c i j * τ i j = 1)
    (hΘ : 0 < Theta τ τX τY) :
    1 / Theta τ τX τY ≤ ∑ i : Fin m, ∑ j : Fin n, c i j ^ 2 * τX i * τY j := by
  let u : Fin m × Fin n → ℝ := fun p => c p.1 p.2 * sqrt (τX p.1 * τY p.2)
  let v : Fin m × Fin n → ℝ := fun p => τ p.1 p.2 / sqrt (τX p.1 * τY p.2)
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ (α := Fin m × Fin n)) u v
  -- Step 1: Σ u·v = Σ c·τ = 1
  have huv : ∑ p : Fin m × Fin n, u p * v p = 1 := by
    have heq : ∀ p : Fin m × Fin n, u p * v p = c p.1 p.2 * τ p.1 p.2 := fun ⟨i, j⟩ => by
      simp only [u, v]
      field_simp [Real.sqrt_ne_zero'.mpr (mul_pos (hτX i) (hτY j))]
    simp_rw [heq]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    exact h_unbiased
  -- Step 2: Σ u² = A₁(c)
  have hu2 : ∑ p : Fin m × Fin n, u p ^ 2 =
      ∑ i : Fin m, ∑ j : Fin n, c i j ^ 2 * τX i * τY j := by
    have heq : ∀ p : Fin m × Fin n, u p ^ 2 = c p.1 p.2 ^ 2 * τX p.1 * τY p.2 :=
      fun ⟨i, j⟩ => by
        simp only [u]; rw [mul_pow, Real.sq_sqrt (le_of_lt (mul_pos (hτX i) (hτY j)))]; ring
    simp_rw [heq]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  -- Step 3: Σ v² = Θ
  have hv2 : ∑ p : Fin m × Fin n, v p ^ 2 = Theta τ τX τY := by
    have heq : ∀ p : Fin m × Fin n, v p ^ 2 = τ p.1 p.2 ^ 2 / (τX p.1 * τY p.2) :=
      fun ⟨i, j⟩ => by
        simp only [v]; rw [div_pow, Real.sq_sqrt (le_of_lt (mul_pos (hτX i) (hτY j)))]
    simp_rw [heq, Theta]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  -- cs: (Σ uv)² ≤ (Σ u²)(Σ v²), substituted: 1 ≤ A₁ · Θ
  rw [huv, hu2, hv2] at cs
  simp only [one_pow] at cs
  -- From 1 ≤ A₁ · Θ, deduce 1/Θ ≤ A₁
  rw [← sub_nonneg]
  have : ∑ i : Fin m, ∑ j : Fin n, c i j ^ 2 * τX i * τY j - 1 / Theta τ τX τY =
         ((∑ i : Fin m, ∑ j : Fin n, c i j ^ 2 * τX i * τY j) * Theta τ τX τY - 1) /
         Theta τ τX τY := by field_simp
  rw [this]
  exact div_nonneg (by linarith) hΘ.le

-- ============================================================
-- Corollary: Equality at optimal weights
-- ============================================================

/-- At w*_ij = τ_ij/(τX_i τY_j): Σ (w*)² τX τY = Θ. -/
theorem A1_opt_eq
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (hΘ : 0 < Theta τ τX τY) :
    ∑ i : Fin m, ∑ j : Fin n,
      (τ i j / (τX i * τY j)) ^ 2 * τX i * τY j =
    Theta τ τX τY := by
  simp only [Theta]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  field_simp [ne_of_gt (mul_pos (hτX i) (hτY j))]

/--
  A₁(w*) = (Σ (w*)² τX τY) / Θ² = Θ / Θ² = 1/Θ.
  So BLUE_A1 is sharp: the optimal ZHY estimator achieves the minimum.
-/
theorem BLUE_A1_sharp
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (hΘ : 0 < Theta τ τX τY) :
    let w_opt := fun i j => τ i j / (τX i * τY j)
    (∑ i : Fin m, ∑ j : Fin n, w_opt i j ^ 2 * τX i * τY j) / (Theta τ τX τY) ^ 2
    = 1 / Theta τ τX τY := by
  simp only []
  rw [A1_opt_eq τ τX τY hτX hτY hΘ]
  field_simp [ne_of_gt hΘ]

/-
  Summary:
  BLUE_A1       : A₁(c) ≥ 1/Θ for all unbiased c         [proved ✓]
  A1_opt_eq     : Σ (w*)² τX τY = Θ                       [proved ✓]
  BLUE_A1_sharp : A₁(w*) = Θ/Θ² = 1/Θ                    [proved ✓]

  Together: A₁(w*) = 1/Θ ≤ A₁(c) for all unbiased c.
  The optimal ZHY estimator minimises A₁.
-/
