/-
  ZHY Exact Variance Decomposition: Lean 4 Formalisation
  ======================================================
  Yang Wu Azzollini (Oxford DPhil 2016, revised 2026)

  Theorem 5.1 of the DPhil thesis:

      Var(∑ᵢⱼ wᵢⱼ RᵢSⱼ | τ) = σ₁²σ₂² · U(w) + σ₁₂² · V(w)

  where
      U(w) = ∑ᵢⱼ wᵢⱼ² τXᵢ τYⱼ
      V(w) = ∑ᵢ (∑ⱼ wᵢⱼτᵢⱼ)² + ∑ⱼ (∑ᵢ wᵢⱼτᵢⱼ)² − ∑ᵢⱼ wᵢⱼ²τᵢⱼ²

  Probabilistic input (IsZHYModel): the bivariate-Brownian covariance
  structure + Isserlis' Gaussian fourth-moment identity, packaged as
  hypotheses.  Geometric input (NoRectangle): the Interval-Structure
  Lemma from thesis p.108.  Variance-of-a-sum is a structural hypothesis.

  The combinatorial scaffolding lives in ZHY_Algebra.lean; this file
  assembles the final decomposition.  Zero sorries.
-/

import Mathlib
import ZHY_Algebra

open BigOperators Finset

namespace ZHY

-- ============================================================
-- Section 1: Covariance structure of the pair-product family
-- ============================================================

/--
  `IsZHYModel` records the covariance structure of the return pair
  `{Rᵢ}, {Sⱼ}` under bivariate Brownian motion, together with the
  Gaussian (Isserlis) identity for the fourth mixed moment.  No sample
  space is constructed; the structure states only the identities the
  thesis proof uses under "by standard distribution theory".

  Fields:
    · `var_RS`    : Var(RᵢSⱼ) = σ₁²σ₂² τXᵢ τYⱼ + σ₁₂² τᵢⱼ²
    · `cov_same`  : Cov(RᵢSⱼ, RᵢSⱼ) = Var(RᵢSⱼ)
    · `cov_sameI` : i = k, j ≠ l  →  Cov = σ₁₂² τᵢⱼ τᵢₗ
    · `cov_sameJ` : i ≠ k, j = l  →  Cov = σ₁₂² τᵢⱼ τₖⱼ
    · `cov_diff`  : i ≠ k, j ≠ l  →  Cov = σ₁₂² τᵢₗ τₖⱼ
-/
structure IsZHYModel
    {m n : ℕ}
    (τ    : Fin m → Fin n → ℝ)
    (τX   : Fin m → ℝ)
    (τY   : Fin n → ℝ)
    (σ₁sq σ₂sq σ₁₂ : ℝ)
    (VRS  : Fin m → Fin n → ℝ)
    (CRSRS : Fin m → Fin n → Fin m → Fin n → ℝ)
    : Prop where
  var_RS :
    ∀ i j, VRS i j = σ₁sq * σ₂sq * τX i * τY j + σ₁₂ ^ 2 * τ i j ^ 2
  cov_same :
    ∀ i j, CRSRS i j i j = VRS i j
  cov_sameI :
    ∀ i j l, j ≠ l → CRSRS i j i l = σ₁₂ ^ 2 * τ i j * τ i l
  cov_sameJ :
    ∀ i k j, i ≠ k → CRSRS i j k j = σ₁₂ ^ 2 * τ i j * τ k j
  cov_diff :
    ∀ i k j l, i ≠ k → j ≠ l →
      CRSRS i j k l = σ₁₂ ^ 2 * τ i l * τ k j

-- ============================================================
-- Section 2: Geometric input — Interval-Structure Lemma
-- ============================================================

/--
  **Interval-Structure Lemma** (DPhil thesis Ch 5, p. 108).

  For any two distinct X-return indices i ≠ k and any two distinct
  Y-return indices j ≠ l, the overlaps τᵢₗ and τₖⱼ cannot both be
  strictly positive.  (In the thesis: J^X_i, J^X_k are disjoint
  consecutive intervals, as are J^Y_j, J^Y_l; both positive overlaps
  would force J^X_i, J^X_k to meet both J^Y_j and J^Y_l, contradicting
  disjointness.)

  Here it is a property of the overlap matrix τ, matching the thesis's
  use of it.
-/
def NoRectangle
    {m n : ℕ} (τ : Fin m → Fin n → ℝ) : Prop :=
  ∀ i k : Fin m, ∀ j l : Fin n,
    i ≠ k → j ≠ l → τ i l = 0 ∨ τ k j = 0

-- ============================================================
-- Section 3: Variance of a linear combination — structural input
-- ============================================================

/--
  Structural identity: the variance of `∑ᵢⱼ wᵢⱼ RᵢSⱼ` equals the
  double sum of covariances.  Taken as a hypothesis here; proof
  follows from `Var(∑ X) = ∑_{i,k} Cov(Xᵢ, Xₖ)` applied inductively.
-/
def HasLinearVariance
    {m n : ℕ}
    (w     : Fin m → Fin n → ℝ)
    (CRSRS : Fin m → Fin n → Fin m → Fin n → ℝ)
    (V     : ℝ) : Prop :=
  V = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n,
        w i j * w k l * CRSRS i j k l

-- ============================================================
-- Section 4: The two summands U(w) and V(w)
-- ============================================================

variable {m n : ℕ}

/-- `U(w) = ∑ᵢⱼ wᵢⱼ² τXᵢ τYⱼ` — coefficient of σ₁²σ₂². -/
noncomputable def USum (w : Fin m → Fin n → ℝ)
    (τX : Fin m → ℝ) (τY : Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, w i j ^ 2 * τX i * τY j

/-- `V(w) = ∑ᵢ (∑ⱼ wᵢⱼτᵢⱼ)² + ∑ⱼ (∑ᵢ wᵢⱼτᵢⱼ)² − ∑ᵢⱼ (wᵢⱼτᵢⱼ)²`
    — coefficient of σ₁₂². -/
noncomputable def VSum (w : Fin m → Fin n → ℝ)
    (τ : Fin m → Fin n → ℝ) : ℝ :=
    (∑ i : Fin m, (∑ j : Fin n, w i j * τ i j) ^ 2)
  + (∑ j : Fin n, (∑ i : Fin m, w i j * τ i j) ^ 2)
  - (∑ i : Fin m, ∑ j : Fin n, (w i j * τ i j) ^ 2)

-- ============================================================
-- Section 5: Main theorem
-- ============================================================

/--
  **Theorem 5.1** (DPhil thesis 2016; formal verification 2026).

  Under the ZHY model, for any weight matrix `w`, the conditional
  variance of the weighted cross-product sum decomposes exactly:

      Var(∑ᵢⱼ wᵢⱼ Rᵢ Sⱼ | τ) = σ₁²σ₂² · U(w) + σ₁₂² · V(w).

  This is an exact finite-sample identity: no asymptotics, no
  distributional assumption on timestamps beyond the overlap
  structure τ satisfying the Interval-Structure Lemma.
-/
theorem theorem51
    (τ    : Fin m → Fin n → ℝ)
    (τX   : Fin m → ℝ)
    (τY   : Fin n → ℝ)
    (σ₁sq σ₂sq σ₁₂ : ℝ)
    (VRS  : Fin m → Fin n → ℝ)
    (CRSRS : Fin m → Fin n → Fin m → Fin n → ℝ)
    (H   : IsZHYModel τ τX τY σ₁sq σ₂sq σ₁₂ VRS CRSRS)
    (hNR : NoRectangle τ)
    (w   : Fin m → Fin n → ℝ)
    (V   : ℝ)
    (HV  : HasLinearVariance w CRSRS V) :
    V = σ₁sq * σ₂sq * USum w τX τY + σ₁₂ ^ 2 * VSum w τ := by
  -- Step 1: unfold HV and apply sum_split_four to the 4-fold sum.
  rw [HV]
  rw [sum_split_four (fun i j k l => w i j * w k l * CRSRS i j k l)]
  -- The goal now has four pieces corresponding to the four cases:
  --   P1 : diagonal           = ∑ᵢⱼ w i j · w i j · CRSRS i j i j
  --   P2 : same-i, diff-j     = ∑ᵢⱼₗ [j=l]·0 else w i j · w i l · CRSRS i j i l
  --   P3 : diff-i, same-j     = ∑ⱼᵢₖ [i=k]·0 else w i j · w k j · CRSRS i j k j
  --   P4 : both differ        = ∑ᵢⱼₖₗ [i=k ∨ j=l]·0 else w i j · w k l · CRSRS i j k l
  -- Target:    σ₁²σ₂² U(w) + σ₁₂² V(w).
  --
  -- Step 2: rewrite P1 using cov_same + var_RS.
  have hP1 : (∑ i : Fin m, ∑ j : Fin n,
                w i j * w i j * CRSRS i j i j)
           = σ₁sq * σ₂sq * USum w τX τY +
             σ₁₂ ^ 2 * (∑ i : Fin m, ∑ j : Fin n, (w i j * τ i j) ^ 2) := by
    unfold USum
    -- w i j * w i j * CRSRS i j i j = w i j ^ 2 * VRS i j
    --                              = w i j ^ 2 * (σ₁²σ₂² τXᵢ τYⱼ + σ₁₂² τᵢⱼ²)
    rw [show (∑ i : Fin m, ∑ j : Fin n,
                w i j * w i j * CRSRS i j i j)
        = ∑ i : Fin m, ∑ j : Fin n,
            (σ₁sq * σ₂sq * (w i j ^ 2 * τX i * τY j) +
             σ₁₂ ^ 2 * (w i j * τ i j) ^ 2) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [H.cov_same, H.var_RS]; ring]
    -- Distribute the sum across the + and pull constants out.
    rw [show (∑ i : Fin m, ∑ j : Fin n,
                (σ₁sq * σ₂sq * (w i j ^ 2 * τX i * τY j) +
                 σ₁₂ ^ 2 * (w i j * τ i j) ^ 2))
        = (∑ i : Fin m, ∑ j : Fin n,
              σ₁sq * σ₂sq * (w i j ^ 2 * τX i * τY j)) +
          (∑ i : Fin m, ∑ j : Fin n,
              σ₁₂ ^ 2 * (w i j * τ i j) ^ 2) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_add_distrib]]
    -- Pull σ₁sq * σ₂sq and σ₁₂^2 out of their sums.
    rw [show (∑ i : Fin m, ∑ j : Fin n,
                σ₁sq * σ₂sq * (w i j ^ 2 * τX i * τY j))
        = σ₁sq * σ₂sq *
          (∑ i : Fin m, ∑ j : Fin n, w i j ^ 2 * τX i * τY j) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]]
    rw [show (∑ i : Fin m, ∑ j : Fin n,
                σ₁₂ ^ 2 * (w i j * τ i j) ^ 2)
        = σ₁₂ ^ 2 *
          (∑ i : Fin m, ∑ j : Fin n, (w i j * τ i j) ^ 2) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]]
  -- Step 3: rewrite P2 using cov_sameI + sum_firstcase_collapse.
  have hP2 : (∑ i : Fin m, ∑ j : Fin n, ∑ l : Fin n,
                if j = l then (0:ℝ)
                else w i j * w i l * CRSRS i j i l)
           = σ₁₂ ^ 2 *
             ((∑ i : Fin m, (∑ j : Fin n, w i j * τ i j) ^ 2) -
              (∑ i : Fin m, ∑ j : Fin n, (w i j * τ i j) ^ 2)) := by
    -- Replace CRSRS i j i l by σ₁₂² τᵢⱼ τᵢₗ under j ≠ l.
    rw [show (∑ i : Fin m, ∑ j : Fin n, ∑ l : Fin n,
                if j = l then (0:ℝ)
                else w i j * w i l * CRSRS i j i l)
        = ∑ i : Fin m, ∑ j : Fin n, ∑ l : Fin n,
            if j = l then (0:ℝ)
            else σ₁₂ ^ 2 * ((w i j * τ i j) * (w i l * τ i l)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun l _ => ?_)
        by_cases h : j = l
        · simp [h]
        · rw [if_neg h, if_neg h, H.cov_sameI i j l h]; ring]
    -- Pull σ₁₂^2 outside the indicator.
    rw [show (∑ i : Fin m, ∑ j : Fin n, ∑ l : Fin n,
                if j = l then (0:ℝ)
                else σ₁₂ ^ 2 * ((w i j * τ i j) * (w i l * τ i l)))
        = σ₁₂ ^ 2 *
          (∑ i : Fin m, ∑ j : Fin n, ∑ l : Fin n,
              if j = l then (0:ℝ)
              else (w i j * τ i j) * (w i l * τ i l)) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        by_cases h : j = l
        · simp [h]
        · simp [h]]
    -- Apply sum_firstcase_collapse with h := w · τ.
    rw [sum_firstcase_collapse (fun i j => w i j * τ i j)]
  -- Step 4: rewrite P3 using cov_sameJ + sum_secondcase_collapse.
  have hP3 : (∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin m,
                if i = k then (0:ℝ)
                else w i j * w k j * CRSRS i j k j)
           = σ₁₂ ^ 2 *
             ((∑ j : Fin n, (∑ i : Fin m, w i j * τ i j) ^ 2) -
              (∑ j : Fin n, ∑ i : Fin m, (w i j * τ i j) ^ 2)) := by
    rw [show (∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin m,
                if i = k then (0:ℝ)
                else w i j * w k j * CRSRS i j k j)
        = ∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin m,
            if i = k then (0:ℝ)
            else σ₁₂ ^ 2 * ((w i j * τ i j) * (w k j * τ k j)) from by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases h : i = k
        · simp [h]
        · rw [if_neg h, if_neg h, H.cov_sameJ i k j h]; ring]
    rw [show (∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin m,
                if i = k then (0:ℝ)
                else σ₁₂ ^ 2 * ((w i j * τ i j) * (w k j * τ k j)))
        = σ₁₂ ^ 2 *
          (∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin m,
              if i = k then (0:ℝ)
              else (w i j * τ i j) * (w k j * τ k j)) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases h : i = k
        · simp [h]
        · simp [h]]
    rw [sum_secondcase_collapse (fun i j => w i j * τ i j)]
  -- Step 5: P4 vanishes by NoRectangle + cov_diff.
  have hP4 : (∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n,
                if i = k ∨ j = l then (0:ℝ)
                else w i j * w k l * CRSRS i j k l)
           = 0 := by
    -- Each summand is zero.
    rw [show (∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n,
                if i = k ∨ j = l then (0:ℝ)
                else w i j * w k l * CRSRS i j k l)
        = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n, (0:ℝ) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun l _ => ?_)
        by_cases hik : i = k
        · simp [hik]
        · by_cases hjl : j = l
          · simp [hjl]
          · -- i ≠ k, j ≠ l: use NoRectangle and cov_diff.
            have hne_or : i = k ∨ j = l ↔ False := by
              constructor
              · rintro (h | h)
                · exact hik h
                · exact hjl h
              · intro h; exact h.elim
            simp only [hne_or, if_false]
            rcases hNR i k j l hik hjl with h1 | h2
            · rw [H.cov_diff i k j l hik hjl, h1]; ring
            · rw [H.cov_diff i k j l hik hjl, h2]; ring]
    simp
  -- Step 6: assemble.
  rw [hP1, hP2, hP3, hP4]
  -- Note: sum_secondcase_collapse states ∑ⱼᵢ (wτ)² not ∑ᵢⱼ.
  -- These are equal by Finset.sum_comm.
  have comm_w2t2 :
      (∑ j : Fin n, ∑ i : Fin m, (w i j * τ i j) ^ 2)
        = ∑ i : Fin m, ∑ j : Fin n, (w i j * τ i j) ^ 2 :=
    Finset.sum_comm
  rw [comm_w2t2]
  unfold VSum
  ring

end ZHY
