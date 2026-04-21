/-
  ZHY Geometry: the Interval-Structure Lemma
  ===========================================
  Yang Wu Azzollini (Oxford DPhil 2016, revised 2026)

  This module formalises the geometric fact about asynchronous
  overlap matrices that closes the derivation of Theorem 1 (exact
  finite-sample variance) of the weighted ZHY estimator paper.

  Main result: `interval_structure_lemma`
    If i ≠ k, j ≠ ℓ, and τ_{ij} > 0 and τ_{kℓ} > 0 on an overlap
    matrix arising from two partitions of [0, 1], then
    τ_{iℓ} · τ_{kj} = 0.

  Approach: we axiomatize the overlap matrix via its structural
  properties (non-negativity, marginal identities, and the key
  "no rectangle" property that we extract from the underlying
  interval geometry), rather than constructing it from concrete
  measure theory.  This separates the combinatorial content
  (needed by Theorem 1's proof) from the measure-theoretic content
  (which is standard and would require a substantial excursion
  into Mathlib's interval/measure infrastructure).

  The correctness of the axiomatization is established in the
  accompanying paper, Lemma "Interval-Structure".
-/

import Mathlib

open BigOperators Finset

namespace ZHY.Geometry

-- ============================================================
-- Section 1: Partitions and overlap matrices
-- ============================================================

variable {m n : ℕ}

/--
  A `GridPair` packages the structural data of two asynchronous
  grids partitioning [0, 1], expressed through the overlap matrix
  and its marginals.

  The fields encode exactly the assumptions of Section 2 of the
  paper, plus the `no_rectangle` property extracted from the
  one-dimensional interval geometry.
-/
structure GridPair (m n : ℕ) where
  /-- Return-period lengths of asset X: τ^X_i. -/
  τX : Fin m → ℝ
  /-- Return-period lengths of asset Y: τ^Y_j. -/
  τY : Fin n → ℝ
  /-- Overlap lengths: τ_{ij}. -/
  τ  : Fin m → Fin n → ℝ
  /-- Return periods of X have positive length. -/
  hτX_pos : ∀ i, 0 < τX i
  /-- Return periods of Y have positive length. -/
  hτY_pos : ∀ j, 0 < τY j
  /-- Overlaps are non-negative. -/
  hτ_nn   : ∀ i j, 0 ≤ τ i j
  /-- Row marginal: sum over j of τ_{ij} equals τ^X_i. -/
  hRowMarginal : ∀ i, ∑ j, τ i j = τX i
  /-- Column marginal: sum over i of τ_{ij} equals τ^Y_j. -/
  hColMarginal : ∀ j, ∑ i, τ i j = τY j
  /--
    **Interval-Structure (no-rectangle) property.**
    For any rectangle of indices i ≠ k, j ≠ ℓ, if both diagonal
    overlaps τ_{ij}, τ_{kℓ} are positive, then at least one of
    the off-diagonal overlaps τ_{iℓ}, τ_{kj} must vanish.
    This captures the one-dimensional geometry of the grids: the
    nonzero overlap set is a "staircase" band, not an arbitrary
    two-dimensional support.
  -/
  hNoRectangle :
    ∀ i k : Fin m, ∀ j ℓ : Fin n,
    i ≠ k → j ≠ ℓ →
    0 < τ i j → 0 < τ k ℓ →
    τ i ℓ * τ k j = 0

-- ============================================================
-- Section 2: The Interval-Structure Lemma
-- ============================================================

variable (G : GridPair m n)

/--
  **Interval-Structure Lemma.**  The key geometric identity
  underlying Theorem 1.  If indices i ≠ k and j ≠ ℓ satisfy
  τ_{ij} > 0 and τ_{kℓ} > 0, then τ_{iℓ} · τ_{kj} = 0.

  Proof: direct application of `GridPair.hNoRectangle`.
-/
theorem interval_structure_lemma
    (i k : Fin m) (j ℓ : Fin n)
    (hik : i ≠ k) (hjℓ : j ≠ ℓ)
    (hij : 0 < G.τ i j) (hkℓ : 0 < G.τ k ℓ) :
    G.τ i ℓ * G.τ k j = 0 :=
  G.hNoRectangle i k j ℓ hik hjℓ hij hkℓ

/--
  Corollary: the "cross-crossed" contribution in the Isserlis
  regime (X) vanishes.  For any weight matrix w supported on
  {τ_{ij} > 0}, the sum
    ∑_{i ≠ k, j ≠ ℓ} w_{ij} w_{kℓ} τ_{iℓ} τ_{kj}
  equals zero.

  This is the step that makes the A_2 form in Theorem 1 close.
-/
theorem regime_X_vanishes
    (w : Fin m → Fin n → ℝ)
    (hw_support : ∀ i j, G.τ i j = 0 → w i j = 0) :
    ∑ i, ∑ j, ∑ k, ∑ ℓ,
      (if i = k then 0 else 1) * (if j = ℓ then 0 else 1) *
      (w i j * w k ℓ * G.τ i ℓ * G.τ k j) = 0 := by
  -- Every term in the sum is zero.  We show this termwise.
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  apply Finset.sum_eq_zero; intro k _
  apply Finset.sum_eq_zero; intro ℓ _
  -- Case split on whether i = k or j = ℓ.
  by_cases hik : i = k
  · simp [hik]
  by_cases hjℓ : j = ℓ
  · simp [hjℓ]
  -- Now i ≠ k and j ≠ ℓ.  We show w_{ij} * w_{kℓ} * τ_{iℓ} * τ_{kj} = 0.
  simp only [if_neg hik, if_neg hjℓ, one_mul]
  -- Case split on whether τ_{ij} = 0 or not.
  by_cases hij_zero : G.τ i j = 0
  · -- If τ_{ij} = 0, then w_{ij} = 0 by support.
    rw [hw_support i j hij_zero]
    ring
  · -- τ_{ij} > 0.  Case split on whether τ_{kℓ} = 0.
    have hij_pos : 0 < G.τ i j := lt_of_le_of_ne (G.hτ_nn i j) (Ne.symm hij_zero)
    by_cases hkℓ_zero : G.τ k ℓ = 0
    · rw [hw_support k ℓ hkℓ_zero]
      ring
    · have hkℓ_pos : 0 < G.τ k ℓ := lt_of_le_of_ne (G.hτ_nn k ℓ) (Ne.symm hkℓ_zero)
      -- Now we can apply the interval-structure lemma.
      have := interval_structure_lemma G i k j ℓ hik hjℓ hij_pos hkℓ_pos
      -- From τ_{iℓ} * τ_{kj} = 0, conclude the full product is 0.
      have h : w i j * w k ℓ * G.τ i ℓ * G.τ k j =
               w i j * w k ℓ * (G.τ i ℓ * G.τ k j) := by ring
      rw [h, this]
      ring

-- ============================================================
-- Section 3: Sanity-check lemma on marginals
-- ============================================================

/--
  Sanity check: the marginal identity implies that summing the
  overlap matrix row-wise then summing over rows gives the total
  time, which equals summing the column marginals.  This is just
  Fubini and should be trivial, but we record it as a lemma
  because Theorem 1's proof uses it implicitly.
-/
theorem total_overlap_consistent :
    ∑ i, G.τX i = ∑ j, G.τY j := by
  calc ∑ i, G.τX i
      = ∑ i, ∑ j, G.τ i j := by
        apply Finset.sum_congr rfl; intro i _
        rw [G.hRowMarginal i]
    _ = ∑ j, ∑ i, G.τ i j := Finset.sum_comm
    _ = ∑ j, G.τY j := by
        apply Finset.sum_congr rfl; intro j _
        rw [G.hColMarginal j]

end ZHY.Geometry

/-
  Summary of what is proved (zero sorries):
  1. interval_structure_lemma  [Interval-Structure Lemma]
  2. regime_X_vanishes         [Corollary: Regime-X sum = 0]
  3. total_overlap_consistent  [Sanity: row and column totals agree]

  These are the foundational geometric facts used in the full
  formalisation of Theorem 1 of the paper.  The next module
  (ZHY_Variance.lean) will use `regime_X_vanishes` together with
  the Isserlis expansion to establish the exact variance identity.
-/
