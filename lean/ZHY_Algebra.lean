/-
  ZHY Pure-Algebra Scaffolding
  =============================
  Yang Wu Azzollini (2026)

  Finset.sum identities used by ZHY_Variance.  No probability content:
  everything here is pure combinatorial algebra over Finset.

  Lemmas exported:
    · sum_square_off_diag       -- (∑ g)² - ∑ g² = ∑∑_{j≠l} g j · g l
    · sum_firstcase_collapse    -- same-i case
    · sum_secondcase_collapse   -- same-j case (symmetric)
    · sum_split_four            -- 4-fold sum partitions by (i=k, j=l) cases
-/

import Mathlib

open BigOperators Finset

namespace ZHY

variable {m n : ℕ}

-- ============================================================
-- Lemma 1: Square-off-diagonal collapse in one variable
-- ============================================================

/--
  Expansion of a squared sum into diagonal and off-diagonal parts.
  Equivalently: ∑ⱼ∑_{l ≠ j} g j · g l = (∑ g)² − ∑ g².
-/
lemma sum_square_off_diag
    (g : Fin n → ℝ) :
    (∑ j : Fin n, ∑ l : Fin n,
        if j = l then (0:ℝ) else g j * g l)
      = (∑ j : Fin n, g j) ^ 2 - ∑ j : Fin n, g j ^ 2 := by
  -- (∑ g)² = ∑ⱼ∑ₗ g j · g l.
  have sq_expand : (∑ j : Fin n, g j) ^ 2
        = ∑ j : Fin n, ∑ l : Fin n, g j * g l := by
    rw [sq, Finset.sum_mul_sum]
  -- Pointwise split of each g j · g l into diagonal-indicator + off-diagonal-indicator.
  have pointwise : ∀ j l : Fin n,
      g j * g l =
        (if j = l then g j ^ 2 else (0:ℝ)) +
        (if j = l then (0:ℝ) else g j * g l) := by
    intro j l
    by_cases h : j = l
    · subst h; simp; ring
    · simp [h]
  -- The product sum equals diagonal + off-diagonal.
  have split : (∑ j : Fin n, ∑ l : Fin n, g j * g l)
        = (∑ j : Fin n, ∑ l : Fin n,
              if j = l then g j ^ 2 else (0:ℝ)) +
          (∑ j : Fin n, ∑ l : Fin n,
              if j = l then (0:ℝ) else g j * g l) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => pointwise j l)
  -- The diagonal double sum collapses to ∑ⱼ g j².
  have diag_eq : (∑ j : Fin n, ∑ l : Fin n,
                    if j = l then g j ^ 2 else (0:ℝ))
               = ∑ j : Fin n, g j ^ 2 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Finset.sum_ite_eq']
  linarith [sq_expand, split, diag_eq]

-- ============================================================
-- Lemmas 2 and 3: "Same-i" and "same-j" collapses
-- ============================================================

/--
  Same-i off-diagonal collapse (thesis Theorem 5.1 "first case" algebra).

    ∑ᵢ ∑_{j ≠ l} h i j · h i l = ∑ᵢ (∑ⱼ h i j)² − ∑ᵢⱼ h i j².
-/
lemma sum_firstcase_collapse
    (h : Fin m → Fin n → ℝ) :
    (∑ i : Fin m, ∑ j : Fin n, ∑ l : Fin n,
        if j = l then (0:ℝ) else h i j * h i l)
      = (∑ i : Fin m, (∑ j : Fin n, h i j) ^ 2)
      - (∑ i : Fin m, ∑ j : Fin n, h i j ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact sum_square_off_diag (fun j => h i j)

/-- Same-j off-diagonal collapse (symmetric, "second case" algebra). -/
lemma sum_secondcase_collapse
    (h : Fin m → Fin n → ℝ) :
    (∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin m,
        if i = k then (0:ℝ) else h i j * h k j)
      = (∑ j : Fin n, (∑ i : Fin m, h i j) ^ 2)
      - (∑ j : Fin n, ∑ i : Fin m, h i j ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact sum_square_off_diag (fun i => h i j)

-- ============================================================
-- Lemma 4: Four-way partition of a 4-fold sum
-- ============================================================

/--
  Partition of a 4-fold sum over `Fin m × Fin n × Fin m × Fin n` by the
  four mutually exclusive cases on `(i = k, j = l)`.

    ∑ᵢⱼₖₗ F i j k l
      = ∑ᵢⱼ F i j i j                                  -- diagonal
      + ∑ᵢⱼ ∑_{l ≠ j} F i j i l                         -- same-i, different-j
      + ∑ⱼᵢ ∑_{k ≠ i} F i j k j                         -- different-i, same-j
      + ∑ᵢⱼₖₗ [i ≠ k ∧ j ≠ l] F i j k l                -- both different

  Pure combinatorics; proved by pointwise partition + distribution of sums.
-/
lemma sum_split_four
    (F : Fin m → Fin n → Fin m → Fin n → ℝ) :
    (∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n, F i j k l)
      = (∑ i : Fin m, ∑ j : Fin n, F i j i j)
      + (∑ i : Fin m, ∑ j : Fin n, ∑ l : Fin n,
            if j = l then (0:ℝ) else F i j i l)
      + (∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin m,
            if i = k then (0:ℝ) else F i j k j)
      + (∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n,
            if i = k ∨ j = l then (0:ℝ) else F i j k l) := by
  -- Pointwise partition:
  --   F i j k l = [i=k∧j=l]·F + [i=k∧j≠l]·F + [i≠k∧j=l]·F + [i≠k∧j≠l]·F
  have pointwise : ∀ i j k l,
      F i j k l =
        (if i = k ∧ j = l then F i j k l else 0) +
        (if i = k ∧ j ≠ l then F i j k l else 0) +
        (if i ≠ k ∧ j = l then F i j k l else 0) +
        (if i ≠ k ∧ j ≠ l then F i j k l else 0) := by
    intro i j k l
    by_cases hik : i = k
    · by_cases hjl : j = l
      · subst hik; subst hjl; simp
      · subst hik; simp [hjl]
    · by_cases hjl : j = l
      · subst hjl; simp [hik]
      · simp [hik, hjl]
  -- Replace F i j k l pointwise by the four-term partition.
  rw [show (∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n, F i j k l)
        = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n,
            ((if i = k ∧ j = l then F i j k l else 0) +
             (if i = k ∧ j ≠ l then F i j k l else 0) +
             (if i ≠ k ∧ j = l then F i j k l else 0) +
             (if i ≠ k ∧ j ≠ l then F i j k l else 0)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact Finset.sum_congr rfl (fun l _ => pointwise i j k l)]
  -- Distribute the four indicator terms across the sum.
  simp only [Finset.sum_add_distrib]
  -- Now the LHS is (S₁ + S₂ + S₃) + S₄ where each Sₐ is a 4-fold sum.
  -- Match each against the target via `congr 1` (three times).
  congr 1
  congr 1
  congr 1
  · -- PIECE 1: (i=k ∧ j=l) piece equals ∑ᵢⱼ F i j i j.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- Show: ∑ₖ∑ₗ (if i=k ∧ j=l then F i j k l else 0) = F i j i j.
    -- Step: collapse ∑ₗ first (using l = j), then ∑ₖ (using k = i).
    rw [show (∑ k : Fin m, ∑ l : Fin n,
              if i = k ∧ j = l then F i j k l else (0:ℝ))
        = ∑ k : Fin m, (if i = k then F i j k j else (0:ℝ)) from ?_]
    · simp [Finset.sum_ite_eq']
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hik : i = k
      · subst hik
        -- Goal: ∑ₗ (if True ∧ j = l then F i j i l else 0) = if True then F i j i j else 0
        simp only [true_and, if_true]
        simp [Finset.sum_ite_eq']
      · -- hik : ¬ i = k.  Both sides reduce to 0.
        simp [hik]
  · -- PIECE 2: (i=k ∧ j≠l) piece equals ∑ᵢⱼ∑_{j≠l} F i j i l.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- Show: ∑ₖ∑ₗ (if i=k ∧ j≠l then F i j k l else 0) = ∑ₗ (if j=l then 0 else F i j i l).
    -- Swap to ∑ₗ∑ₖ, then collapse ∑ₖ via k = i.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hjl : j = l
    · -- j = l case: LHS has j ≠ l false, so ∑ₖ 0 = 0; RHS is (if j=l then 0 else ...) = 0.
      simp [hjl]
    · -- j ≠ l case: indicator reduces to `i = k`.
      rw [show (∑ k : Fin m, if i = k ∧ j ≠ l then F i j k l else (0:ℝ))
          = ∑ k : Fin m, if i = k then F i j k l else (0:ℝ) from by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          simp [hjl]]
      simp [Finset.sum_ite_eq', hjl]
  · -- PIECE 3: (i≠k ∧ j=l) piece equals ∑ⱼᵢ∑_{i≠k} F i j k j.
    -- The target is indexed in (j, i, k) order; the LHS is in (i, j, k, l).
    -- Swap the outer two sums via Finset.sum_comm.
    rw [show (∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin n,
                if i ≠ k ∧ j = l then F i j k l else (0:ℝ))
          = ∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin m, ∑ l : Fin n,
                if i ≠ k ∧ j = l then F i j k l else (0:ℝ) from
          Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- Show: ∑ₗ (if i≠k ∧ j=l then F i j k l else 0) = if i=k then 0 else F i j k j.
    by_cases hik : i = k
    · -- i = k case: LHS has i ≠ k false, so ∑ₗ 0 = 0.  RHS is 0.
      simp [hik]
    · -- i ≠ k case: indicator reduces to `j = l`.
      rw [show (∑ l : Fin n, if i ≠ k ∧ j = l then F i j k l else (0:ℝ))
          = ∑ l : Fin n, if j = l then F i j k l else (0:ℝ) from by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          simp [hik]]
      simp [Finset.sum_ite_eq', hik]
  · -- PIECE 4: (i≠k ∧ j≠l) piece.  Rewrite the indicator `i≠k ∧ j≠l` as
    -- `¬(i=k ∨ j=l)`, matching the target form `if i=k ∨ j=l then 0 else F`.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hik : i = k
    · simp [hik]
    · by_cases hjl : j = l
      · simp [hik, hjl]
      · simp [hik, hjl]

end ZHY
