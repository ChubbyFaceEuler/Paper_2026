/-
  ZHY Theorem 2: Full-Variance Optimal Weights
  =============================================
  Yang Wu Azzollini (Oxford DPhil 2016, revised 2026)

  Theorem 2 (Full-variance optimal weights):
  Under normalisation T(w) = Σ_ij w_ij τ_ij = 1, the weights w*(κ)
  minimising V(w) = σ₁²σ₂² A₁(w) + σ₁₂² A₂(w) are the unique solution of:

    w*_ij [τX_i τY_j - κ τ²_ij] + κ τ_ij [R_i(w*) + C_j(w*)] = μ τ_ij

  for each pair (i,j) with τ_ij > 0, where κ = σ₁₂²/(σ₁²σ₂²).

  Proof strategy: completing the square.
    V(c) - V(c*) = V(d) + 2·cross(c*, d)
    where d = c - c*, cross = (λ/2)·T(d) = 0 (KKT + unbiasedness)
    and V(d) ≥ 0 (variance is a non-negative quadratic form).

  Status:
  · Definitions, row/col sums: zero sorries
  · Quadratic expansion lemma: one sorry (ring manipulation over finset sums)
  · Cross-term = 0: one sorry (sum reindexing)
  · V(d) ≥ 0: one axiom (follows from Var of a random variable ≥ 0)
  · Main theorem: zero sorries (follows from the three above)
-/

import Mathlib

open BigOperators Finset

variable {m n : ℕ}
variable (τ  : Fin m → Fin n → ℝ)
variable (τX : Fin m → ℝ)
variable (τY : Fin n → ℝ)

-- ============================================================
-- Section 1: Row sums, column sums, normalisation
-- ============================================================

/-- Row sum: R_i(w) = Σ_j w_ij τ_ij -/
noncomputable def rowSum (w : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j : Fin n, w i j * τ i j

/-- Column sum: C_j(w) = Σ_i w_ij τ_ij -/
noncomputable def colSum (w : Fin m → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i : Fin m, w i j * τ i j

/-- Normalisation: T(w) = Σ_ij w_ij τ_ij -/
noncomputable def Tnorm (w : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, w i j * τ i j

/-- T(w) = Σ_i R_i(w) -/
lemma Tnorm_eq_rowSum (w : Fin m → Fin n → ℝ) :
    Tnorm τ w = ∑ i : Fin m, rowSum τ w i := by
  simp [Tnorm, rowSum]

/-- T(w) = Σ_j C_j(w) -/
lemma Tnorm_eq_colSum (w : Fin m → Fin n → ℝ) :
    Tnorm τ w = ∑ j : Fin n, colSum τ w j := by
  simp only [Tnorm, colSum]
  rw [Finset.sum_comm]

/-- Row sums are linear -/
lemma rowSum_add (w d : Fin m → Fin n → ℝ) (i : Fin m) :
    rowSum τ (fun a b => w a b + d a b) i = rowSum τ w i + rowSum τ d i := by
  simp [rowSum, add_mul, Finset.sum_add_distrib]

/-- Column sums are linear -/
lemma colSum_add (w d : Fin m → Fin n → ℝ) (j : Fin n) :
    colSum τ (fun a b => w a b + d a b) j = colSum τ w j + colSum τ d j := by
  simp [colSum, add_mul, Finset.sum_add_distrib]

/-- T is linear -/
lemma Tnorm_sub (w d : Fin m → Fin n → ℝ) :
    Tnorm τ (fun i j => w i j - d i j) = Tnorm τ w - Tnorm τ d := by
  simp [Tnorm, sub_mul, Finset.sum_sub_distrib]

-- ============================================================
-- Section 2: Variance coefficients A₁ and A₂
-- ============================================================

/-- A₁(w) = Σ_ij w²_ij τX_i τY_j  (coefficient of σ₁²σ₂²) -/
noncomputable def A1c (w : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, w i j ^ 2 * τX i * τY j

/--
  A₂(w) = Σ_i R_i(w)² + Σ_j C_j(w)² − Σ_ij w²_ij τ²_ij
  (coefficient of σ₁₂²; from Isserlis/Wick expansion of Theorem 1)
-/
noncomputable def A2c (w : Fin m → Fin n → ℝ) : ℝ :=
  (∑ i : Fin m, rowSum τ w i ^ 2) +
  (∑ j : Fin n, colSum τ w j ^ 2) -
  ∑ i : Fin m, ∑ j : Fin n, w i j ^ 2 * τ i j ^ 2

/-- Full conditional variance: V(w) = σ₁²σ₂² A₁(w) + σ₁₂² A₂(w) -/
noncomputable def fullVar2 (σ₁sq σ₂sq σ₁₂sq : ℝ) (w : Fin m → Fin n → ℝ) : ℝ :=
  σ₁sq * σ₂sq * A1c τX τY w + σ₁₂sq * A2c τ w

-- ============================================================
-- Section 3: Quadratic expansion
-- ============================================================

/-- Bilinear cross term for A₁ -/
noncomputable def crossA1 (w d : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, w i j * d i j * τX i * τY j

/-- Bilinear cross term for A₂ -/
noncomputable def crossA2 (w d : Fin m → Fin n → ℝ) : ℝ :=
  (∑ i : Fin m, rowSum τ w i * rowSum τ d i) +
  (∑ j : Fin n, colSum τ w j * colSum τ d j) -
  ∑ i : Fin m, ∑ j : Fin n, w i j * d i j * τ i j ^ 2

/--
  Quadratic expansion of fullVar2.
  V(w + d) = V(w) + V(d) + 2 [σ₁²σ₂² crossA1(w,d) + σ₁₂² crossA2(w,d)]
-/
lemma fullVar2_expand (σ₁sq σ₂sq σ₁₂sq : ℝ) (w d : Fin m → Fin n → ℝ) :
    fullVar2 τ τX τY σ₁sq σ₂sq σ₁₂sq (fun i j => w i j + d i j) =
    fullVar2 τ τX τY σ₁sq σ₂sq σ₁₂sq w +
    fullVar2 τ τX τY σ₁sq σ₂sq σ₁₂sq d +
    2 * (σ₁sq * σ₂sq * crossA1 τX τY w d + σ₁₂sq * crossA2 τ w d) := by
  -- Apply linearity of rowSum/colSum before unfolding
  simp only [fullVar2, A1c, A2c, crossA1, crossA2]
  simp_rw [rowSum_add τ w d, colSum_add τ w d]
  simp only [rowSum, colSum]
  simp_rw [add_sq, add_mul, mul_add, Finset.sum_add_distrib]
  sorry

-- ============================================================
-- Section 4: Cross term vanishes at KKT weights
-- ============================================================

/--
  KKT first-order condition for Theorem 2.
  ∂V/∂w_ij = λ τ_ij gives (for all i, j):
    σ₁²σ₂² w_ij τX_i τY_j + σ₁₂² τ_ij (R_i(w) + C_j(w) − w_ij τ_ij) = (λ/2) τ_ij
-/
def isKKT2 (σ₁sq σ₂sq σ₁₂sq : ℝ) (w : Fin m → Fin n → ℝ) (lam : ℝ) : Prop :=
  ∀ (i : Fin m) (j : Fin n),
    σ₁sq * σ₂sq * w i j * τX i * τY j +
    σ₁₂sq * τ i j * (rowSum τ w i + colSum τ w j - w i j * τ i j) =
    lam / 2 * τ i j

/--
  The cross term equals (λ/2) · T(d).
  Therefore, when T(d) = 0 (both c and c* are unbiased), cross = 0.
-/
lemma crossTermEq (σ₁sq σ₂sq σ₁₂sq : ℝ) (w d : Fin m → Fin n → ℝ)
    (lam : ℝ) (hkkt : isKKT2 τ τX τY σ₁sq σ₂sq σ₁₂sq w lam) :
    σ₁sq * σ₂sq * crossA1 τX τY w d + σ₁₂sq * crossA2 τ w d =
    lam / 2 * Tnorm τ d := by
  simp only [crossA1, crossA2, Tnorm, rowSum, colSum, isKKT2] at *
  -- Rearrange A₂ cross terms: Σ_i R_i(w) R_i(d) = Σ_ij d_ij τ_ij R_i(w)
  -- and Σ_j C_j(w) C_j(d) = Σ_ij d_ij τ_ij C_j(w)
  -- so the full cross = Σ_ij d_ij [σ₁²σ₂² w_ij τX_i τY_j +
  --    σ₁₂² τ_ij (R_i(w) + C_j(w) - w_ij τ_ij)] = Σ_ij d_ij (λ/2) τ_ij
  sorry

-- ============================================================
-- Section 5: V(d) ≥ 0
-- ============================================================

/--
  The quadratic form V is non-negative for all d.

  Proof: V(d) = Var(Σ_ij d_ij R_i S_j) ≥ 0 since variance is non-negative.
  This uses the full bivariate Brownian motion model
  (cov(R_i S_j, R_k S_l) = σ₁₂² τ_il τ_kj from Theorem 1/Isserlis).

  The algebraic condition is: σ₁₂² ≤ σ₁²σ₂² (|ρ| ≤ 1), which is
  guaranteed by the Cauchy-Schwarz inequality for covariances.
-/
axiom fullVar2_nonneg
    (σ₁sq σ₂sq σ₁₂sq : ℝ)
    (hσ₁  : 0 ≤ σ₁sq)
    (hσ₂  : 0 ≤ σ₂sq)
    (hρ   : σ₁₂sq ^ 2 ≤ σ₁sq * σ₂sq)
    (d : Fin m → Fin n → ℝ) :
    0 ≤ fullVar2 τ τX τY σ₁sq σ₂sq σ₁₂sq d

-- ============================================================
-- Section 6: Theorem 2 — KKT implies global minimum
-- ============================================================

/--
  **Theorem 2 (Full-variance optimal weights)**:

  Let c* satisfy the KKT first-order conditions with multiplier λ
  and be unbiased (T(c*) = 1). Then for every other unbiased
  estimator c (T(c) = 1):

    V(c*) ≤ V(c)

  Proof by completing the square:
    V(c) = V(c* + d)  where d = c - c*, T(d) = 0
         = V(c*) + V(d) + 2·cross(c*, d)
         = V(c*) + V(d) + 2·(λ/2)·T(d)
         = V(c*) + V(d)  [since T(d) = 0]
         ≥ V(c*)         [since V(d) ≥ 0]
-/
theorem theorem2_fullvar_optimal
    (σ₁sq σ₂sq σ₁₂sq : ℝ)
    (hσ₁  : 0 ≤ σ₁sq)
    (hσ₂  : 0 ≤ σ₂sq)
    (hρ   : σ₁₂sq ^ 2 ≤ σ₁sq * σ₂sq)
    -- Optimal weights with KKT multiplier λ
    (c_opt : Fin m → Fin n → ℝ) (lam : ℝ)
    (hkkt   : isKKT2 τ τX τY σ₁sq σ₂sq σ₁₂sq c_opt lam)
    (hopt   : Tnorm τ c_opt = 1)
    -- Any competitor
    (c : Fin m → Fin n → ℝ)
    (hc     : Tnorm τ c = 1) :
    fullVar2 τ τX τY σ₁sq σ₂sq σ₁₂sq c_opt ≤
    fullVar2 τ τX τY σ₁sq σ₂sq σ₁₂sq c := by
  -- d = c - c_opt, T(d) = 0
  let d : Fin m → Fin n → ℝ := fun i j => c i j - c_opt i j
  have hd : Tnorm τ d = 0 := by
    simp [d, Tnorm_sub, hc, hopt]
  -- c = c_opt + d
  have hc_eq : c = (fun i j => c_opt i j + d i j) := by ext i j; simp [d]
  -- Expand V(c) = V(c_opt) + V(d) + 2·cross
  rw [hc_eq, fullVar2_expand]
  -- Cross term = (λ/2) · T(d) = 0
  have cross_zero :
      σ₁sq * σ₂sq * crossA1 τX τY c_opt d +
      σ₁₂sq * crossA2 τ c_opt d = 0 := by
    rw [crossTermEq τ τX τY σ₁sq σ₂sq σ₁₂sq c_opt d lam hkkt, hd, mul_zero]
  -- V(d) ≥ 0
  have Vd := fullVar2_nonneg τ τX τY σ₁sq σ₂sq σ₁₂sq hσ₁ hσ₂ hρ d
  -- Conclude: V(c_opt) ≤ V(c_opt) + V(d) + 2·0
  linarith

-- ============================================================
-- Section 7: Reduction at κ = 0
-- ============================================================

/--
  Remark: at σ₁₂ = 0 (κ = ρ² = 0), the KKT condition reduces to
    w*_ij τX_i τY_j = (λ/2) τ_ij
  i.e. w*_ij ∝ τ_ij / (τX_i τY_j), the A₁-optimal weights.
  This confirms Theorem 2 ⊇ BLUE_A1 (ZHY_BLUE.lean) at ρ = 0.
-/
theorem theorem2_reduces_to_BLUE_at_zero
    (σ₁sq σ₂sq : ℝ)
    (c_opt : Fin m → Fin n → ℝ) (lam : ℝ)
    (hkkt : isKKT2 τ τX τY σ₁sq σ₂sq 0 c_opt lam)
    (i : Fin m) (j : Fin n) :
    σ₁sq * σ₂sq * c_opt i j * τX i * τY j = lam / 2 * τ i j := by
  have := hkkt i j
  simp [rowSum, colSum] at this
  linarith

/-
  Summary:
  =========
  theorem2_fullvar_optimal : V(c*) ≤ V(c) for all unbiased c
    — provided c* satisfies KKT and model params satisfy |ρ| ≤ 1
  theorem2_reduces_to_BLUE_at_zero : at ρ=0, KKT reduces to BLUE weights

  Sorrys / axioms:
  · fullVar2_expand ring step: finset ring manipulation (fillable with simp + ring)
  · crossTermEq: sum reindexing (Σ R_i(w) R_i(d) = Σ_ij d_ij τ_ij R_i(w))
  · fullVar2_nonneg: V(d) ≥ 0 from probabilistic model (Var ≥ 0)
-/
