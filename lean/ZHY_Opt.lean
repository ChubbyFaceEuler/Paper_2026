/-
  ZHY Optimal Weights: Lean 4 Formalisation
  ==========================================
  Dr Yang Azzollini (Oxford DPhil 2016, revised 2026)

  Formalises Theorems 2 and 3:

  Theorem 2 (Full-Variance Optimal Weights):
    The weights minimising V(w) = σ₁²σ₂² A₁(w) + σ₁₂² A₂(w)
    subject to T(w) = 1 satisfy the KKT system.

  Theorem 3 (Two-Step Efficiency):
    For fixed κ = ρ², the weights w*(κ) minimise V(w)
    over all normalised weight matrices.

  Proof strategy for KKT sufficiency:
    V(w) is a quadratic form in w. We prove sufficiency directly:
    for any feasible v with T(v)=1, expand V(v) - V(w*) and show
    it is a sum of non-negative terms using the KKT conditions.
    This avoids the need to prove global convexity of A2_num,
    which is not convex in general (only V = A1 + κ·A2 is convex
    for κ ∈ [0,1] due to the combined Hessian being PSD).
-/

import Mathlib

open BigOperators Finset Real

variable {m n : ℕ}
variable (τ  : Fin m → Fin n → ℝ)
variable (τX : Fin m → ℝ)
variable (τY : Fin n → ℝ)
variable (κ  : ℝ)

-- ============================================================
-- Definitions
-- ============================================================

noncomputable def T_ZHY (w : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, w i j * τ i j

noncomputable def A1_num (w : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, w i j ^ 2 * τX i * τY j

noncomputable def Rrow (w : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j : Fin n, w i j * τ i j

noncomputable def Ccol (w : Fin m → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i : Fin m, w i j * τ i j

noncomputable def A2_num (w : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, Rrow τ w i ^ 2
  + ∑ j : Fin n, Ccol τ w j ^ 2
  - ∑ i : Fin m, ∑ j : Fin n, w i j ^ 2 * τ i j ^ 2

noncomputable def V_obj (w : Fin m → Fin n → ℝ) : ℝ :=
  A1_num τX τY w + κ * A2_num τ w

noncomputable def Theta : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, τ i j ^ 2 / (τX i * τY j)

-- ============================================================
-- Lemma: T_ZHY is linear
-- ============================================================

lemma T_ZHY_linear (w₁ w₂ : Fin m → Fin n → ℝ) (a b : ℝ) :
    T_ZHY τ (fun i j => a * w₁ i j + b * w₂ i j) =
    a * T_ZHY τ w₁ + b * T_ZHY τ w₂ := by
  simp only [T_ZHY]
  simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc]
  simp [Finset.mul_sum, mul_comm]

-- ============================================================
-- Lemma: A1_num is non-negative
-- ============================================================

lemma A1_num_nonneg
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (w : Fin m → Fin n → ℝ) :
    0 ≤ A1_num τX τY w := by
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  apply mul_nonneg; apply mul_nonneg
  · positivity
  · exact le_of_lt (hτX i)
  · exact le_of_lt (hτY j)

-- ============================================================
-- Lemma: A1_num is convex
-- ============================================================

lemma A1_num_convex
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j) :
    ConvexOn ℝ Set.univ (A1_num τX τY) := by
  -- A1_num(w) = Σ_ij (w_ij)² · (τX_i · τY_j)
  -- Each term is w ↦ w_ij² · c_ij where c_ij > 0
  -- This is a positively weighted sum of convex functions
  -- Each term w ↦ w_ij² · (τX_i · τY_j) is convex (square × pos const)
  -- ConvexOn.sum not available in this Mathlib build; full proof needs Pi.normedSpace
  sorry

-- ============================================================
-- Lemma: The partial derivative of V at w* equals μ · τ_ij
-- (This is the key step for KKT sufficiency)
-- ============================================================

/-- The gradient condition: for V(w) = A1_num + κ·A2_num,
    the partial derivative ∂V/∂w_ij at w* is:
      2 w*_ij (τX_i τY_j - κ τ_ij²) + 2κ τ_ij (R_i + C_j)
    The KKT condition says this equals 2μ τ_ij. -/
def KKT_condition (w : Fin m → Fin n → ℝ) (μ : ℝ) : Prop :=
  ∀ i : Fin m, ∀ j : Fin n,
    0 < τ i j →
    w i j * (τX i * τY j - κ * τ i j ^ 2)
    + κ * τ i j * (Rrow τ w i + Ccol τ w j)
    = μ * τ i j

-- ============================================================
-- Theorem 2: w* satisfies KKT at κ = 0
-- ============================================================

noncomputable def w_opt_zero : Fin m → Fin n → ℝ :=
  fun i j => τ i j / (τX i * τY j)

theorem KKT_at_kappa_zero
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j) :
    KKT_condition τ τX τY 0 (w_opt_zero τ τX τY) 1 := by
  -- At κ=0: w*_ij · τX_i · τY_j = 1 · τ_ij, i.e. τ_ij/(τX_i τY_j) · τX_i τY_j = τ_ij ✓
  intro i j _
  simp only [w_opt_zero, zero_mul, sub_zero, one_mul, add_zero]
  exact div_mul_cancel₀ (τ i j) (ne_of_gt (mul_pos (hτX i) (hτY j)))

-- ============================================================
-- Key Lemma: V(v) - V(w) ≥ 0 when w satisfies KKT
-- Direct algebraic proof via completing the square
-- ============================================================

/-- For any quadratic objective V and feasible w satisfying KKT,
    V(v) - V(w) = V(v-w) ≥ 0 (using linearity of constraint).
    This is the direct proof of KKT sufficiency for quadratic V.

    Proof: Let d = v - w. Then T(d) = T(v) - T(w) = 0.
    V(v) = V(w + d) = V(w) + 2·⟨∇V(w), d⟩ + V(d)
    where ⟨∇V(w), d⟩ = Σ_ij (∂V/∂w_ij) · d_ij
                       = Σ_ij 2μ τ_ij · d_ij   (by KKT)
                       = 2μ · T(d) = 0

    So V(v) - V(w) = V(d) ≥ 0 iff V is non-negative on {T=0}.
-/
lemma V_diff_nonneg
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (w v : Fin m → Fin n → ℝ) (μ : ℝ)
    (hTw : T_ZHY τ w = 1) (hTv : T_ZHY τ v = 1)
    (hKKT : KKT_condition τ τX τY κ w μ) :
    V_obj τ τX τY κ w ≤ V_obj τ τX τY κ v := by
  sorry
  /- Proof outline:
     Let d_ij = v_ij - w_ij. Then Σ d_ij τ_ij = 0.

     V(v) - V(w) = A1_num(v) - A1_num(w) + κ·(A2_num(v) - A2_num(w))

     For A1_num:
       A1_num(v) - A1_num(w)
       = Σ (v_ij² - w_ij²) τX_i τY_j
       = Σ (d_ij² + 2 w_ij d_ij) τX_i τY_j
       = A1_num(d) + 2 Σ w_ij d_ij τX_i τY_j

     For A2_num (similar expansion):
       A2_num(v) - A2_num(w) = A2_num(d) + 2·cross_term

     The cross term from KKT:
       Σ_ij (∂V/∂w_ij) · d_ij = Σ_ij 2μ τ_ij d_ij = 2μ · T(d) = 0

     So V(v) - V(w) = V(d) where T(d) = 0.

     Need: V(d) ≥ 0 for all d with T(d) = 0.
     This requires showing V is non-negative on the null space of T,
     which follows from the Hessian of V being PSD on this subspace.
     The Hessian of A1_num is diag(τX_i τY_j) > 0.
     The Hessian of A2_num on null(T) is PSD iff κ ≤ critical value.
     For κ ∈ [0,1] this holds (numerical evidence from thesis).
  -/

-- ============================================================
-- Theorem 3: KKT_sufficient
-- ============================================================

theorem KKT_sufficient
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (w : Fin m → Fin n → ℝ) (μ : ℝ)
    (hT : T_ZHY τ w = 1)
    (hKKT : KKT_condition τ τX τY κ w μ) :
    ∀ v : Fin m → Fin n → ℝ, T_ZHY τ v = 1 →
    V_obj τ τX τY κ w ≤ V_obj τ τX τY κ v :=
  fun v hTv => V_diff_nonneg τ τX τY κ hτX hτY hκ hκ1 w v μ hT hTv hKKT

theorem two_step_efficiency
    (hτX : ∀ i, 0 < τX i) (hτY : ∀ j, 0 < τY j)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (w_star : Fin m → Fin n → ℝ) (μ : ℝ)
    (hT : T_ZHY τ w_star = 1)
    (hKKT : KKT_condition τ τX τY κ w_star μ) :
    ∀ w : Fin m → Fin n → ℝ, T_ZHY τ w = 1 →
    V_obj τ τX τY κ w_star ≤ V_obj τ τX τY κ w :=
  KKT_sufficient τ τX τY κ hτX hτY hκ hκ1 w_star μ hT hKKT

/-
  Summary:
  ========
  T_ZHY_linear       : T is linear                          [proved ✓]
  A1_num_nonneg      : A₁ ≥ 0                               [proved ✓]
  A1_num_convex      : A₁ is convex                         [sorry - Pi space sq convex]
  KKT_at_kappa_zero  : w* satisfies KKT at κ=0              [proved ✓]
  V_diff_nonneg      : V(v) - V(w*) ≥ 0 via quadratic expand[sorry - Hessian PSD on null(T)]
  KKT_sufficient     : follows from V_diff_nonneg            [sorry - inherited]
  two_step_efficiency: Theorem 3                             [sorry - inherited]

  Remaining mathematical gap:
  The key sorry is V_diff_nonneg, which requires showing that
  the Hessian of V restricted to the null space of T is PSD.
  For A1_num this is immediate (diagonal, positive entries).
  For A2_num on null(T) this requires a spectral argument.
  This is the core mathematical content of Theorem 2.
-/
