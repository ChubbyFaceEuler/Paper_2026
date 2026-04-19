# Running the Lean 4 Proof

## Prerequisites

Install Lean 4 via elan (the Lean version manager):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source ~/.profile
```

Verify installation:
```bash
lean --version   # should print leanprover/lean4:v4.x.x
lake --version
```

## Setup

```bash
cd ~/Documents/Paper_2026

# Download Mathlib cache (saves ~2 hours of compilation)
lake exe cache get

# Build the project
lake build ZHY_Core
```

Expected output:
```
Building ZHY.ZHY_Core
```
No errors, no warnings (other than unused variable hints).

## What is proved (zero sorries)

| Theorem | Statement |
|---------|-----------|
| `lemma41_unbiased_iff` | Cross-product estimator unbiased ↔ Σ c_ij τ_ij = 1 |
| `nonOverlapping_irrelevant` | Non-overlapping pairs irrelevant to unbiasedness |
| `zhy_unbiased` | Normalised ZHY estimator is unbiased |
| `A1_optimal_explicit` | T(w*) = Θ at optimal weights |
| `CR_equality_at_zero` | FI · Var_min = 1 at ρ=0 (Cramér-Rao achieved) |

## Mathematical context

These are the core algebraic results of:

> Yang Wu Azzollini. "Exact Finite-Sample Variance of the Weighted
> ZHY Estimator with Optimal Weights and Asynchronous Gauss-Markov
> Optimality." Working paper, 2026.

The single probabilistic hypothesis is:
  E[R_i · S_j] = σ₁₂ · τ_ij
which follows from bivariate Brownian motion + Itô isometry.
All five theorems are proved from this axiom using only algebra.

## Troubleshooting

If `lake exe cache get` fails:
```bash
lake build   # compiles from scratch, takes ~30-60 min
```

If you see `unknown identifier 'Finset.sum_div'`:
```bash
lake update   # update to latest Mathlib
lake exe cache get
lake build ZHY_Core
```
