# Exact Finite-Sample Variance of the Weighted ZHY Estimator

**Dr Yang Azzollini** — DPhil Statistics, University of Oxford

---

## The Result

For two assets observed asynchronously at arbitrary times, the
weighted Zhou–Hayashi–Yoshida covariance estimator

$$\hat{\sigma}_{12}(\mathbf{w}) = \frac{\sum_{ij} R_i S_j w_{ij} \,\mathbf{1}(\tau_{ij}>0)}{T(\mathbf{w})}$$

has **exact** finite-sample conditional variance

$$\boxed{\operatorname{Var}(\hat{\sigma}_{12} \mid \tau) = \sigma_1^2\sigma_2^2\, A_1(\mathbf{w}) + \sigma_{12}^2\, A_2(\mathbf{w})}$$

where $A_1$ and $A_2$ are explicit functions of the overlap structure
$\{\tau_{ij}\}$. This is **exact** (not asymptotic), holds for **any
fixed timestamps**, and requires no distributional assumption on
observation times beyond independence from prices.

The optimal weights $w_{ij}^* = \tau_{ij}/(\tau_i^X \tau_j^Y)$
minimise $A_1$, giving $A_1(\mathbf{w}^*) = 1/\Theta$ where
$\Theta = \sum_{ij} \tau_{ij}^2 / (\tau_i^X \tau_j^Y)$.

**The optimal ZHY estimator improves on naive 5-minute
synchronisation by 3.8× on simulated crypto tick data.**

---

## New Results (2026)

Beyond the thesis, this repository contains three new theorems:

| Theorem | Statement |
|---------|-----------|
| **Theorem 2** | Full-variance optimal weights via $(K+1)\times(K+1)$ KKT system |
| **Theorem 3** | Two-step estimator is BLUE within the weighted ZHY class |
| **Theorem 4** | Asynchronous Gauss–Markov: two-step achieves Cramér–Rao at $\rho=0$ |

---

## Formal Verification in Lean 4

The core algebraic results are formally verified using
[Lean 4](https://lean-lang.org/) and
[Mathlib](https://leanprover-community.github.io/mathlib4_docs/):

```
lean/
├── ZHY_Core.lean     — 5 theorems, zero sorries  (commit 2939dd37)
│   ├── lemma41_unbiased_iff      Lemma 4.1: unbiased ↔ Σ c_ij τ_ij = 1
│   ├── nonOverlapping_irrelevant  non-overlapping pairs irrelevant
│   ├── zhy_unbiased               normalised ZHY is unbiased
│   ├── A1_optimal_explicit        T(w*) = Θ at optimal weights
│   └── CR_equality_at_zero        FI · Var_min = 1 at ρ=0
│
├── ZHY_BLUE.lean     — 3 theorems, zero sorries  (commit f4c8ce21)
│   ├── BLUE_A1        A₁(c) ≥ 1/Θ for all unbiased c  [Cauchy-Schwarz]
│   ├── A1_opt_eq      A₁(w*) numerator = Θ
│   └── BLUE_A1_sharp  A₁(w*) = 1/Θ  [sharp bound]
│
└── ZHY_Isserlis.lean — Isserlis theorem calculation for Theorem 1
```

**To build:**
```bash
cd lean
lake exe cache get   # downloads precompiled Mathlib (~15 min)
lake build ZHY_Core
lake build ZHY_BLUE
```

---

## Implementation

### Python (academic)
```bash
cd code
python crypto_demo.py      # ZHY on 5 simulated crypto assets
python plot_results.py     # reproduce the comparison figure
```

| Method | Frobenius Error | Improvement |
|--------|----------------|-------------|
| Naive 5-min synchronised | 0.2601 | — |
| Optimal ZHY (Theorem 1) | 0.0676 | **3.8×** |
| Precision-weighted shrinkage | 0.0674 | **3.9×** |

### K/KDB+ (production)
```q
\l trading/k/zhy.k
test[]              / verify with simulated data
testmr[]            / test mean-reversion strategy
```

The K engine computes the full overlap matrix $\{\tau_{ij}\}$ and
optimal ZHY estimate in vectorised form — no loops.

### Interactive Brokers (live trading)
```bash
cd trading/python
pip install -r requirements.txt
python zhy_mr_ib.py --paper    # paper trading, ES vs NQ
```

The trading system calibrates the lead-lag between ES and NQ
at minute timescale (daily recalibration), trades mean-reversion
of the spread $Z(t) = \text{NQ}(t) - \alpha - \beta\cdot\text{ES}(t-h^*)$,
and sizes positions using the exact variance from Theorem 1.

---

## Repository Structure

```
Paper_2026/
├── paper/                  LaTeX sections
│   ├── theorems_summary.pdf   2-page theorem statements
│   └── sections/              KKT system, Gauss-Markov theorem
├── lean/                   Lean 4 formal proofs
│   ├── ZHY_Core.lean
│   ├── ZHY_BLUE.lean
│   └── ZHY_Isserlis.lean
├── code/                   Python implementation
│   ├── zhy_estimator.py
│   └── crypto_demo.py
└── trading/                K/KDB+ + IB trading system
    ├── k/zhy.k
    ├── k/zhy_meanrev.k
    └── python/zhy_mr_ib.py
```

---

## Background

University of Oxford: BA Mathematics & Computer Science (St Hugh's
College), MSc Applied Statistics (supervised by Professor Brian D.
Ripley), DPhil Statistics (Lady Margaret Hall, supervised by
Professor Brian D. Ripley and Dr Peter Clifford).

Prior to the DPhil: ten-plus years in quantitative research at a
leading international investment bank, developing and trading
high-frequency statistical arbitrage strategies.

---

## Contact

`yang.maths@gmail.com`

*Working paper available on request.*
