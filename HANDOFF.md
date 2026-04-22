# ZHY Paper Project — Handoff Document
## Date: April 22, 2026 (updated late evening, after Theorem 5.1 formalisation)
## For: Dr Yang Azzollini

---

## Who You Are

Oxford DPhil Statistics (Lady Margaret Hall), supervised by Brian D. Ripley
(MSc) and Brian D. Ripley + Peter Clifford (DPhil). BA Mathematics &
Computer Science, St Hugh's College. Ten-plus years quantitative researcher
at a leading international investment bank. Currently in Saratoga CA.
Contact: yang.maths@gmail.com

---

## The Core Result — Honest Framing

Be careful in the paper and in conversation to separate what's from 2016
and what's genuinely new in 2026.

### From the 2016 DPhil thesis (Chapter 5)

- **Theorem 5.1 — exact finite-sample variance decomposition.**
  `Var(∑ᵢⱼ wᵢⱼ RᵢSⱼ | τ) = σ₁²σ₂² · A₁(w) + σ₁₂² · A₂(w)`
  where `A₁` and `A₂` are explicit functions of the overlap structure
  `{τᵢⱼ}`. Exact, not asymptotic, no distributional assumption on the
  observation times beyond the geometric disjointness of consecutive
  return intervals.

- **Interval-Structure Lemma.** The proof of Theorem 5.1 on page 108
  uses the fact that, for `i ≠ k` and `j ≠ l`, the overlaps `τᵢₗ` and
  `τₖⱼ` cannot both be positive. This is explicit in the thesis:
  "both J^X_i and J^X_k must intersect both J^Y_j and J^Y_l which is
  impossible since J^X_i and J^X_k are disjoint, as are J^Y_j and J^Y_l."

- **A₁-optimal weights.** The Lagrangian derivation gives
  `w*ᵢⱼ = τᵢⱼ / (τXᵢ · τYⱼ)`.

- **Theorem 5.2.** Extension to the noise model with three D-terms.

### New in the 2026 work

- **Theorem 2 — Full-variance optimal weights via (K+1)×(K+1) KKT system.**
  Extends the A₁-only optimum to general `κ = σ₁₂² / (σ₁² σ₂²)`.

- **Theorem 3 — Two-step plug-in estimator is BLUE within the weighted ZHY class.**

- **Theorem 4 — Asynchronous Gauss-Markov / Cramér-Rao.**
  The ZHY optimal estimator attains the Cramér-Rao bound at `ρ = 0`,
  reframing A₁ optimality in information-theoretic terms.

- **Lean 4 formalisation.** Theorems 1, 4, 5.1, and the BLUE result
  now have machine-checked proofs (see "Lean 4 Status" below).

### Positioning for the paper

"We give the first explicit derivation of an exact finite-sample,
timestamp-conditional variance for the weighted ZHY class of
estimators, derive the full BLUE-optimal weights under general
correlation, and provide a machine-checked Lean 4 formalisation of
the variance decomposition. This offers a rigorous alternative to the
asymptotic approximations of Hayashi-Yoshida (2008) and Griffin-Oomen
(2011)."

---

## Repository

**Location:** ~/Documents/Paper_2026
**GitHub:** github.com/ChubbyFaceEuler/Paper_2026 (PUBLIC)

**Structure (current):**
```
Paper_2026/
├── HANDOFF.md                  ← this file
├── paper/
│   ├── theorems_summary.pdf    ← 2-page theorem statements for Yoshida
│   └── theorems_summary.tex
├── lean/
│   ├── ZHY_Core.lean           ← 5 theorems, ZERO SORRIES ✓
│   ├── ZHY_BLUE.lean           ← BLUE theorem at ρ=0, ZERO SORRIES ✓
│   ├── ZHY_Algebra.lean        ← pure-algebra scaffolding, 4 lemmas,
│   │                             ZERO SORRIES ✓ (2026-04-22)
│   ├── ZHY_Variance.lean       ← Theorem 5.1 formalisation, ZERO SORRIES ✓
│   │                             (2026-04-22)
│   ├── lakefile.lean
│   └── lean-toolchain          ← leanprover/lean4:v4.30.0-rc2
├── journal/                    ← JFEC submission (tight style)
│   └── sections/
│       ├── 01_introduction.tex ← DONE
│       └── 02_literature.tex   ← DONE
├── thesis_extended/            ← Book-style full exposition
│   └── chapters/               ← EMPTY — to be written
├── code/
│   ├── zhy_estimator.py        ← core Python implementation
│   └── crypto_demo.py          ← 5-coin simulation demo
└── trading/
    ├── k/zhy.k                 ← K engine, vectorised
    ├── k/zhy_meanrev.k         ← mean-reversion strategy
    └── python/zhy_mr_ib.py     ← IB Python wrapper
```

**Note on files that were listed in the April 19 HANDOFF but are NOT
actually on master:**
- `ZHY_Isserlis.lean` — returns 404 on GitHub; either renamed or never
  committed. Isserlis now lives inline in `ZHY_Variance.lean` as the
  `IsZHYModel.cov_sameI` / `cov_sameJ` / `cov_diff` structure fields.
- `ZHY_Hello.lean` — not on master.

**Recent commits:**
- Run `git log --oneline -20` on master to see the latest.
- The two most recent Lean additions are `ZHY_Algebra.lean` and
  `ZHY_Variance.lean`, 2026-04-22.

---

## Lean 4 Status

### Toolchain
- **Lean:** `leanprover/lean4:v4.30.0-rc2` (not 4.14 as the old HANDOFF
  claimed — the project was bumped some time between April 19 and
  April 22)
- **Mathlib commit:** `d2962c4edce550edb489343fa7b499ea5bb25969`
- Four modules compile clean from cache.

### Module-by-module

**ZHY_Core.lean — compiles, zero errors** (5 theorems):
1. `lemma41_unbiased_iff` — Lemma 4.1: unbiased ↔ `Σ cᵢⱼ τᵢⱼ = 1`
2. `nonOverlapping_irrelevant` — non-overlapping pairs irrelevant
3. `zhy_unbiased` — normalised ZHY estimator is unbiased
4. `A1_optimal_explicit` — `T(w*) = Θ` at optimal weights
5. `CR_equality_at_zero` — `FI · Var_min = 1` at `ρ = 0`

**ZHY_BLUE.lean — compiles, zero errors** (3 theorems):
1. `BLUE_A1` — `A₁(c) ≥ 1/Θ` for all unbiased `c` (Cauchy-Schwarz)
2. `A1_opt_eq` — `A₁(w*)` numerator `= Θ`
3. `BLUE_A1_sharp` — `A₁(w*) = 1/Θ`

**ZHY_Algebra.lean — NEW 2026-04-22, compiles, zero errors** (4 lemmas):
Pure combinatorial algebra over `Finset.sum` — no probability content.
1. `sum_square_off_diag` — `∑ⱼ∑_{l ≠ j} g j · g l = (∑ g)² − ∑ g²`
2. `sum_firstcase_collapse` — same-`i` off-diagonal sum
3. `sum_secondcase_collapse` — same-`j` off-diagonal sum (symmetric)
4. `sum_split_four` — the four-way partition of a 4-fold sum by
   `(i = k, j = l)` cases; this is what makes Theorem 5.1's proof
   go through cleanly.

**ZHY_Variance.lean — NEW 2026-04-22, compiles, zero errors**
The main formalisation of Theorem 5.1:
- `IsZHYModel` — packages the Gaussian Isserlis identity and the four
  covariance identities (`var_RS`, `cov_same`, `cov_sameI`, `cov_sameJ`,
  `cov_diff`) as structure fields. Honest axiom boundary: matches the
  thesis's "by standard distribution theory".
- `NoRectangle τ` — the Interval-Structure Lemma stated as a property
  of the overlap matrix, matching how the thesis uses it.
- `HasLinearVariance` — variance-of-a-sum as a structural hypothesis.
- `USum`, `VSum` — the two summands of the decomposition.
- `theorem51` — **`V = σ₁²σ₂² · USum + σ₁₂² · VSum`, ZERO SORRIES.**

### Build

```bash
cd ~/Documents/Paper_2026
lake exe cache get   # if not already cached
lake build ZHY_Core ZHY_BLUE ZHY_Algebra ZHY_Variance
```

All four build in under a minute from cache.

### Known cosmetic warnings (harmless)
- `push_neg` deprecation note in `ZHY_Core`.
- Two unused `hτ_nn` parameters in `ZHY_Core` corollaries.
- Five unused `Finset.sum_ite_eq'` simp hints in `ZHY_Algebra` — `simp`
  closed the goals without needing them.

None of these affect correctness. Can be cleaned up later.

---

## Paper Status

### Journal version (journal/)
Target: JFEC submission within 6 months.

| Section | File | Status |
|---------|------|--------|
| Introduction | 01_introduction.tex | DONE |
| Literature Review | 02_literature.tex | DONE |
| Model | 02_model.tex | EMPTY |
| ZHY Estimator | 03_estimator.tex | EMPTY |
| Main Results | 04_main_results.tex | EMPTY |
| Simulation | 05_simulation.tex | EMPTY |
| Conclusion | 06_conclusion.tex | EMPTY |

### Source material for remaining sections
- Model (Section 2): from `chap5.tex` lines 1–100.
- ZHY Estimator (Section 3): from `chap5.tex` lines 300–315.
- Theorem 1 proof (Section 4): `chap5.tex` lines 317–368 — note this
  is the 2016 result; the paper should present it clearly as such.
- Optimal A₁ weights: `chap5.tex` lines 410–412 — also 2016.
- New 2026 theorems (Full-variance KKT, two-step BLUE, Gauss-Markov):
  `sections_4_2_4_3.tex` + `section_gauss_markov.tex`.

### Simulation results (existing)
- 5 crypto assets (BTC/ETH/SOL/LINK/ADA).
- Naive 5-min: Frobenius error 0.2601.
- Optimal ZHY: 0.0676 (3.8× better).
- Precision-weighted shrinkage: 0.0674.

---

## Literature Review — Key Facts

**The gap, confirmed by Gemini search (2011–2026):**
No existing paper has:
- Exact finite-sample conditional variance for the HY estimator
- BLUE result for the weighted HY class (finite-sample)
- Machine-checked formalisation of any of the above

**Key papers and their limitations:**
- Hayashi-Yoshida (2008): asymptotic, `λ → ∞`, general partitions
- Hayashi-Yoshida (2011): asymptotic, stable convergence
- Griffin-Oomen (2011): asymptotic, renewal processes
- Koike (2014–2026): asymptotic kernel variance estimator
- Bibinger (2014): Le Cam asymptotic optimality
- Ogihara-Yoshida (2012): quasi-MLE, asymptotic

---

## Trading System

**Assets:** ES vs NQ (CME, both on same exchange)
**Strategy:** Mean-reversion of lagged spread `Z(t) = NQ(t) - α - β·ES(t-h*)`
**Lag calibration:** Daily/weekly at minute timescale (RBS approach)
**Entry:** `|Z| > 2σ_Z`, Exit: `|Z| < 0.5σ_Z`, Stop: `|Z| > 4σ_Z`
**Position sizing:** From Theorem 5.1 precision (higher precision = larger position)

**IB account:** Live account, TWS running, port 7497 (paper)
**KDB+:** Installed and licensed on Mac

**To run:**
```bash
q -p 5000
# In Q: \l trading/k/zhy_meanrev.k
# Type: testmr[]
python trading/python/zhy_mr_ib.py --data-only --port 7497
python trading/python/zhy_mr_ib.py --paper --port 7497
```

---

## Immediate Actions (Priority Order)

### THIS WEEK

1. **Commit tonight's Lean work.** Two new files need to land on master:
   ```bash
   cd ~/Documents/Paper_2026
   git add lean/ZHY_Algebra.lean lean/ZHY_Variance.lean lean/lakefile.lean
   git commit -m "Formalise Theorem 5.1 in Lean 4: exact variance decomposition"
   git push origin master
   ```

2. **Send Yoshida email** — still priority #1 from previous handoffs.
   - To: `yoshida@ms.u-tokyo.ac.jp`
   - Oxford alumni email applied April 18; decide whether to wait or send
     from `yang.maths@gmail.com` now.
   - Text is in the April 19 HANDOFF; one edit worth considering: mention
     the Lean formalisation ("a machine-checked proof in Lean 4") as an
     additional reassurance that the result is correct.
   - If he says yes: send `theorems_summary.pdf`.

3. **Update theorems_summary.pdf** if needed to reflect the 2016/2026
   distinction clearly before sending to Yoshida.

### THIS MONTH

4. Write journal sections `02_model.tex` through `06_conclusion.tex`.
5. Assemble `main.tex` for journal version.
6. Collect ES/NQ tick data via IB (`--data-only` mode).
7. Validate the trading signal on real data.

### AFTER YOSHIDA REPLIES

8. Send Brian Ripley email (when paper draft is ready).
9. Submit to JFEC.

---

## Key People

**Yoshida:** `yoshida@ms.u-tokyo.ac.jp`
- Most authoritative person on the HY estimator.
- Won 2026 MEXT Commendation (April 8, 2026).
- Publishing on deep learning for HFT (April 2025 preprint).
- Email him first, before anyone else.

**Brian Ripley:** `brian.ripley@stats.ox.ac.uk` (verify address)
- Supervised MSc and DPhil.
- Send email when the paper draft is ready.

**Pelger:** Stanford, works on high-frequency factor models.
- Potential application of ZHY to his covariance pipeline.
- Do not contact until the paper is submitted.

**Axiom Math:** axiommath.ai
- $1.6B valuation, building an AI mathematician in Lean 4.
- CEO: Carina Hong (Oxford Rhodes Scholar).
- The Lean proofs are the calling card. `ZHY_Variance.lean` is now the
  most impressive piece to show them — a non-trivial piece of applied
  mathematics, machine-verified, with zero sorries.
- DO NOT approach until Paper 1 is submitted.

---

## Decisions Made (Do Not Re-Litigate)

- Asset pair: ES vs NQ (not ES/Euro Stoxx — wrong timezone for Saratoga).
- Strategy: Mean-reversion (not directional) — matches RBS approach.
- Lag timescale: Minutes, calibrated daily.
- Journal target: JFEC (Journal of Financial Econometrics).
- Name on paper: Dr Yang Azzollini (not Yang Wu Azzollini).
- Repository: public on GitHub under ChubbyFaceEuler.
- Trading system: validate signal BEFORE showing to friend with fund.
- Axiom: wait until Paper 1 submitted.
- **Framing of Interval-Structure Lemma: it is 2016 thesis content,
  not a new 2026 result.** The thesis proof on p.108 uses the disjointness
  of consecutive intervals directly. The 2026 contribution is the
  formalisation in Lean 4, not the mathematical argument.

---

## The Book (Future)

Planned structure (to write after paper is submitted):
1. The problem — Epps effect, synchronisation.
2. The ZHY estimator — overlaps, unbiasedness.
3. Exact variance — Theorem 5.1 with complete proof and Lean 4 walk-through.
4. Optimal weights — KKT, two-step.
5. Gauss-Markov theorem.
6. Lean 4 formalisation — worked example using the `ZHY_*` modules as
   a concrete case study in formalising applied statistics.
7. Trading system — K/KDB+ implementation.
8. Extensions — noise, multivariate, lead-lag.

---

## Technical Setup

- Mac: Saratoga CA.
- Warp terminal: AI terminal, handles file operations and compilation.
- VS Code: Lean 4 extension installed.
- KDB+: installed and licensed.
- IB TWS: running, live account.
- Python: `ib_insync`, `qpython` (`pip install`).
- Lean: 4.30.0-rc2, installed via `elan`.
- Mathlib: commit `d2962c4`, cached locally.

---

## Session Log — 2026-04-22 (evening)

What happened tonight:

1. **Re-read the thesis carefully.** Confirmed that the "Interval-Structure
   Lemma" that had been described as new 2026 mathematics in earlier
   HANDOFF and overview drafts is, in fact, explicit in the 2016 thesis
   Chapter 5 proof of Theorem 5.1 (page 108). The 2026 contribution is
   the Lean 4 formalisation, not the mathematical argument.

2. **Verified the environment.** Lean 4.30.0-rc2 + Mathlib d2962c4.
   `ZHY_Core` and `ZHY_BLUE` both build clean from cache.

3. **Wrote `ZHY_Algebra.lean`.** Four pure-combinatorial Finset.sum
   lemmas, serving as scaffolding for `ZHY_Variance`. Compiled cleanly
   on the second Warp build (first build flagged five `rw [Finset.sum_ite_eq']`
   failures; the fix was to replace each with `simp [Finset.sum_ite_eq']`).

4. **Wrote `ZHY_Variance.lean`.** The full Theorem 5.1 formalisation,
   packaged with `IsZHYModel` / `NoRectangle` / `HasLinearVariance`
   as honest axiomatic inputs. Compiled cleanly on the first Warp build
   with zero warnings.

5. **Both files now live in** `~/Documents/Paper_2026/lean/` and are
   added as roots in the lakefile. Not yet committed or pushed — see
   "Immediate Actions" above.

---

*End of handoff document*
*Generated: April 22, 2026 (~11:30 PM PDT)*
