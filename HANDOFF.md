# ZHY Paper Project — Handoff Document
## Date: April 19, 2026
## For: Dr Yang Azzollini

---

## Who You Are

Oxford DPhil Statistics (Lady Margaret Hall), supervised by Brian D. Ripley
(MSc) and Brian D. Ripley + Peter Clifford (DPhil). BA Mathematics &
Computer Science, St Hugh's College. Ten-plus years quantitative researcher
at a leading international investment bank. Currently in Saratoga CA.
Contact: yang.maths@gmail.com

---

## The Core Result

**Theorem 1 (DPhil thesis, Chapter 5):**
The weighted ZHY covariance estimator has exact finite-sample conditional variance:

  Var(σ̂₁₂ | τ) = σ₁²σ₂² A₁(w) + σ₁₂² A₂(w)

where A₁ and A₂ are explicit functions of the overlap structure {τᵢⱼ}.
This is EXACT (not asymptotic), holds for ANY fixed timestamps, requires
NO distributional assumption on observation times beyond independence
from prices.

**Three new results (2026):**
- Theorem 2: Full-variance optimal weights via (K+1)×(K+1) KKT system
- Theorem 3: Two-step estimator is BLUE within weighted ZHY class
- Theorem 4: Asynchronous Gauss-Markov — achieves Cramér-Rao at ρ=0

---

## Repository

**Location:** ~/Documents/Paper_2026
**GitHub:** github.com/ChubbyFaceEuler/Paper_2026 (may still be private)

**Structure:**
```
Paper_2026/
├── paper/
│   ├── theorems_summary.pdf    ← 2-page theorem statements for Yoshida
│   └── theorems_summary.tex
├── lean/
│   ├── ZHY_Core.lean           ← 5 theorems, ZERO SORRIES ✓
│   ├── ZHY_BLUE.lean           ← BLUE theorem at ρ=0, ZERO SORRIES ✓
│   ├── ZHY_Isserlis.lean       ← Isserlis calculation
│   ├── ZHY_Hello.lean          ← minimal test, no Mathlib
│   ├── lakefile.lean
│   └── lean-toolchain          ← Lean 4.14.0
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

**Key commits:**
- 2939dd37 — ZHY_Core.lean: 5 theorems verified
- f4c8ce21 — ZHY_BLUE.lean: BLUE theorem verified
- 85bebbb  — journal/ and thesis_extended/ folders created
- (check git log for latest)

---

## Lean 4 Status

**ZHY_Core.lean — COMPILES, ZERO ERRORS:**
1. lemma41_unbiased_iff — Lemma 4.1: unbiased ↔ Σ cᵢⱼτᵢⱼ = 1
2. nonOverlapping_irrelevant — non-overlapping pairs irrelevant
3. zhy_unbiased — normalised ZHY estimator is unbiased
4. A1_optimal_explicit — T(w*) = Θ at optimal weights
5. CR_equality_at_zero — FI · Var_min = 1 at ρ=0

**ZHY_BLUE.lean — COMPILES, ZERO ERRORS:**
1. BLUE_A1 — A₁(c) ≥ 1/Θ for all unbiased c (Cauchy-Schwarz proof)
2. A1_opt_eq — A₁(w*) numerator = Θ
3. BLUE_A1_sharp — A₁(w*) = 1/Θ (sharp bound)

**To build:**
```bash
cd ~/Documents/Paper_2026
lake exe cache get   # if not done
lake build ZHY_Core
lake build ZHY_BLUE
```

**Three minor warnings (cosmetic only):**
- push_neg deprecated (still works)
- Two unused hτ_nn parameters in corollaries

---

## Paper Status

### Journal version (journal/)
Target: JFEC submission within 6 months

| Section | File | Status |
|---------|------|--------|
| Introduction | 01_introduction.tex | DONE |
| Literature Review | 02_literature.tex | DONE |
| Model | 02_model.tex | EMPTY |
| ZHY Estimator | 03_estimator.tex | EMPTY |
| Main Results | 04_main_results.tex | EMPTY |
| Simulation | 05_simulation.tex | EMPTY |
| Conclusion | 06_conclusion.tex | EMPTY |

### Source material for remaining sections:
- Model (Section 2): from chap5.tex lines 1-100 (uploaded in prev conversation)
- ZHY Estimator (Section 3): from chap5.tex lines 300-315
- Theorem 1 proof: chap5.tex lines 317-368
- Optimal weights: chap5.tex lines 410-412
- New theorems (2-4): sections_4_2_4_3.tex + section_gauss_markov.tex

### Simulation results:
- 5 crypto assets (BTC/ETH/SOL/LINK/ADA)
- Naive 5-min: Frobenius error 0.2601
- Optimal ZHY: 0.0676 (3.8× better)
- Precision-weighted shrinkage: 0.0674

---

## Literature Review — Key Facts

**The gap confirmed by Gemini search (2011-2026):**
NO existing paper has:
- Exact finite-sample conditional variance for HY estimator
- BLUE result for weighted HY class (finite-sample)

**Key papers and their limitations:**
- Hayashi-Yoshida (2008): asymptotic, λ→∞, general partitions
- Hayashi-Yoshida (2011): asymptotic, stable convergence
- Griffin-Oomen (2011): asymptotic, renewal processes
- Koike (2014-2026): asymptotic kernel variance estimator
- Bibinger (2014): Le Cam asymptotic optimality
- Ogihara-Yoshida (2012): quasi-MLE, asymptotic

**Positioning sentence:**
"The first explicit derivation of a finite-sample, timestamp-conditional
variance formula for the ZHY class of estimators, providing a rigorous
alternative to the asymptotic approximations of Hayashi-Yoshida (2008)
and Griffin-Oomen (2011)."

---

## Trading System

**Assets:** ES vs NQ (CME, both on same exchange)
**Strategy:** Mean-reversion of lagged spread Z(t) = NQ(t) - α - β·ES(t-h*)
**Lag calibration:** Daily/weekly at minute timescale (as per RBS approach)
**Entry:** |Z| > 2σ_Z, Exit: |Z| < 0.5σ_Z, Stop: |Z| > 4σ_Z
**Position sizing:** From Theorem 1 precision (higher precision = larger position)

**IB account:** Live account, TWS running, port 7497 (paper)
**KDB+:** Installed and licensed on Mac

**To run:**
```bash
# 1. Start KDB+ on port 5000
q -p 5000
# In Q: \l trading/k/zhy_meanrev.k
# Type: testmr[]

# 2. Collect data
python trading/python/zhy_mr_ib.py --data-only --port 7497

# 3. Paper trade
python trading/python/zhy_mr_ib.py --paper --port 7497
```

---

## Immediate Actions (Priority Order)

### THIS WEEK:
1. **Send Yoshida email** — most important action
   - To: yoshida@ms.u-tokyo.ac.jp
   - Wait for Oxford alumni email (applied April 18) OR send from
     yang.maths@gmail.com now — do not wait more than a week
   - Email text:
     "Dear Professor Yoshida, I completed a DPhil at Oxford in 2016
     under Brian Ripley, deriving the exact finite-sample conditional
     variance of the general weighted HY estimator as an explicit
     function of the overlap structure {τᵢⱼ}, without distributional
     assumptions on the observation times. Before publishing, I would
     like to confirm this has not appeared elsewhere in the literature.
     Would you be willing to take a brief look? Dr Yang Azzollini"
   - If he says yes: send theorems_summary.pdf immediately

2. **Push to GitHub**
   - Ask Warp: git push origin master
   - Make repository PUBLIC after pushing

3. **Commit README.md**
   - Download README.md from outputs
   - Ask Warp to move to ~/Documents/Paper_2026/README.md
   - git add README.md && git commit && git push

### THIS MONTH:
4. Write journal sections 02_model.tex through 06_conclusion.tex
5. Assemble main.tex for journal version
6. Collect ES/NQ tick data via IB (--data-only mode)
7. Validate signal on real data

### AFTER YOSHIDA REPLIES:
8. Send Brian Ripley email (when draft ready)
9. Submit to JFEC

---

## Key People

**Yoshida:** yoshida@ms.u-tokyo.ac.jp
- Most authoritative person on HY estimator
- Won 2026 MEXT Commendation (April 8, 2026)
- Publishing on deep learning for HFT (April 2025 preprint)
- Email him first, before anyone else

**Brian Ripley:** brian.ripley@stats.ox.ac.uk (verify)
- Supervised MSc and DPhil
- Send email when paper draft is ready (not yet)

**Pelger:** Stanford, works on high-frequency factor models
- Potential application of ZHY to his covariance matrix pipeline
- Do not contact until paper is submitted

**Axiom Math:** axiommath.ai
- $1.6B valuation, building AI mathematician in Lean 4
- CEO: Carina Hong (Oxford Rhodes Scholar)
- The Lean proofs are the calling card
- DO NOT approach until Paper 1 is submitted
- de97af5 / f4c8ce21 are the commits to show them

---

## Decisions Made (Do Not Re-Litigate)

- Asset pair: ES vs NQ (not ES/Euro Stoxx — wrong timezone for Saratoga)
- Strategy: Mean-reversion (not directional) — matches RBS approach
- Lag timescale: Minutes, calibrated daily
- Journal target: JFEC (Journal of Financial Econometrics)
- Name on paper: Dr Yang Azzollini (not Yang Wu Azzollini)
- Repository: public on GitHub under ChubbyFaceEuler
- Trading system: validate signal BEFORE showing to friend with fund
- Axiom: wait until Paper 1 submitted

---

## The Book (Future)

Planned structure (to write after paper submitted):
1. The problem — Epps effect, synchronisation
2. The ZHY estimator — overlaps, unbiasedness
3. Exact variance — Theorem 1 with complete proof
4. Optimal weights — KKT, two-step
5. Gauss-Markov theorem
6. Lean 4 formalisation — worked example
7. Trading system — K/KDB+ implementation
8. Extensions — noise, multivariate, lead-lag

---

## Technical Setup

- Mac: Saratoga CA
- Warp terminal: AI terminal, handles file ops and compilation
- VS Code: Lean 4 extension installed (v0.0.234)
- KDB+: installed and licensed
- IB TWS: running, live account
- Python: ib_insync, qpython needed (pip install)
- Lean 4.14.0: installed via elan
- Mathlib cache: downloaded (8,300 files)

---

## Lean 4 Learning Progress

Julianna is learning Lean 4 from scratch, one concept at a time.
Completed: Types and terms (Lessons 1-2).
Background: Haskell (functional programming) — transfers directly.
K language — also has functional array thinking.
Next Lean lesson: Propositions and proofs (the `by` tactic block).

---
*End of handoff document*
*Generated: April 19, 2026*
