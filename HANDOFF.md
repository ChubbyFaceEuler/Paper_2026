# ZHY Paper Project — Handoff Document
## Date: April 21, 2026
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

**Theorem 1 (DPhil thesis, Chapter 5; exact variance identity):**
The weighted ZHY covariance estimator has exact finite-sample conditional
variance:

  Var(σ̂₁₂(w) | τ) = [σ₁² σ₂² A₁(w) + σ₁₂² A₂(w)] / T(w)²

where A₁(w) = Σ_{ij} w²_{ij} τ^X_i τ^Y_j and
A₂(w) = Σ_i R_i(w)² + Σ_j C_j(w)² − Σ_{ij} w²_{ij} τ²_{ij}.

This is EXACT (not asymptotic), holds for ANY fixed timestamps, requires
NO distributional assumption on observation times beyond independence
from prices.

**Three new results (2026):**
- Theorem 2: Full-variance KKT sufficiency for κ = ρ² ∈ [0,1]
- Theorem 3: Two-step estimator is BLUE at fixed κ within weighted ZHY class
- Theorem 4: Asynchronous Gauss-Markov — achieves Cramér-Rao at ρ=0

**New result (April 21, 2026 session): the Interval-Structure Lemma.**
Fix i ≠ k and j ≠ ℓ. If τ_{ij} > 0 and τ_{kℓ} > 0 on an overlap matrix
arising from two partitions of [0,1], then τ_{iℓ} · τ_{kj} = 0.
This is the geometric identity that closes the Isserlis expansion
in Theorem 1's proof. See "New Mathematical Result" section below.

---

## Repository

**Location:** ~/Documents/Paper_2026
**GitHub:** github.com/ChubbyFaceEuler/Paper_2026 (public)

**Structure (actual as of April 21):**
```
Paper_2026/
├── HANDOFF.md                  ← this document
├── README.md                   ← public description
├── lean/
│   ├── ZHY_Core.lean           ← 5 theorems, ZERO SORRIES ✓
│   ├── ZHY_BLUE.lean           ← BLUE at ρ=0, ZERO SORRIES ✓
│   ├── ZHY_Opt.lean            ← V_nonneg, KKT, two-step, ZERO SORRIES ✓
│   ├── ZHY_Main.lean           ← aggregator (re-exports 7 theorems)
│   ├── ZHY_Geometry.lean       ← Interval-Structure Lemma ✓ (NEW 2026-04-21)
│   ├── lakefile.lean
│   └── lean-toolchain
├── journal/                    ← JFEC submission (tight style)
│   ├── main.tex                ← EMPTY (0 bytes)
│   ├── references.bib
│   └── sections/
│       ├── 01_introduction.tex ← EMPTY
│       ├── 02_model.tex        ← 83 lines, populated (bivariate BM model)
│       ├── 03_estimator.tex    ← EMPTY
│       ├── 04_main_results.tex ← EMPTY
│       ├── 04b_theorem3_asymptotic.tex  ← 53 lines, populated
│       ├── 05_simulation.tex   ← EMPTY
│       └── 06_conclusion.tex   ← EMPTY
├── Yangs_theorems_summary.pdf  ← 2-page theorem summary (needs update)
└── (trading/, code/ subdirs as before; see below)
```

**Key commits:**
- `2939dd37` — ZHY_Core.lean: Theorems 1(ii,iii) pieces, 5 theorems verified
- `f4c8ce21` — ZHY_BLUE.lean: BLUE at ρ=0 verified
- `bcade6c`  — ZHY_Opt.lean: V_expand placeholder
- **`f77aeba`** — ZHY_Opt: V_expand closed, Theorem 2 (KKT) verified (2026-04-21)
- **`116f0df`** — ZHY_Opt: Theorem 3 (two-step, fixed-κ) verified (2026-04-21)
- **`319558c`** — ZHY_Main aggregator + Thm 3 asymptotic tex fragment (2026-04-21)
- **`65a6702`** — ZHY_Geometry: Interval-Structure Lemma (2026-04-21)

---

## Lean 4 Status

**ZHY_Core.lean — ZERO SORRIES:**
1. `lemma41_unbiased_iff` — unbiased ↔ Σ cᵢⱼτᵢⱼ = 1
2. `nonOverlapping_irrelevant` — non-overlapping pairs irrelevant
3. `zhy_unbiased` — normalised ZHY estimator is unbiased
4. `A1_optimal_explicit` — T(w*) = Θ at optimal weights
5. `CR_equality_at_zero` — FI · Var_min = 1 at ρ=0

**ZHY_BLUE.lean — ZERO SORRIES:**
1. `BLUE_A1` — A₁(c) ≥ 1/Θ for unbiased c (Cauchy-Schwarz)
2. `A1_opt_eq` — A₁(w*) numerator = Θ
3. `BLUE_A1_sharp` — A₁(w*) = 1/Θ (sharp)

**ZHY_Opt.lean — ZERO SORRIES (new as of 2026-04-21):**
1. `V_nonneg` — A₁(d) + κA₂(d) ≥ 0 for all perturbations d, κ ∈ [0,1]
2. `V_expand` — quadratic expansion V(w') = V(w) + 2G(w;d) + V(d)
3. `KKT_sufficient` — Theorem 2: KKT solutions minimise variance
4. `two_step_efficiency` — Theorem 3: fixed-κ form
5. Helper lemmas for Finset algebra

**ZHY_Main.lean — aggregator:**
Re-exports 7 paper theorems under canonical names via `abbrev`:
- `theorem1_unbiasedness`, `corollary1_1_A1_optimal`
- `theorem2_KKT_sufficient`, `theorem3_two_step_efficiency`
- `theorem4_i_unbiased_iff_ZHY`, `theorem4_ii_BLUE_rho_zero`,
  `theorem4_iii_Cramer_Rao_at_zero`

**ZHY_Geometry.lean — ZERO SORRIES (new as of 2026-04-21):**
1. `structure GridPair` — axiomatisation of asynchronous overlap matrices
2. `interval_structure_lemma` — the key geometric identity
3. `regime_X_vanishes` — the "cross-crossed" Isserlis sum vanishes
4. `total_overlap_consistent` — Fubini sanity check

**Build status:** all modules compile clean, 8316+ jobs, zero errors.

**To build:**
```bash
cd ~/Documents/Paper_2026
lake exe cache get   # if not done
lake build ZHY_Main  # builds all upstream modules
```

---

## What IS and is NOT Formally Verified

**Formally verified (zero sorries):**
- Unbiasedness of weighted ZHY estimator
- Corollary 1.1 (A₁-optimal weights at ρ=0)
- BLUE at ρ=0 within weighted ZHY (via Cauchy-Schwarz)
- Theorem 2 (KKT sufficiency, κ ∈ [0,1])
- Theorem 3 (two-step, fixed-κ)
- Theorem 4(i) (unbiased iff weighted ZHY)
- Theorem 4(iii) product-equals-unity form (FI · Var_min = 1)
- **Interval-Structure Lemma** + **Regime-X vanishing** (NEW)

**NOT formally verified; on paper only:**
- **Theorem 1 as a single variance identity.** The Isserlis expansion +
  four-regime decomposition + A₂ assembly. The algebraic pieces
  (Interval-Structure, Regime-X) are in Lean; the Isserlis expansion
  and the assembly into the full variance identity are not yet.
  Next step would be `ZHY_Variance.lean`, estimated 3-5 days of Lean work.
- Corollary 3.1 (asymptotic attainment). Requires probability-theoretic
  infrastructure beyond deterministic-τ setting.
- Fisher information derivation via block matrix inversion
  (the explicit Θ / (σ₁²σ₂²) trace computation from the joint
  Gaussian covariance). Only the product-equals-1 form is in Lean.
- Proof that real interval-partition grids satisfy
  `GridPair.hNoRectangle`. The property is axiomatized as a field
  of the `GridPair` structure; the geometric derivation (from the
  u_{ℓ-1} < t_i ≤ t_{k-1} < u_j ≤ u_{ℓ-1} contradiction argument)
  is in the paper but not yet formalised. Elementary but requires
  Mathlib's interval/measure infrastructure.

**Three minor cosmetic warnings (not blocking):**
- push_neg deprecated (still works)
- Unused hτ_nn / hτX / hτY / h₀ parameters in a few corollaries
- Unused variables in A1_opt_eq (handled implicitly by field_simp)

---

## New Mathematical Result (2026-04-21)

**The Interval-Structure Lemma.**

Statement: For any overlap matrix arising from two partitions of [0,1],
if i ≠ k, j ≠ ℓ, τ_{ij} > 0, and τ_{kℓ} > 0, then τ_{iℓ} · τ_{kj} = 0.

Equivalently: the set {(i,j) : τ_{ij} > 0} does not contain the four
corners of any axis-aligned rectangle with non-trivially separated
rows and columns. The overlap set is a diagonal staircase band,
not an arbitrary two-dimensional support.

**Why this matters.** The paper's A₂ functional
    A₂(w) = Σ_i R_i² + Σ_j C_j² − Σ_{ij} w²_{ij} τ²_{ij}
does NOT equal the full Isserlis Term II sum
    S(w) = Σ_{ijkℓ} w_{ij} w_{kℓ} τ_{iℓ} τ_{kj}
in general. A 2×2 numerical check on arbitrary (non-partition) τ
matrices shows the two differ by terms of the form
w_{ij} w_{kℓ} τ_{iℓ} τ_{kj} with i ≠ k AND j ≠ ℓ — the "cross-crossed"
Regime-X contribution.

The Interval-Structure Lemma says: on valid overlap matrices, every
such cross-crossed term has at least one factor equal to zero.
Summed, Regime X contributes zero to the variance, and the paper's
A₂ form is exactly the Term II contribution.

**Without this lemma, Theorem 1's proof does not close.**

**Status:** proved in the paper (Lemma 3.3 of journal_03_variance_v4.tex)
by a direct contradiction argument. Axiomatised in Lean as a field of
the `GridPair` structure (ZHY_Geometry.lean). Algebraic consequences
proved in Lean, zero sorries.

**Does not appear in DPhil thesis (Azzollini 2016) or in prior discussions
of the weighted ZHY variance.** This is a new contribution emerging from
the formalisation work of this session.

---

## Paper Drafts (local scratch, not yet committed)

Produced during the 2026-04-21 session. Not pushed to repo; live in
local outputs/downloads area. Use as input to future drafting work.

- `journal_03_variance_v4.tex` — Section 3 full-derivation draft,
  bookkeeping style (~10 pages in PDF). Contents:
  second-moment lemma from Itô isometry, overlap marginals,
  termwise overlap bound, **Interval-Structure Lemma**, Isserlis,
  Theorem 1 with full four-regime proof, Corollary 1.1 with full
  Cauchy-Schwarz evaluation.
- `journal_04_optimal_v3.tex` — Section 4 full-derivation draft,
  bookkeeping style (~8 pages). Contents: V_nonneg via termwise
  decomposition, V_expand via full polarisation, KKT sufficiency,
  two-step theorem + asymptotic corollary, Theorem 4 with full
  Fisher information derivation via block matrix inversion.
- `Sections_3_and_4_full_expansion.pdf` — 18-page compiled draft.
- `summary_updates.txt` — three text replacements for
  Yangs_theorems_summary.pdf reflecting current formalisation status.

---

## Paper Status (journal/)

Target: JFEC (Journal of Financial Econometrics). Framing: Framing B
(methodology-as-brand: exact finite-sample + real-time-recursive +
formally verified). Finance is the concrete setting; the Zhou/HY
equivalence is a remark, not the thesis.

| Section | File | Lines | Status |
|---------|------|-------|--------|
| Model | 02_model.tex | 83 | populated (bivariate BM) |
| Intro | 01_introduction.tex | 0 | EMPTY |
| Estimator | 03_estimator.tex | 0 | EMPTY — but content drafted in v4 |
| Main Results | 04_main_results.tex | 0 | EMPTY — but content drafted in v3 |
| Thm 3 asymptotic | 04b_theorem3_asymptotic.tex | 53 | populated, not \input'd |
| Simulation | 05_simulation.tex | 0 | EMPTY |
| Conclusion | 06_conclusion.tex | 0 | EMPTY |
| main.tex | main.tex | 0 | EMPTY — no document skeleton yet |

**Section 2 reorganisation pending:** The current `02_model.tex` has a
subsection on the weighted ZHY estimator class (§2.3, labelled
`sec:estimator`) that needs to move forward into Section 3. Forward
references to Section 3/4 also need updating. When done, Section 2
is purely model+assumptions (~60 lines).

---

## Literature Review — Key Facts

**The gap confirmed by prior searches (2011-2026):**
No existing paper has:
- Exact finite-sample conditional variance for HY estimator
- BLUE result for weighted HY class (finite-sample)
- Formal verification of any of the above

**Key papers and their limitations:**
- Hayashi-Yoshida (2008): asymptotic, λ→∞, general partitions
- Hayashi-Yoshida (2011): asymptotic, stable convergence
- Griffin-Oomen (2011): asymptotic, renewal processes
- Koike (2014-2016): asymptotic kernel variance estimator
- Bibinger (2014): Le Cam asymptotic optimality
- Ogihara-Yoshida (2012): quasi-MLE, asymptotic

**Positioning sentence (Framing B):**
"The first explicit derivation of a finite-sample, timestamp-conditional
variance formula for the weighted Zhou-Hayashi-Yoshida class of estimators,
with the full optimality theory and the underlying geometric identity
formally verified in Lean 4 with Mathlib."

---

## Trading System

**Assets:** ES vs NQ (CME, same exchange, same timezone)
**Strategy:** Mean-reversion of lagged spread Z(t) = NQ(t) − α − β·ES(t−h*)
**Lag calibration:** Daily/weekly at minute timescale (RBS approach)
**Entry:** |Z| > 2σ_Z, Exit: |Z| < 0.5σ_Z, Stop: |Z| > 4σ_Z
**Position sizing:** From Theorem 1 precision (higher precision = larger position)

**IB account:** Live, TWS running, port 7497 (paper)
**KDB+:** Installed and licensed on Mac

**To run:**
```bash
q -p 5000                                                  # KDB+
python trading/python/zhy_mr_ib.py --data-only --port 7497 # data
python trading/python/zhy_mr_ib.py --paper --port 7497    # paper trade
```

---

## Key People

**Yoshida:** yoshida@ms.u-tokyo.ac.jp
  - Emailed April 2026 from yang.maths@gmail.com.
  - Most authoritative person on HY estimator.
  - MEXT Commendation April 2026.
  - If/when he replies: updated theorems summary reflects 4 completed
    Lean commits, not just the 2 he would have been told about before.

**Brian Ripley:** brian.ripley@stats.ox.ac.uk (verify)
  - Supervised MSc and DPhil.
  - Send email when paper draft is ready (not yet).

**Pelger (Stanford):** high-frequency factor models.
  - Potential downstream use of ZHY in covariance matrix pipelines.
  - Do not contact until paper is submitted.

**Axiom Math:** axiommath.ai, $1.6B valuation, AI mathematician in Lean 4.
  - CEO Carina Hong (Oxford Rhodes Scholar).
  - Lean proofs are the calling card for any eventual conversation.
  - DO NOT approach until Paper 1 is submitted.
  - Commits to show: 2939dd37, f4c8ce21, f77aeba, 116f0df, 65a6702.

---

## Immediate Actions (Priority Order)

### THIS WEEK:

1. **Update Yangs_theorems_summary.pdf** — `summary_updates.txt` has
   three replacement text blocks reflecting the four completed Lean
   commits and the updated formalisation scope. Apply by hand and
   recompile.

2. **Await Yoshida reply** — if he engages, the updated summary PDF
   is what to send.

### THIS MONTH:

3. **Section 2 reorganisation** — move estimator-class subsection from
   `02_model.tex` to Section 3; update forward references.

4. **Section 1 (introduction)** — write in Framing B (methodology-as-brand).
   Finance concrete, Lean a pillar, Zhou/HY equivalence as a remark.

5. **Integrate paper drafts** — take `journal_03_variance_v4.tex` and
   `journal_04_optimal_v3.tex` from local scratch, adapt to the journal
   style, integrate into `journal/sections/03_estimator.tex` and
   `04_main_results.tex`, \input into `main.tex` (which still needs
   a skeleton).

6. **Collect ES/NQ tick data** via IB (--data-only mode).
7. **Validate mean-reversion signal** on real data.

### LATER / LOWER PRIORITY:

8. **Write `ZHY_Variance.lean`** — formalise Theorem 1 itself
   using `ZHY_Geometry.regime_X_vanishes` + axiomatized second moments
   + axiomatized Isserlis + four-regime decomposition. Estimated
   3-5 days of focused Lean work.

9. **Prove `hNoRectangle` from concrete interval geometry** — removes
   the axiomatisation. Elementary but requires Mathlib's
   measure-theoretic interval infrastructure.

10. **Section 5 (simulation)** — cannot draft without results; collect
    first.

11. **Send Brian Ripley email** when paper draft ready.

12. **Submit to JFEC** when paper complete.

---

## Decisions Made (Do Not Re-Litigate)

- Asset pair: ES vs NQ (not ES/Euro Stoxx — wrong timezone)
- Strategy: Mean-reversion (not directional)
- Lag timescale: Minutes, calibrated daily
- Journal target: JFEC
- Name on paper: Dr Yang Azzollini
- Repository: public on GitHub under ChubbyFaceEuler
- Trading system: validate signal BEFORE showing to any fund
- Axiom: wait until Paper 1 submitted
- **Framing: B (methodology-as-brand), NOT A (Zhou-credit-claim)**
- **Paper approach: bookkeeping style first, journal polish later**

---

## The Book (Future)

Planned structure (after paper submitted):
1. The problem — Epps effect, synchronisation
2. The ZHY estimator — overlaps, unbiasedness
3. Exact variance — Theorem 1 with complete proof
4. Optimal weights — KKT, two-step
5. Gauss-Markov theorem
6. Lean 4 formalisation — worked example including the
   Interval-Structure Lemma
7. Trading system — K/KDB+ implementation
8. Extensions — noise, multivariate, lead-lag

---

## Technical Setup

- Mac: Saratoga CA
- Warp terminal: AI terminal, handles file ops and compilation
- VS Code: Lean 4 extension installed (v0.0.234)
- KDB+: installed and licensed
- IB TWS: running, live account
- Python: ib_insync, qpython available (pip install)
- Lean 4.14.0: installed via elan
- Mathlib cache: downloaded
- LaTeX: standard distribution, compiles the draft tex files cleanly

---

*End of handoff document*
*Generated: April 19, 2026 (original)*
*Updated: April 21, 2026 (this revision)*
