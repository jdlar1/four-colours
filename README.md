<img src="assets/icon.svg" width="64" height="64" alt="">

# Four-Colour Theorem: Kempe-Span Theory & Reduced Unavoidable Sets

> **Author's note:** I come from an engineering background—I am not a research mathematician. This repository grew out of experimenting with **Gemini 4 Neon** as an orchestrator together with **GPT-6.2 Astra** subagents doing the main heavy computational work (plus proof/Lean 4 and adversarial-review subagents on a single workstation), to see what interesting, genuinely machine-checkable mathematical results could be produced without trusting LLM prose. Every claim below is anchored strictly to external verifiers (the original 1997/2010 C checkers and the Lean 4 kernel).

Verified computational improvements to the classical Four-Colour Theorem unavoidable sets alongside a pure-math characterization of Kempe-chain block spans (partially formalized in Lean 4).

## Summary of Results

| Result | Metric | Baseline | Verification | Directory |
|---|---|---|---:|---|
| **RSST-format unavoidable set** (D+C, ring $\le 14$) | **604 configs** (`284 D + 320 C`) | RSST 1997: `633` (`249 D + 384 C`) | Unmodified RSST `reduce.c` + `discharge.c` (`present5`–`present12`) | [four-colours/sota_rules_v2/](four-colours/sota_rules_v2/) |
| **Purely D-reducible unavoidable set** (refined rules) | **2,484 configs** (`91` at ring 16) | Steinberger 2010: `2,822` (`161` at ring 16) | Unmodified Steinberger `discharge.c` (`p5`–`p12`) + ring-16 patched `reduce.c` | [four-colours/sota_d/best_bundle/](four-colours/sota_d/best_bundle/) |
| **Purely D-reducible** (unmodified `L_42` rules) | **2,636 configs** (`127` at ring 16) | Steinberger 2010: `2,822` | Same as above | [four-colours/sota_d/fixed_l42_bundle/](four-colours/sota_d/fixed_l42_bundle/) |
| **Purely D-reducible** (ring-16 minimization) | **75 at ring 16** (`2,826` total) | Steinberger 2010: `161` at ring 16 | Same as above | [four-colours/sota_d/ring_stress_bundle/](four-colours/sota_d/ring_stress_bundle/) |
| **Fixed-rule RSST irredundancy & D/C split** | **633** (`294 D + 339 C`) + 633 private witnesses | RSST 1997 (`rules` byte-identical) | Unmodified RSST `reduce.c` + `discharge.c` (`present5`–`present11`) | [four-colours/sota/](four-colours/sota/) |
| **Theorem A/B: Kempe Spans = Birkhoff–Lewis** | $B_\alpha \cap B_\beta = \mathrm{BL}_k$, $\dim B_\alpha = \frac{T_k + (-1)^k}{2}$ ($k \ge 2$) | Classical BL / Riordan $R_k$ | Prose proof + numerical check ($k \le 9$); **Theorem B & $\mathrm{BL}_k \le B_\alpha \cap B_\beta$ verified in Lean 4** | [four-colours/analytical/](four-colours/analytical/), [four-colours/lean_theorem62/](four-colours/lean_theorem62/) |

## Repository Layout

- **[four-colours/](four-colours/)** — Introductory Tait-colouring notes, pentagon cap analysis (`caps.md`, `caps.py`), and distance-3 witness (`three_swaps.py`).
- **[four-colours/recon/](four-colours/recon/)** — Unmodified RSST 1997 archive (`rsst/`), `33333` C-reducibility certificates (`33333.conf`, decagon wheel census), fullerene check, and block-count analysis.
- **[four-colours/sota_rules_v2/](four-colours/sota_rules_v2/)** — Primary **604-configuration** (`284 D + 320 C`) RSST-format proof bundle (`best_bundle/`), verification logs (`verification/`), and audit script (`verify.sh`).
- **[four-colours/sota_d/](four-colours/sota_d/)** — Purely D-reducible proof bundles (**2,484** in `best_bundle/`, **2,636** fixed-`L_42` in `fixed_l42_bundle/`, **75 ring-16** in `ring_stress_bundle/`), Steinberger's original archive (`steinberger/`, `source.tar`), and replay script (`verify.sh`).
- **[four-colours/sota/](four-colours/sota/)** — Fixed-rule RSST irredundancy certificate (`private-witnesses.tsv`), improved fixed-rule D/C split (`bundle/`: `294 D + 339 C`), and radius-1 degree-5 census (`h1_results.md`).
- **[four-colours/analytical/](four-colours/analytical/)** — Complete proof of $B_\alpha \cap B_\beta = \mathrm{BL}_k$ and $\dim B_\alpha = (T_k + (-1)^k)/2$ (`theorem62_proof.md`), verification script (`theorem62_check.py`), and analytical barrier memo (`thrust2_memo.md`).
- **[four-colours/lean_theorem62/](four-colours/lean_theorem62/)** — Lean 4 (`v4.37.0-rc1` + Mathlib) formalization (2,217 lines). Kernel-verifies **Theorem B** (`Theorem62.theorem_B`), **`Theorem62.theorem_A_BL_le`** ($\mathrm{BL}_k \le B_\alpha \cap B_\beta$), `kempeSpan_eq_fourier`, and `finrank_kempeSpan` with zero `sorry` and standard axioms only (`[propext, Classical.choice, Quot.sound]`). The reverse inclusion $B_\alpha \cap B_\beta \le \mathrm{BL}_k$ and `dim BL_k = R_k` remain to be formalized.
- **[priority/](priority/)** — SHA-256 manifests and Bitcoin-anchored OpenTimestamps (`.ots`) priority proofs.

## Quick Verification

```sh
# 1. Verify the 604-configuration RSST-format bundle (requires gcc, python3 + networkx)
cd four-colours/sota_rules_v2 && ./verify.sh best_bundle

# 2. Verify the 2,484-configuration purely D-reducible bundle (requires gcc, python3 + networkx)
cd four-colours/sota_d && sh verify.sh best_bundle 8

# 3. Verify the Lean 4 Theorem B formalization (requires elan / Lean 4)
cd four-colours/lean_theorem62 && lake exe cache get && lake build Theorem62.AxiomCheck

# 4. Run the Theorem 62 Python checks (requires numpy)
cd four-colours/analytical && python3 theorem62_check.py
```

## Verification Scope & Caveats

- **C-verified unavoidable sets (`604`, `2,484`, `2,636`, `2,826/75`)**: Every bundle passes the original RSST (`reduce.c`, `discharge.c`) or Steinberger (`discharge.c`, plus the ring-16 array-bound fix to `reduce.c`) C verifiers across hub degrees `5–12` with zero duplicate configurations. Extension from `present12`/`p12` to all $d > 12$ relies on the audited `[-2, +2]` spoke-offset locality and maximum source degree `8`; it is not formalized in Coq.
- **Pure mathematics (`Theorem A/B`)**: `four-colours/analytical/theorem62_proof.md` proves $B_\alpha \cap B_\beta = \mathrm{BL}_k$ and $\dim B_\alpha = (T_k + (-1)^k)/2$ for all $k \ge 2$ (also admitting a short $O(2)/SO(3)$ representation-theoretic proof that explains the principal-angle spectrum $|P_{2m}(0)|$, with first non-trivial cosine $1/2 = |P_2(0)|$). In `four-colours/lean_theorem62/`, Lean 4 kernel-verifies `Theorem62.theorem_B`, `kempeSpan_eq_fourier`, `finrank_kempeSpan`, and `Theorem62.theorem_A_BL_le` ($\mathrm{BL}_k \le B_\alpha \cap B_\beta$) with zero `sorry` and standard axioms only; the reverse inclusion $B_\alpha \cap B_\beta \le \mathrm{BL}_k$ and `dim BL_k = R_k` remain to be formalized in Lean 4.
- **Priority timestamps**: `priority/` contains SHA-256 manifests and OpenTimestamps (`.ots`) proofs, including completed Bitcoin block attestations.

