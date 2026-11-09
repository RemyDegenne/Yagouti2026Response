# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `AlphaRAR/`.

**Status.** Every challenge is proved. The challenges were regenerated on 2026-11-09, when the project
moved to LMLExplore; `scripts/comparator-verify.sh` has to be run again on them.

Each challenge is one file that imports LML and Mathlib modules only (the project does not use
LMLExplore's definitions yet), and modules of Lean's own library, no project modules and no
sibling helpers.

## The trust story

For each headline theorem `AlphaRAR.<name>` there is a challenge file `Challenge_<name>.lean` and a
config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 4.1 (strong consistency and rates) | `aRTS_LLN` |
| Theorem 4.2 (i), equation (5) (proportion deviations, `o_P(√n)`) | `aRTS_prop_dev` |
| Theorem 4.2 (i), equation (6) (proportion deviations, `O(√(n log log n))` a.s.) | `aRTS_prop_dev_ae` |
| Theorem 4.2 (ii), equation (9) (joint asymptotic normality) | `aRTS_clt_joint` |
| Theorem 5.2 (consistency and rate for sparse targets) | `aRTSFE_sparse_rate_of_isARTSFE` |
| Corollary 5.3 (componentwise CLT, under the corrected schedule condition) | `aRTSFE_sparse_clt_of_contDiffAt` |

Each challenge states the theorem with `sorry`, with every definition of the project that the
statement rests on copied verbatim from its source by
[challenge-gen](https://github.com/LeanTrustBuilders/challenge-gen); the definitions of
LMLExplore, LML, Tau Ceti and Mathlib that it uses are imported. A reader checks the *statement*
(the challenge file) by hand and lets comparator check that the project proves exactly it, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, the proofs replayed through the
kernel. The config also lists the lemmas the definitions use, left `sorry` in the challenge and
proved by the project, and the theorems Lean makes of the proofs inside definitions.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).
