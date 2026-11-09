# Errata of On Response-Adaptive Targeting Strategies for Multi-Treatment Experiments

Errors found in the paper while formalizing it, with their corrections. Each entry gives where the
error is (the revision of the paper, the result, the page or equation), the error, the correction,
the declarations that state the corrected form, the kind of error and when it was found. Entries
are numbered `E1`, `E2`, … and never renumbered.

## E1. Lemma 4.5: sampling every treatment infinitely often does not give the componentwise CLT

- **Where:** arXiv:2606.17777v1, Lemma 4.5 (Joint CLT with Componentwise Scaling), Section 4.2,
  and its proof in Appendix A.2, end of Step 2 ("by the martingale CLT theorem").
- **Error:** the lemma assumes only `N_{n,k} → ∞` a.s. for every arm. The proof checks the
  self-normalized Lindeberg condition and then applies "the martingale CLT" to the martingale
  normalized by the random `√⟨M⟩_n`. The martingale CLTs of that family (Hall–Heyde, Theorem 3.2)
  need a stabilization hypothesis `⟨M⟩_n / s_n² → η²` for a deterministic `s_n`, which is never
  established. The statement is false without it: with two arms, pull arm 1 in block `j` until its
  self-normalized sum first exceeds `1`, then park on arm 2 for the rest of the block (blocks
  `a_{j+1} = 2^{a_j}`). Both arms are sampled infinitely often, yet at the end of each block the
  self-normalized statistic exceeds `1` with probability tending to `1`, not `ℙ(Z > 1) ≈ 0.159`.
- **Correction:** add the regularity hypothesis: for each arm there is a deterministic
  `c_{k,n} → ∞` with `N_{n,k} / c_{k,n} → 1` a.s. Theorems 4.2 and 5.1 are not affected, since
  there `N_{n,k} / n → v_k > 0` gives it with `c_{k,n} = v_k n`, and Theorems 4.1 and 5.2 do not
  use the lemma. Corollary 5.3, stated as a direct consequence of the lemma, is (E2); Lemma 6.1,
  which applies the lemma to any αRTS-FE design, inherits the problem. Write-up:
  `notes/regularity-gap.md`.
- **Lean:** `AlphaRAR.estimatorError_joint_tendsto_multivariateGaussian` states the lemma with the
  regularity hypothesis, with per-arm normalizers.
- **Kind:** false statement (missing hypothesis).
- **Found:** during the formalization, July 2026 (`notes/regularity-gap.md`).

## E2. Corollary 5.3: not a consequence of Lemma 4.5 under condition (ii) of Definition 5.1

- **Where:** arXiv:2606.17777v1, Corollary 5.3, Section 5, and Definition 5.1, condition (ii)
  (`h(n) = o(√n)`).
- **Error:** the corollary is derived as a direct consequence of Lemma 4.5, in the sparse regime
  (`v_k = 0`), where the regularity hypothesis that the lemma needs (E1) is not available. Under
  `h(n) = o(√n)`, a design that tracks its target gives a sparse arm about `√n` pulls, coupled
  with the fluctuations of the estimator, so that `N_{n,k} / c_{k,n} → 1` is not known for any
  deterministic `c_{k,n}`, and forced exploration does not set the scale.
- **Correction:** replace condition (ii) by `√(n log log n) ≪ h(n) = o(n)`. Theorem 5.1 needs
  only `h(n) = o(n)` (under Condition B forced exploration eventually stops); under the new
  condition, every arm fed by forced exploration has `N_{n,k} / h(n) → 1` a.s., which is the
  regularity of E1, and the corollary holds. `h(n) = n^{2/3}` satisfies the new condition and not
  the paper's. Write-up: `maths/sparse-clt-fix.md`.
- **Lean:** `AlphaRAR.IsExplorationSchedule` (condition (ii) as `h(n) = o(n)`),
  `AlphaRAR.aRTSFE_sparse_clt_of_contDiffAt` (Corollary 5.3 under the new condition),
  `AlphaRAR.pullCount_div_sched_tendsto_one`, `AlphaRAR.underExplored_eventually_empty` and
  `AlphaRAR.sched23_satisfies_schedule_hypotheses`.
- **Kind:** gap in the proof; the corrected statement changes a hypothesis.
- **Found:** during the formalization, July 2026 (`maths/sparse-clt-fix.md`).

## E3. Appendix A.2: the martingale LIL of Stout needs `⟨M⟩_n → ∞`

- **Where:** arXiv:2606.17777v1, Appendix A.2, proof of Theorem 4.2 (the bound
  `M_{n,k} = O(√(n log log n))` a.s., "by LIL for martingales (see Stout 1970)").
- **Error:** the law of the iterated logarithm for martingales that the proof cites assumes that the
  quadratic variation tends to infinity, which can fail for the assignment martingale of a general
  αRTS design: a design whose selection probabilities are in `{0, 1}` has `⟨M⟩ ≡ 0`.
- **Correction:** the increments are bounded by `1`, and the bound
  `M_{n,k} = O(√(n log log n))` a.s. holds for every martingale with bounded increments, with no
  hypothesis on `⟨M⟩`. The conclusion of the step, and Theorem 4.2, are unaffected.
- **Lean:** `AlphaRAR.ae_isBigO_sqrt_nat_mul_loglog_of_bdd` (the unconditional bounded-increment
  LIL), applied in `AlphaRAR.ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog`.
- **Kind:** gap in the proof.
- **Found:** during the formalization, July 2026.

## E4. Appendix A.2, Step 2 of the proof of Lemma 4.5: inverted inequality

- **Where:** arXiv:2606.17777v1, Appendix A.2, end of Step 2 of the proof of Lemma 4.5.
- **Error:** the proof writes `ℙ(L_{n,k}(ε) ≤ η) ≤ ℙ(N_{n,k} ≤ m) → 0`, which says that
  `L_{n,k}(ε)` is not small.
- **Correction:** `ℙ(L_{n,k}(ε) > η) ≤ ℙ(N_{n,k} < m) → 0`.
- **Lean:** `AlphaRAR.tendstoInMeasure_lindeberg_wArray` (the Lindeberg condition).
- **Kind:** typo.
- **Found:** during the formalization, July 2026 (`notes/regularity-gap.md`, section 5).
