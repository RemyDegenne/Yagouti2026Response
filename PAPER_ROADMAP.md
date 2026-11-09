# Paper roadmap: On Response-Adaptive Targeting Strategies for Multi-Treatment Experiments

Paper: RemyDegenne/Yagouti2026Response · LMLExplore afd365492580 · LMLRoadmaps d01bdd6b89ce · Refreshed 2026-11-09

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Ville's inequality for nonnegative supermartingales, finite and infinite horizon | exists | `MeasureTheory.Supermartingale.measure_exists_le_le` | – | `ForLMLExplore/Probability/Martingale/Freedman.lean` |
| R2 | Freedman's inequality, with the predictable quadratic variation as variance process | exists | `LMLExplore.measure_exists_le_sum_and_sum_condExp_sq_le_le` | – | `ForLMLExplore/Probability/Martingale/Freedman.lean` |
| R3 | The L¹ bound 2√B from an inverse-square tail bound (layer cake) | exists | `MeasureTheory.lintegral_ofReal_le_two_mul_sqrt_of_measure_lt_le` | – | `ForLMLExplore/MeasureTheory/Integral/TailBoundLIntegral.lean` |
| R4 | Indistinguishable processes | exists | `ProbabilityTheory.Indistinguishable` | – | `ForLMLExplore/Probability/Process/Indistinguishable.lean` |
| R5 | The variance as the central second moment | exists | `ProbabilityTheory.variance_eq_integral` | – | `ForLMLExplore/Probability/Moments/Variance.lean` |
| R6 | Linear images of a centred multivariate Gaussian, with covariance G S Gᵀ | exists | `TauCeti.Probability.map_affine_multivariateGaussian` | – | `ForLMLExplore/Probability/Distributions/Gaussian/MultivariateGaussianMap.lean` |
| R7 | Chi-square laws and Cochran's theorem for the orthogonal projection of a standard Gaussian | exists | `Submodule.map_norm_sq_starProjection_stdGaussian` | – | |
| R8 | Conditional law and conditional mean of the feedback in a stationary bandit | exists | `Learning.IsAlgEnvSeq.condExp_feedback_comp` | – | `ForLMLExplore/SequentialLearning/IsAlgEnvSeq.lean` |
| R9 | The successive responses of one arm along a run are i.i.d. with the arm's law | exists | `Bandits.hasLaw_rewardByCount_infinitePi` | – | `YDK2026/OptionalSkipping.lean` |
| R10 | Stochastic orders o_p and O_p and their calculus | staged | S1 | proved | `ForLMLExplore/Probability/StochasticOrder.lean` |
| R11 | Convergence in distribution: eventual congruence, reindexing, Slutsky for products, tightness, the delta-method remainder | staged | S1 | proved | `ForLMLExplore/MeasureTheory/Function/TendstoInDistribution.lean`, `ForLMLExplore/MeasureTheory/Function/TendstoInMeasure.lean` |
| R12 | Predictable quadratic variation of a square-integrable martingale | staged | S2 | proved | `ForLMLExplore/Probability/Martingale/QuadraticVariation.lean` |
| R13 | The previous-index filtration | staged | S2 | proved | `ForLMLExplore/Probability/Process/Filtration.lean` |
| R14 | Doob's L² maximal inequality and the O_p(√n) growth of square-integrable martingales | staged | S2 | proved | `ForLMLExplore/Probability/Martingale/MartingaleMaximal.lean`, `ForLMLExplore/Probability/Martingale/MartingaleRate.lean` |
| R15 | Kronecker's lemma | staged | S3 | proved | `ForLMLExplore/Analysis/SpecificLimits/Kronecker.lean` |
| R16 | Strong law of large numbers for martingales | staged | S3 | proved | `ForLMLExplore/Probability/Martingale/MartingaleSLLN.lean` |
| R17 | Martingale law of the iterated logarithm, upper half, with the sharp constant, for bounded and for growing increments | staged | S4 | proved | `ForLMLExplore/Probability/Martingale/Freedman.lean`, `ForLMLExplore/Probability/Martingale/LILCommon.lean`, `ForLMLExplore/Probability/Martingale/LIL.lean`, `ForLMLExplore/Probability/Martingale/LILTruncation.lean` |
| R18 | Hartman–Wintner law of the iterated logarithm for i.i.d. sums, upper half | staged | S4 | proved | `ForLMLExplore/Probability/HartmanWintner.lean`, `ForLMLExplore/Probability/HartmanWintnerTruncation.lean`, `ForLMLExplore/MeasureTheory/Integral/TsumMeasureIoi.lean` |
| R19 | Doob's optional skipping theorem | staged | S5 | proved | `YDK2026/OptionalSkipping.lean` |
| R20 | Martingale central limit theorem for triangular arrays, Lindeberg form | staged | S6 | proved | `ForLMLExplore/Probability/Martingale/MartingaleCLTIngredients.lean`, `ForLMLExplore/Probability/Martingale/MartingaleCLT.lean` |
| R21 | Anscombe's random-index central limit theorem | staged | S6 | proved | `ForLMLExplore/Probability/AnscombeCLT.lean` |
| R22 | Quadratic bounds on the first-order Taylor remainder | staged | S7 | proved | `ForLMLExplore/Analysis/Calculus/TaylorRemainder.lean` |
| R23 | Means of a kernel, moments of the feedback along a run, diverging pull counts | staged | S8 | proved | `ForLMLExplore/SequentialLearning/Means.lean`, `ForLMLExplore/SequentialLearning/IsAlgEnvSeq.lean`, `ForLMLExplore/SequentialLearning/PullCount.lean`, `ForLMLExplore/Probability/HasCondDistrib.lean` |
| R24 | Fisher information, and the variance as inverse Fisher information in a natural exponential family | staged | S9 | todo | |
| R25 | The positive-part convergence lemma (Lemma C.5) | paper | | proved | `ForLMLExplore/Analysis/SpecificLimits/Convergence.lean` |
| R26 | Increment control (Lemma C.6) and the o_p increment bound of a martingale family (proof of Lemma A.3) | paper | | proved | `ForLMLExplore/Analysis/Normed/Group/IncrementControl.lean`, `ForLMLExplore/Probability/Martingale/MartingaleIncrement.lean` |
| R27 | Drift-sign o_p(√n) deviation bounds and the assembled deviation bound of the allocation | paper | | proved | `ForLMLExplore/Probability/StochasticOrder/DeviationBound.lean`, `ForLMLExplore/Probability/StochasticOrder/PropDev.lean` |
| R28 | The Pearson statistic, its quadratic-form rewriting, the projection I − ssᵀ and its null limit (Lemma 6.1) | paper | | todo | `ForLMLExplore/Analysis/Matrix/Projection.lean` |

## Notes

- R1, R2, R3, R5, R6, R8: the paper still has its own copies, in the files listed; they are to be
  deleted and their uses moved to the linked declarations. R1: `smul_measure_sup_le_integral_zero`
  and `smul_measure_exists_ge_le_integral_zero`. R6: `multivariateGaussian_map_matrix` is the case
  `m = 0`, `c = 0` of Tau Ceti's affine form. R8: `condExp_feedback_comp_stationaryEnv` and
  `condExp_feedback_stationaryEnv` are LML's `IsAlgEnvSeq.condExp_feedback_comp` and
  `IsAlgEnvSeq.condExp_feedback` for `Environment.bandit ν`, rewritten with `Learning.means_bandit`.
- R2: the local `measure_exists_ge_le_exp*` bound a martingale with increments bounded by `c`, with
  the variance proxy `1 + δ`. LMLExplore's form is for partial sums `∑ k < n, X k` with `X n`
  `ℱ (n + 1)`-measurable and the variance process `∑ k < n, μ[X k ^ 2 | ℱ k]`, which is `⟨M⟩`
  (`predQuadVar_ae_eq_sum`); its exponent `a²/(2(σ² + ab/3))` gives the `1 + δ` form once
  `ab/3 ≤ δσ²`, and `LMLExplore.measure_exists_le_mul_sum_sub_mul_sum_condExp_sq_le` is the
  fixed-parameter form. The ReinforcementLearning roadmap's Layer 3.1 owns Freedman's inequality
  and asks that no separate supermartingale argument be built: R17 is to be rebased on it.
- R3: LMLExplore's hypothesis `P(x < f) ≤ a / x²` is weaker than the local `μ {t ≤ Y} ≤ B / t²`.
- R4: Mathlib's `ProbabilityTheory.Indistinguishable` is a `def` for `∀ᵐ ω, ∀ i, X i ω = Y i ω`.
  The local `AlphaRAR.Indistinguishable` is a structure with that single field only because the
  `@[characterization]` annotations of `YDK2026/` read the relation off the head of the statement;
  a port uses Mathlib's.
- R7: Tau Ceti covers the blueprint's chapter `chap:pre_cochran`: `TauCeti.Probability.chiSquaredMeasure`,
  `TauCeti.Probability.gaussianReal_map_sq`, `TauCeti.Probability.map_sum_sq_pi_gaussianReal`
  and, for Cochran's theorem, `Submodule.map_norm_sq_starProjection_stdGaussian`
  (`‖P_K x‖²` has the chi-square law with `finrank K` degrees of freedom). R28 builds on them; its
  projection `I − ssᵀ` is the star projection onto `(ℝ ∙ s)ᗮ`.
- R9: LML proves it on `P.prod (streamMeasure ν)`, where `rewardByCount A Y a (m + 1)` is the
  response at the `(m + 1)`-th pull of `a`, taken from an auxiliary stream when `a` has fewer
  pulls. When `a` is pulled infinitely often almost surely, it agrees almost surely with the local
  sampled response of `iIndepFun_sampledResponse` and `map_sampledResponse_eq`, which the paper
  derives from its own optional skipping theorem (R19).
- R10–R23: the declarations in the namespace `AlphaRAR` move to LMLExplore's namespaces in a port.
- R10: the local orders are of order one (`IsLittleOpOne`, `IsBigOpOne`), for real random
  variables, along `atTop`. S1 asks for general rates, normed spaces and filters; the order-one
  forms become the rate-one case.
- R11: S1 also asks for the delta method itself, which the paper assembles in `YDK2026/` from
  `tendstoInMeasure_smul_littleO_of_tight`.
- R12: the local file defines only `⟨M⟩` (Mathlib's `predictablePart` of `M²`), and proves
  `⟨M + N⟩ = ⟨M⟩ + ⟨N⟩` for conditionally orthogonal martingales. S2 asks for the covariation
  `⟨M, N⟩`, of which these are special cases.
- R14: the local inequality is the L¹ form `∫⁻ max_{k ≤ N} |M k| ≤ 2 √E[M_N²]`, with variants for
  backward increments and for finite families of martingales. S2 asks for Doob's Lᵖ inequality,
  from which it follows.
- R16: the local strong law is the case `p = 2` (`martingale_div_weight_ae_tendsto_zero`,
  `martingale_div_predQuadVar_ae_tendsto_zero`). S3 asks for Chow's theorem for `1 ≤ p ≤ 2`.
- R17: the exponential supermartingale and the Freedman bounds of `Freedman.lean` duplicate R1 and
  R2, which the port uses instead. The new material is the block Borel–Cantelli engine
  (`ae_eventually_forall_lt_of_summable`, `ae_eventually_forall_le_lt_of_summable`) and the files
  `LILCommon.lean`, `LIL.lean` and `LILTruncation.lean`. Only the upper half (`limsup ≤ 1`) is
  proved; S4 asks for Stout's theorem, both halves.
- R18: only the upper half (`limsup ≤ 1`). `TsumMeasureIoi.lean` gives Mathlib's
  `ProbabilityTheory.tsum_prob_mem_Ioi_lt_top`, stated there for the measure of a `MeasureSpace`
  only, for any finite measure.
- R19: the file is in the paper's folder, but its abstract part, up to `iIndepFun_sampledSeq` and
  `map_sampledSeq_eq`, names no object of the paper: it moves to `ForLMLExplore/Probability/`
  before a port, and `hfact_stationaryEnv`, `iIndepFun_sampledResponse` and
  `map_sampledResponse_eq` stay in the paper (see R9). The local theorem is for real values; S5
  asks for any measurable space.
- R20: the local theorem is for real arrays (`AlphaRAR.MartDiffArray`), with a constant limit
  variance `σ²`.
- R21: the local theorem is for i.i.d. sums, with the regularity `N_n / c_n → 1` almost surely. S6
  asks for Anscombe's condition and the regularity in probability.
- R22: the local bound has the constant `K`; S7 asks for the sharp `K / 2`.
- R23: `Kernel.means ν k = (ν k)[id]` is what LML's `Learning.means_bandit` computes
  `(Environment.bandit ν).means` to be. The two `condExp_feedback*_stationaryEnv` lemmas of
  `IsAlgEnvSeq.lean` are R8, not part of this item.
- R24: not formalized. The paper uses it only in Remark 4.3 (asymptotic efficiency), through
  Proposition C.4. LMLExplore's `MeasureTheory.Measure.hasDerivAt_natParam` (the derivative
  `1 / ψ''(η(μ))` of the natural parameter in the mean) is the core of the mean-parameter identity.
- R25–R27: lemmas that name no object of the paper but serve only the bookkeeping of its proofs,
  too specific for LMLExplore. They sit in `ForLMLExplore/` and are to move to `YDK2026/`.
- R28: only `isProjection_one_sub_vecMulVec` is formalized; the statistic, its rewriting and its
  limit are not.

## Proposed targets

### S1. Stochastic orders and convergence in distribution

For random variables `X : ι → Ω → E` with values in a real normed space, probability measures
`μ : ι → Measure Ω`, a filter `l` and a rate `r : ι → ℝ`:

- `o_p(r)`, the convergence of `X i / r i` to `0` in probability, and `O_p(r)`, the eventual
  uniform tail bound `μ i {‖X i‖ > M r i} < ε`. Their calculus: sums, products by `o_p` and `O_p`
  scalars, `o_p ⟹ O_p`, domination, almost sure convergence `⟹ o_p(1)`, a bounded `p`-th moment
  `⟹ O_p(1)` (Markov), `O_p(1)` iff the laws form an `IsTightMeasureSet`, and convergence in
  distribution `⟹ O_p(1)` [vdV98, Section 2.2, Theorem 2.4].
- Complements to Mathlib's `TendstoInDistribution`: congruence when the sequences agree almost
  everywhere only eventually; reindexing along a map that tends to the filter; convergence to a
  random variable as convergence to the identity on its law; Slutsky's theorem for scalar
  multiplication, `Y i → c` in probability and `X i ⇒ Z` give `Y i • X i ⇒ c • Z` [vdV98, Lemma 2.8].
- The delta method [vdV98, Theorem 3.1]: in finite dimension, if `r i → ∞`,
  `r i • (X i − θ) ⇒ Z` and `T` is differentiable at `θ`, then
  `r i • (T (X i) − T θ) ⇒ T'(θ) Z`; its core is the remainder lemma: `a i • φ (S i) → 0` in
  probability when `a i • S i` is `O_p(1)`, `S i → 0` in probability and `φ = o(‖·‖)` at `0`.

[vdV98] A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998.

### S2. Discrete-time martingales: predictable quadratic covariation and maximal inequalities

For real processes indexed by `ℕ` and adapted to a filtration:

- The predictable quadratic covariation `⟨M, N⟩` of two square-integrable martingales, the
  predictable part of `M N` in Mathlib's Doob decomposition (`predictablePart`), and
  `⟨M⟩ = ⟨M, M⟩` [Wil91, Section 12.12]: increments `E[ΔM_n ΔN_n | ℱ_n]`; null at `0` and
  predictable; `⟨M⟩` nonnegative and nondecreasing, with `⟨M⟩_n ≤ c² n` for increments bounded by
  `c`; `M N − ⟨M, N⟩` a martingale, and uniqueness up to Mathlib's `Indistinguishable`; symmetry,
  bilinearity and polarization; the discrete Itô isometry `E[M_n²] = E[M_0²] + E[⟨M⟩_n]`.
- The previous-index filtration `n ↦ ℱ (n − 1)`, trivial at `0`, against which the increment at
  step `n` is fresh.
- Doob's Lᵖ inequality [Wil91, Theorem 14.11]: for a nonnegative submartingale and `1 < p < ∞`,
  `‖max_{k ≤ n} X_k‖_p ≤ p / (p − 1) ‖X_n‖_p`; its corollary for `|M|`, `M` a martingale, and the
  L¹ form `E[max_{k ≤ n} |M_k|] ≤ 2 ‖M_n‖_2`.
- With S1: a square-integrable martingale null at `0` whose increments have second moments at most
  `σ²` is `O_p(√n)`.

[Wil91] D. Williams, *Probability with Martingales*, Cambridge University Press, 1991.

### S3. Strong law of large numbers for martingales

- Kronecker's lemma, in a real normed space [Shi19, Chapter 4, Section 3]: if `∑ x_k` converges
  and `b_n > 0` is nondecreasing with `b_n → ∞`, then `b_n⁻¹ ∑_{k ≤ n} b_k x_k → 0`.
- Chow's strong law [Cho67], [HH80, Theorem 2.18]: for a real martingale `S_n = ∑_{i ≤ n} X_i`,
  a positive nondecreasing predictable `U_n` and `1 ≤ p ≤ 2`, the series `∑ X_i / U_i` converges
  almost surely on `{∑ U_i^{-p} E[|X_i|^p | ℱ_{i−1}] < ∞}`, and `S_n / U_n → 0` almost surely on
  its intersection with `{U_n → ∞}`. Corollaries: `M_n / ⟨M⟩_n → 0` almost surely on
  `{⟨M⟩_n → ∞}` (with S2), and `M_n / n → 0` almost surely when `∑ E[(ΔM_k)²] / k² < ∞`.

[Cho67] Y. S. Chow, On a strong law of large numbers for martingales, *Ann. Math. Statist.* 38
(1967), 610–611. [HH80] P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*,
Academic Press, 1980. [Shi19] A. N. Shiryaev, *Probability-2*, 3rd ed., Springer, 2019.

### S4. Laws of the iterated logarithm

- Stout's martingale law of the iterated logarithm [Sto70]: for a real martingale with
  `s_n² = ⟨M⟩_n → ∞` almost surely and increments `|ΔM_n| ≤ K_n s_n / √(2 log log s_n²)`, where
  `K_n` is predictable and tends to `0` almost surely,
  `limsup M_n / √(2 s_n² log log s_n²) = 1` almost surely, both halves, with the
  bounded-increment case and the rates in `IsBigO` form. Built on Freedman's inequality
  (ReinforcementLearning roadmap, Layer 3.1, in LMLExplore) by a Borel–Cantelli argument over
  geometric blocks [Fre75].
- The variant normalized by a deterministic linear bound `⟨M⟩_n ≤ v n`, for increments growing like
  `o(√(n / log log n))`.
- The Hartman–Wintner law [HW41]: for i.i.d. real variables with mean `0` and variance
  `σ² ∈ (0, ∞)`, `limsup S_n / √(2 σ² n log log n) = 1` and `liminf … = −1` almost surely.

[Sto70] W. F. Stout, A martingale analogue of Kolmogorov's law of the iterated logarithm,
*Z. Wahrscheinlichkeitstheorie verw. Gebiete* 15 (1970), 279–290. [Fre75] D. A. Freedman, On tail
probabilities for martingales, *Ann. Probab.* 3 (1975), 100–118. [HW41] P. Hartman and A. Wintner,
On the law of the iterated logarithm, *Amer. J. Math.* 63 (1941), 169–176.

### S5. Optional skipping

Let `D_j` be `{0, 1}`-valued and adapted to a filtration `𝒢`, with infinitely many ones almost
surely, and `Y_j` with values in a measurable space, `𝒢_k`-measurable for `j < k`, and fresh on
the hits: `μ (Y_j ⁻¹' E ∩ S) = ρ E * μ S` for every `S ∈ 𝒢_j` contained in `{D_j = 1}`. Then `Y`
read at the successive hit times is i.i.d. with law `ρ` [Doo36], [Doo53, Chapter III, Section 5].
Halmos's theorem on gambling systems [Hal39] is the case of i.i.d. `Y` and a predictable selection.

[Doo36] J. L. Doob, Note on probability, *Ann. of Math.* 37 (1936), 363–367. [Doo53] J. L. Doob,
*Stochastic Processes*, Wiley, 1953. [Hal39] P. R. Halmos, Invariants of certain stochastic
transformations: the mathematical theory of gambling systems, *Duke Math. J.* 5 (1939), 461–478.

### S6. Martingale central limit theorem and Anscombe's theorem

- The martingale central limit theorem for triangular arrays [HH80, Corollary 3.1]: for real
  square-integrable martingale differences `X_{n,i}` with row filtrations, if
  `∑_i E[X_{n,i}² | ℱ_{n,i−1}] → σ²` in probability and the conditional Lindeberg condition holds,
  then `∑_i X_{n,i} ⇒ 𝒩(0, σ²)`, in the shape of Mathlib's i.i.d. central limit theorem
  `tendstoInDistribution_inv_sqrt_mul_sum_sub`. The mixed-normal limit for a random `η²` under
  nested filtrations [HH80, Theorem 3.2], and the form for `ℝᵈ`-valued arrays with conditional
  covariances tending to `Σ`, through Mathlib's Cramér–Wold theorem.
- Anscombe's theorem [Ans52], [Gut09, Section 1.3]: if `Y_n ⇒ Z` and `Y` satisfies Anscombe's
  condition (for every `ε > 0` there are `δ > 0` and `n_0` with
  `P(max_{m : |m − n| ≤ δ n} |Y_m − Y_n| > ε) < ε` for `n ≥ n_0`), then `Y_{N_n} ⇒ Z` for
  integer-valued `N_n` with `N_n / c_n → 1` in probability and `c_n → ∞`. Instances: the
  randomly indexed i.i.d. sum `S_{N_n} / √N_n ⇒ 𝒩(0, σ²)`, and its martingale analogue.

[HH80] as in S3. [Ans52] F. J. Anscombe, Large-sample theory of sequential estimation,
*Proc. Cambridge Philos. Soc.* 48 (1952), 600–607. [Gut09] A. Gut, *Stopped Random Walks*, 2nd ed.,
Springer, 2009.

### S7. Taylor remainder bounds

For `f : E → F` between real normed spaces, differentiable on a convex set `s` with
`‖f' z − f' θ‖ ≤ K ‖z − θ‖` on `s`: `‖f x − f θ − f' θ (x − θ)‖ ≤ K / 2 ‖x − θ‖²` on `s`, from
Mathlib's mean-value inequalities along segments. For `f` of class `C²` at `θ`: the same bound near
`θ` for some `K`, and `f x − f θ − f' θ (x − θ) = O(‖x − θ‖²)` at `θ`; at a local minimum,
`f x − f θ ≤ K ‖x − θ‖²` near `θ` [Car71].

[Car71] H. Cartan, *Differential Calculus*, Hermann, 1971.

### S8. Means and moments of the feedback along a run

- The means `k ↦ (ν k)[id]` of a kernel `ν : Kernel 𝓐 𝓨` into a Banach space, with their
  measurability, and their identification with LML's `Environment.means` of `Environment.bandit ν`
  (`means_bandit`).
- Lᵖ from a conditional distribution: if `HasCondDistrib Y X κ P`, `P` is finite and the `p`-th
  moments of the laws `κ x` are bounded uniformly in `x`, then `Y ∈ Lᵖ(P)`. Hence, for a run of
  any algorithm in any environment whose feedback kernels have uniformly bounded `p`-th moments,
  every feedback `Y n` is in Lᵖ.
- With trivial observations (`𝓞 = Unit`), `filtrationObs (n + 1) = filtration n`.
- Pathwise facts on pull counts: a diverging count, or a positive limiting proportion, forces
  infinitely many pulls [LS20, Chapter 4].

[LS20] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.

### S9. Fisher information

The Fisher information `I(θ) = E_θ[(∂_θ log p_θ)²]` of a one-parameter family of laws dominated
by a measure, with differentiable log-density; the reparametrization rule
`I(θ) = I(η(θ)) η'(θ)²`; and, for the natural exponential family generated by a measure `ρ` and a
statistic `T` (LMLExplore's `expFamilyMeans` and `natParam`), `I(η) = ψ''(η)`, the variance of `T`,
and in the mean parametrization `I(μ) = 1 / ψ''(η(μ))`, from `hasDerivAt_natParam` [LC98,
Section 2.5].

[LC98] E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998.
