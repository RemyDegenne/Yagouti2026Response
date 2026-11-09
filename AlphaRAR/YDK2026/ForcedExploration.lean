/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.ForLMLExplore.Analysis.Calculus.TaylorRemainder
public import AlphaRAR.YDK2026.ARTSNormality
public import AlphaRAR.YDK2026.PropDevLIL
public meta import TrustAnnotations

/-!
# Forced exploration and sparse targets

This file develops the forced-exploration variant `aRTSFE` of the aRTS family (Section 5 of the
paper). Forced exploration samples the least-explored arms whenever some arm has been pulled fewer
than `h(m)` times (`h` an *exploration schedule*), which guarantees every arm is sampled infinitely
often.

The whole point of the generic-conditions modularisation is that the asymptotic theory needs
**nothing** design-specific beyond a hitting time `ℓ_{n,k}` satisfying the generic conditions. The
`aRTSFE` design satisfies them with the forced-exploration hitting time — the last time arm `k` was
either under-sampled *or* under-explored (`count ≤ h(m)`). Both the strong consistency of the
paper's Theorem 4.1 and the normality of its Theorem 4.2 (deviation bounds and the joint CLT) then
follow by reusing the abstract-hitting-time theorems (`consistency_of_hitting`,
`prop_dev_of_hitting`, `prop_dev_ae_of_hitting`, `count_sub_smul_ae_of_hitting`,
`clt_joint_of_hitting`), the *only* new ingredients being the smallness bounds on
`N_ℓ - ℓ ρ̂_ℓ`: `≤ (h(ℓ))^+ = o(n)` for consistency, and — under Condition
**B**, where forced exploration eventually switches itself off — `≤ C(ω)` for the `√n`-scaled
deviations, so `o(√n)` and `O(√(n log log n))`. Only `h(m) = o(m)` is ever used; the paper's
`h(m) = o(√m)` is not needed anywhere (see `IsSqrtSmall`).

## Main results

* `AlphaRAR.IsExplorationSchedule`, `AlphaRAR.aRTSFEUnder`.
* `AlphaRAR.IsARTSFE` — the design-family predicate, on histories, `IsARTS`'s analogue for `aRTSFE`;
  `AlphaRAR.throttle_of_isARTSFE` and `AlphaRAR.fe_of_isARTSFE` transport it to the process.
* `AlphaRAR.aRTSFE_proportion_tendsto` — a.s. `N_{n,k}/n → v_k`, `ρ̂_{n,k} → v_k` for `aRTSFE`.
* `AlphaRAR.aRTSFE_prop_dev`, `AlphaRAR.aRTSFE_prop_dev_ae`, `AlphaRAR.aRTSFE_count_sub_smul_ae`,
  `AlphaRAR.aRTSFE_clt_joint` — Theorem 4.2 of the paper, for `aRTSFE`.

The sparse targets (consistency and rate, and the sparse componentwise CLT) are in
`AlphaRAR.YDK2026.ForcedExplorationSparse`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Real
open scoped Topology ENNReal NNReal Matrix

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- An **exploration schedule**, in the weakened form this development uses: a nondecreasing
threshold `h(m)` with `h(m) → ∞` and `h(m) = o(m)`. Monotonicity is a harmless convenience that
lets `h(ℓ) ≤ h(n)` for `ℓ ≤ n`.

The paper additionally requires `h(m) = o(√m)`; that is `IsSqrtSmall` below, deliberately *not* a
field here, and in fact assumed by *no* result of this development. It would only ever be used by
the `√n`-scaled normality results, and there it is unnecessary
(`underExplored_eventually_empty`: under Condition **B** forced exploration switches itself off,
so any `h(m) = o(m)` does — see `aRTSFE_smallness_op` and `aRTSFE_smallness_upper`). Dropping it is
what makes schedules with `h(m) ≫ √m` available — and those are exactly the ones under which forced
exploration, rather than the data-dependent targeting rule, decides a *sparse* arm's sample size,
which is what earns the sparse componentwise CLT (`pullCount_div_sched_tendsto_one`,
`aRTSFE_sparse_clt`). -/
structure IsExplorationSchedule (hsched : ℕ → ℝ) : Prop where
  /-- The schedule is nondecreasing. -/
  mono : Monotone hsched
  /-- The schedule diverges: `h(m) → ∞` (this is what forces every arm to be sampled infinitely
  often). -/
  tendsto_atTop : Tendsto hsched atTop atTop
  /-- The schedule is `o(m)`. -/
  div_tendsto_zero : Tendsto (fun m ↦ hsched m / (m : ℝ)) atTop (𝓝 0)

/-- The paper's stronger schedule condition `h(m) = o(√m)` (condition (ii) of its Definition 5.1).
No result here assumes it: it is kept only to *record* the paper's condition and to state that the
sparse regime lies outside it (`not_isSqrtSmall_sched23`,
`sched23_satisfies_schedule_hypotheses`). See `IsExplorationSchedule`. -/
def IsSqrtSmall (hsched : ℕ → ℝ) : Prop :=
  Tendsto (fun m ↦ hsched m / √m) atTop (𝓝 0)

/-- `h(m) = o(√m)` implies `h(m)/m → 0`, so the paper's condition is stronger than the one
retained in `IsExplorationSchedule`. -/
@[specifies IsSqrtSmall "places the paper's condition strictly above the one this development \
keeps: `o(√m)` implies `o(m)`, so `IsSqrtSmall` is an extra demand and never a weakening"]
lemma IsSqrtSmall.div_tendsto_zero {hsched : ℕ → ℝ} (hlo : IsSqrtSmall hsched) :
    Tendsto (fun m ↦ hsched m / (m : ℝ)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun m : ℕ ↦ 1 / √m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hprod : Tendsto (fun m : ℕ ↦ (hsched m / √m) * (1 / √m))
      atTop (𝓝 0) := by simpa using hlo.mul h2
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  rw [div_mul_div_comm, mul_one, Real.mul_self_sqrt (Nat.cast_nonneg m)]

/-- **A positive allocation proportion eventually outgrows the schedule** — the single-arm core of
`underExplored_eventually_empty` (Proposition 1 of `maths/sparse-clt-fix.md`). If `N_{n,k}/n → v`
with `v > 0` and the schedule is `o(n)`, then arm `k` is eventually *not* under-explored, however
large `h` is below `n`. This is what makes the paper's `h(n) = o(√n)` unnecessary: under
Condition **B** forced exploration switches itself off, so the `aRTSFE` gap is eventually the
`aRTS` gap. -/
lemma eventually_sched_lt_pullCount [DecidableEq 𝓐] {hsched : ℕ → ℝ}
    (hdiv : Tendsto (fun n ↦ hsched n / (n : ℝ)) atTop (𝓝 0)) {v : ℝ} (hv : 0 < v)
    {k : 𝓐} {ω : Ω}
    (hprop : Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 v)) :
    ∀ᶠ n in atTop, hsched n < (pullCount A k n ω : ℝ) := by
  have h1 : ∀ᶠ n in atTop, hsched n / (n : ℝ) < v / 2 :=
    hdiv.eventually (eventually_lt_nhds (by linarith))
  have h2 : ∀ᶠ n in atTop, v / 2 < (pullCount A k n ω : ℝ) / (n : ℝ) :=
    hprop.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n hn1 hn2 hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  exact (div_lt_div_iff_of_pos_right hnR).mp (hn1.trans hn2)

/-- The **forced-exploration hitting predicate**: arm `k` is either *under-sampled*
(`N_{m,k} ≤ m ρ̂_{m,k}`) or *under-explored* (`N_{m,k} ≤ h(m)`). Its last occurrence before `n` is
the forced-exploration hitting time; the generic conditions hold with it. -/
def aRTSFEUnder [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hsched : ℕ → ℝ) (k : 𝓐) (ω : Ω) (m : ℕ) : Prop :=
  (pullCount A k m ω : ℝ) ≤ (m : ℝ) * aRTSTarget A Y θ₀ T m ω k
    ∨ (pullCount A k m ω : ℝ) ≤ hsched m

noncomputable instance [DecidableEq 𝓐] {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {hsched : ℕ → ℝ}
    {k : 𝓐} {ω : Ω} : DecidablePred (aRTSFEUnder A Y θ₀ T hsched k ω) := Classical.decPred _

/-- **The forced-exploration aRTS design family** (Definition 5.1 of the paper, algorithm form) —
the `IsARTS` analogue for `aRTSFE`. An algorithm is an `α`-throttled forced-exploration aRTS design
with offsets `θ₀`, target map `T` and schedule `h` when its policy obeys two rules:

* **forced exploration takes priority**: if some arm is under-explored (`N_{n,j} ≤ h(n)`), then
  all of the policy's mass sits on the *least-sampled* under-explored arms — every other arm gets
  probability zero;
* **outside forced exploration the design is throttled**: an arm that is neither under-sampled nor
  under-explored gets probability at most `α ρ̂_k`.

Compared with `IsARTS`, the throttle carries the extra premise `h(n) < N_{n,k}`: forced
exploration is allowed to override it, which is exactly what the design is for.

Like `IsARTS`, this is stated purely on histories — no process, measure or filtration appears — so
it is a property of the algorithm alone, checkable design by design. `throttle_of_isARTSFE` and
`fe_of_isARTSFE` transport the two fields to the process-level hypotheses that the asymptotic
theorems consume. -/
structure IsARTSFE [DecidableEq 𝓐] (alg : Algorithm Unit 𝓐 ℝ) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hsched : ℕ → ℝ) (α : ℝ) : Prop where
  /-- An arm that is neither under-sampled nor under-explored is throttled at `α ρ̂_k`. -/
  throttle : ∀ (n : ℕ) (hist : Hist Unit 𝓐 ℝ n) (k : 𝓐),
    (n : ℝ) * histTarget θ₀ T k n hist < (pullCount' n hist k : ℝ) →
      hsched n < (pullCount' n hist k : ℝ) →
        (alg.policy n (hist, ()) {k}).toReal ≤ α * histTarget θ₀ T k n hist
  /-- When some arm is under-explored, an arm that is not a least-sampled under-explored one cannot
  be drawn. -/
  forced : ∀ (n : ℕ) (hist : Hist Unit 𝓐 ℝ n) (k : 𝓐),
    (∃ j, (pullCount' n hist j : ℝ) ≤ hsched n) →
      (hsched n < (pullCount' n hist k : ℝ) ∨
        ∃ j, (pullCount' n hist j : ℝ) ≤ hsched n ∧
          (pullCount' n hist j : ℝ) < (pullCount' n hist k : ℝ)) →
        alg.policy n (hist, ()) {k} = 0

omit [IsProbabilityMeasure P] in
/-- The level sets of the forced-exploration predicate are measurable (a union of the two
measurable events `N ≤ m ρ̂` and `N ≤ h(m)`). -/
lemma measurableSet_aRTSFEUnder [DecidableEq 𝓐] [Finite 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (hsched : ℕ → ℝ) (k : 𝓐) (m : ℕ) :
    MeasurableSet {ω | aRTSFEUnder A Y θ₀ T hsched k ω m} := by
  simp only [aRTSFEUnder, Set.ofPred_or]
  refine (measurableSet_aRTSUnder h θ₀ hT k m).union ?_
  simp only [← count_indicator_eq_pullCount]
  exact measurableSet_le (measurable_count_actionIndicator h k m) measurable_const

/-- **The forced-exploration gap bound.** At the forced-exploration hitting time the gap
`N_ℓ - ℓ ρ̂_ℓ` is bounded by `(h(ℓ))^+ ≤ (h(n))^+`: if `ℓ = 0` the gap is `≤ 0`; otherwise the
hitting predicate holds at `ℓ`, so either arm `k` is under-sampled (gap `≤ 0`) or under-explored
(`N_ℓ ≤ h(ℓ)`, and `ℓ ρ̂_ℓ ≥ 0`), and monotonicity lifts `h(ℓ)` to `h(n)`. This single
deterministic bound feeds all three smallness conditions (`o(n)`, `o(√n)`, `O(√(n log log n))`). -/
lemma aRTSFE_gap_le [DecidableEq 𝓐] (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hTnn : ∀ z k, 0 ≤ T z k)
    {hsched : ℕ → ℝ} (hmono : Monotone hsched) (k : 𝓐) (ω : Ω) (n : ℕ) :
    (pullCount A k (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω : ℝ)
      - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
        * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k
      ≤ max 0 (hsched n) := by
  rcases Nat.eq_zero_or_pos (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) with h0 | hpos
  · rw [h0]
    simp only [pullCount_zero_apply, Nat.cast_zero, zero_mul, sub_zero]
    exact le_max_left _ _
  · have hP : aRTSFEUnder A Y θ₀ T hsched k ω (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) :=
      Nat.findGreatest_of_ne_zero rfl hpos.ne'
    have hmono2 : max 0 (hsched (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n))
        ≤ max 0 (hsched n) := max_le_max le_rfl (hmono (Nat.findGreatest_le n))
    refine le_trans ?_ hmono2
    rcases hP with hunder | hsmall
    · exact le_trans (by linarith) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hnn : (0 : ℝ) ≤ (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
          * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k :=
        mul_nonneg (Nat.cast_nonneg _) (by simp only [aRTSTarget]; exact hTnn _ _)
      linarith

omit [IsProbabilityMeasure P] in
/-- **Once forced exploration is off, the gap is bounded by a path constant.** Suppose arm `k` is
never under-explored after `n₀`, i.e. `h(m) < N_{m,k}` for every `m ≥ n₀` — which is what
Condition **B** buys through `eventually_sched_lt_pullCount`. Then at the forced-exploration hitting
time the under-explored disjunct of `aRTSFEUnder` can only fire before `n₀`, so the gap is bounded
*uniformly in `n`* by the finitely many gaps at times `< n₀`: either `ℓ_n = 0` and the gap is `0`,
or `ℓ_n ≥ n₀` and arm `k` is under-sampled there, giving a gap `≤ 0`, or `ℓ_n < n₀` and the gap is
one of the (nonnegative parts of the) summands.

This is what replaces the paper's `h(n) = o(√n)` in the `√n`-scaled smallness conditions
(`aRTSFE_smallness_op`, `aRTSFE_smallness_upper`): a bound by a *constant* is `o(√n)` and
`O(√(n log log n))` for free, whatever the schedule does below `n`. -/
lemma aRTSFE_gap_le_sum_of_not_underExplored [DecidableEq 𝓐] (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    {hsched : ℕ → ℝ} (k : 𝓐) (ω : Ω) {n₀ : ℕ}
    (hoff : ∀ m, n₀ ≤ m → hsched m < (pullCount A k m ω : ℝ)) (n : ℕ) :
    (pullCount A k (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω : ℝ)
      - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
        * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k
      ≤ ∑ m ∈ Finset.range n₀, max 0 ((pullCount A k m ω : ℝ)
          - (m : ℝ) * aRTSTarget A Y θ₀ T m ω k) := by
  have hC0 : (0 : ℝ) ≤ ∑ m ∈ Finset.range n₀, max 0 ((pullCount A k m ω : ℝ)
      - (m : ℝ) * aRTSTarget A Y θ₀ T m ω k) :=
    Finset.sum_nonneg fun m _ ↦ le_max_left _ _
  rcases Nat.eq_zero_or_pos (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) with h0 | hpos
  · rw [h0]
    simpa only [pullCount_zero_apply, Nat.cast_zero, zero_mul, sub_zero] using hC0
  · have hP : aRTSFEUnder A Y θ₀ T hsched k ω (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) :=
      Nat.findGreatest_of_ne_zero rfl hpos.ne'
    rcases lt_or_ge (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) n₀ with hlt | hge
    · -- The under-explored disjunct fired before `n₀`: the gap is one of the finitely many terms.
      exact le_trans (le_max_right 0 _)
        (Finset.single_le_sum (f := fun m ↦ max 0 ((pullCount A k m ω : ℝ)
            - (m : ℝ) * aRTSTarget A Y θ₀ T m ω k))
          (fun m _ ↦ le_max_left _ _) (Finset.mem_range.mpr hlt))
    · -- After `n₀` the under-explored disjunct is impossible, so arm `k` is under-sampled.
      rcases hP with hunder | hsmall
      · linarith
      · exact absurd hsmall (not_le.mpr (hoff _ hge))

/-- **Forced-exploration consistency smallness** (the `aRTSFE` form of `generic_small_of_hitting`).
At the forced-exploration hitting time the gap is `≤ (h(n))^+` (`aRTSFE_gap_le`), which is `o(n)`
because the schedule is, so it vanishes divided by `n`. -/
lemma aRTSFE_smallness [DecidableEq 𝓐] (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hTnn : ∀ z k, 0 ≤ T z k)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (k : 𝓐) (ω : Ω) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      ((pullCount A k (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω : ℝ)
        - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
          * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k)
        / (n : ℝ) < δ := by
  -- `max 0 (h n) / n → 0`, by squeezing between `0` and `|h n / n|`.
  have hmaxlim : Tendsto (fun n : ℕ ↦ max 0 (hsched n) / (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_)
      (by simpa using hh.div_tendsto_zero.abs)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [abs_div, Nat.abs_cast]
      gcongr
      exact max_le (abs_nonneg _) (le_abs_self _)
  filter_upwards [hmaxlim.eventually (gt_mem_nhds hδ), eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hnR]
  linarith [aRTSFE_gap_le (A := A) (Y := Y) θ₀ T hTnn hh.mono k ω n, (div_lt_iff₀ hnR).mp hn]

omit [IsProbabilityMeasure P] in
/-- The `aRTSFE` consistency smallness for *all* arms, in the form consumed by the abstract-hitting
consistency/rate theorems (`consistency_of_hitting`, `theta_consistent_of_hitting`,
`proportion_tendsto_of_hitting`, `rho_rate_of_hitting`): `aRTSFE_smallness` bundled over `k`. -/
lemma aRTSFE_smallness_all [DecidableEq 𝓐] (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) :
    ∀ k, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ((pullCount A k (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω : ℝ)
          - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
            * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k)
          / (n : ℝ) < δ :=
  fun k ↦ Eventually.of_forall fun ω δ hδ ↦ aRTSFE_smallness θ₀ T hTnn hh k ω δ hδ

/-- **Forced-exploration `o_p`-smallness** (the `aRTSFE` form of the `hsmall_op` hypothesis of
`prop_dev_of_hitting`). Under Condition **B** — supplied here by the *positive* proportion limit
`N_{n,k}/n → v > 0` — forced exploration eventually stops firing
(`eventually_sched_lt_pullCount`), so the gap `N_ℓ - ℓ ρ̂_ℓ` is a.s. bounded by a path constant
(`aRTSFE_gap_le_sum_of_not_underExplored`) and `(1 + N_ℓ - ℓ ρ̂_ℓ)^+ / √n → 0` a.s., hence `o_p(1)`.

Nothing beyond `h(n) = o(n)` is asked of the schedule. Together with `aRTSFE_smallness_upper` this
is where the paper's condition (ii), `h(n) = o(√n)`, would be used; Proposition 1 of
`maths/sparse-clt-fix.md` replaces it, which is what lets `IsExplorationSchedule` keep only `o(n)`
and makes the sparse regime (`h(n) ≫ √n`) reachable. -/
lemma aRTSFE_smallness_op [DecidableEq 𝓐] [Finite 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (k : 𝓐) {v : ℝ} (hv : 0 < v)
    (hNconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ))
      atTop (𝓝 v)) :
    IsLittleOpOne P (fun n ω ↦
      max ((1 + ((pullCount A k (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω : ℝ)
        - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
          * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k)) / √n) 0) := by
  refine isLittleOpOne_of_tendsto_ae (fun n ↦ ?_) ?_
  · exact (((measurable_const.add (measurable_gap_hitting h θ₀ hT
      (measurableSet_aRTSFEUnder h θ₀ hT hsched k) k n)).div_const (√n)).max
        measurable_const).aestronglyMeasurable
  filter_upwards [hNconv] with ω hω
  -- Condition **B**: after some `n₀` arm `k` is never under-explored again.
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (eventually_sched_lt_pullCount hh.div_tendsto_zero hv hω)
  -- so the gap is bounded, uniformly in `n`, by a path constant `C`.
  set C : ℝ := ∑ m ∈ Finset.range n₀, max 0 ((pullCount A k m ω : ℝ)
    - (m : ℝ) * aRTSTarget A Y θ₀ T m ω k) with hCdef
  have hC0 : (0 : ℝ) ≤ C := Finset.sum_nonneg fun m _ ↦ le_max_left _ _
  have hlim : Tendsto (fun n : ℕ ↦ max ((1 + C) / √n) 0) atTop (𝓝 0) := by
    have hd : Tendsto (fun n : ℕ ↦ (1 + C) / √n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using hd.max (tendsto_const_nhds (x := (0 : ℝ)))
  refine squeeze_zero' (Eventually.of_forall fun n ↦ le_max_right _ _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hgap := aRTSFE_gap_le_sum_of_not_underExplored (A := A) (Y := Y) θ₀ T k ω hn₀ n
  rw [← hCdef] at hgap
  exact max_le_max (by gcongr) le_rfl

/-- Eventually `1 ≤ √(n log log n)` — the crude bound that turns a constant into an
`O(√(n log log n))`. -/
lemma one_le_sqrt_mul_log_log : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ √(n * Real.log (Real.log n)) := by
  have hll := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop (1 : ℝ)
  filter_upwards [hll, eventually_ge_atTop 1] with n hlln hn1
  simp only [Function.comp_apply] at hlln
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have h1 : (1 : ℝ) ≤ (n : ℝ) * Real.log (Real.log n) := by nlinarith
  simpa using Real.sqrt_le_sqrt h1

omit [IsProbabilityMeasure P] in
/-- **Forced-exploration loglog-smallness** (the `aRTSFE` form of the `hsmall_upper` hypothesis of
`dev_upper_of_hitting`). Under Condition **B** the gap is a.s. bounded by a path constant
(`aRTSFE_gap_le_sum_of_not_underExplored`, through `eventually_sched_lt_pullCount`), and a constant
is `O(√(n log log n))` because `√(n log log n) ≥ 1` eventually. As for `aRTSFE_smallness_op`,
nothing beyond `h(n) = o(n)` is asked of the schedule. -/
lemma aRTSFE_smallness_upper [DecidableEq 𝓐] (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched) (k : 𝓐) {v : ℝ} (hv : 0 < v)
    (hNconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ))
      atTop (𝓝 v)) :
    ∀ᵐ ω ∂P, ∃ C, ∀ᶠ n in atTop,
      ((pullCount A k (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω : ℝ)
        - (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n : ℝ)
          * aRTSTarget A Y θ₀ T (hitting (aRTSFEUnder A Y θ₀ T hsched k ω) n) ω k)
        ≤ C * √(n * Real.log (Real.log n)) := by
  filter_upwards [hNconv] with ω hω
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (eventually_sched_lt_pullCount hh.div_tendsto_zero hv hω)
  set C : ℝ := ∑ m ∈ Finset.range n₀, max 0 ((pullCount A k m ω : ℝ)
    - (m : ℝ) * aRTSTarget A Y θ₀ T m ω k) with hCdef
  have hC0 : (0 : ℝ) ≤ C := Finset.sum_nonneg fun m _ ↦ le_max_left _ _
  refine ⟨C, ?_⟩
  filter_upwards [one_le_sqrt_mul_log_log] with n hn
  have hgap := aRTSFE_gap_le_sum_of_not_underExplored (A := A) (Y := Y) θ₀ T k ω hn₀ n
  rw [← hCdef] at hgap
  nlinarith


/-! ### No starvation under forced exploration (sparse targets)

Forced exploration guarantees every arm is sampled infinitely often, with no assumption on the
target — the key ingredient that extends the theory to sparse targets (`v_k = 0`). -/

/-- **Forced exploration prevents starvation, pathwise** (the deterministic core). Fix a path `ω`.
If the schedule diverges (`hsched → ∞`) and the path obeys the action-level forced-exploration rule
`hfe` — whenever some arm is under-explored (`N_{m,j} ≤ h(m)` for some `j`), the chosen arm `A_m`
is a *least-sampled under-explored* arm — then every arm's pull count diverges: `N_{n,k} → ∞`.

The proof is the potential-function argument: were arm `k` to stall (`N_{n,k} ≤ B` for all `n`),
then for `n` large enough that `h(n) ≥ B` the arm `k` is under-explored, so `A_n` is least-sampled
among the under-explored arms and has count `≤ N_{n,k} ≤ B`; the potential
`D(n) = ∑_j (B + 1 - N_{n,j})^+` then drops by exactly `1` at every such step, forcing it negative —
impossible for a sum of naturals. -/
lemma no_starvation_pathwise [Finite 𝓐] [DecidableEq 𝓐] (ω : Ω) {hsched : ℕ → ℝ}
    (hh : Tendsto hsched atTop atTop)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω) (k : 𝓐) :
    Tendsto (fun n ↦ pullCount A k n ω) atTop atTop := by
  let : Fintype 𝓐 := Fintype.ofFinite 𝓐
  refine tendsto_atTop_atTop_of_monotone (monotone_pullCount k ω) fun B ↦ ?_
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  -- `hcon : ∀ n, pullCount A k n ω < B` (arm `k` stalls below `B`).
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hh.eventually_ge_atTop (B : ℝ))
  set D : ℕ → ℕ := fun n ↦ ∑ j, (B + 1 - pullCount A j n ω) with hDdef
  -- The potential drops by exactly `1` at every step `n ≥ N₁`.
  have hdec : ∀ n, N₁ ≤ n → D (n + 1) + 1 = D n := by
    intro n hn
    have hkn : (pullCount A k n ω : ℝ) ≤ hsched n :=
      le_trans (by exact_mod_cast (hcon n).le) (hN₁ n hn)
    obtain ⟨-, hc2⟩ := hfe n ⟨k, hkn⟩
    have hcB : pullCount A (A n ω) n ω ≤ B := le_trans (hc2 k hkn) (hcon n).le
    have hsum_eq : ∑ j ∈ Finset.univ.erase (A n ω), (B + 1 - pullCount A j (n + 1) ω)
        = ∑ j ∈ Finset.univ.erase (A n ω), (B + 1 - pullCount A j n ω) :=
      Finset.sum_congr rfl fun j hj ↦ by
        rw [pullCount_eq_pullCount_of_action_ne (Finset.ne_of_mem_erase hj).symm]
    simp only [hDdef]
    rw [← Finset.add_sum_erase Finset.univ (fun j ↦ B + 1 - pullCount A j (n + 1) ω)
        (Finset.mem_univ (A n ω)),
      ← Finset.add_sum_erase Finset.univ (fun j ↦ B + 1 - pullCount A j n ω)
        (Finset.mem_univ (A n ω)),
      hsum_eq, pullCount_action_eq_pullCount_add_one]
    omega
  -- Hence `D(N₁ + t) + t = D(N₁)` for all `t`, so `t ≤ D(N₁)` — a contradiction at `t = D(N₁) + 1`.
  have hkey : ∀ t, D (N₁ + t) + t = D N₁ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hd := hdec (N₁ + t) (Nat.le_add_right N₁ t)
      change D (N₁ + t + 1) + (t + 1) = D N₁
      omega
  have hbad := hkey (D N₁ + 1)
  omega

omit [IsProbabilityMeasure P] in
/-- **Forced exploration prevents starvation** (the no-starvation half of the paper's
Theorem 5.2). For any forced-exploration design — given here through the a.s. action-level rule
`hfe`: whenever some arm is under-explored, the next action `A_m` is a least-sampled arm among the
under-explored ones — with a diverging schedule (`hsched → ∞`), every arm is sampled infinitely
often, `N_{n,k} → ∞` a.s., with *no assumption on the target*. This is the key ingredient enabling
sparse targets (`v_k = 0`); it is the a.s. wrapper of `no_starvation_pathwise`. -/
lemma aRTSFE_no_starvation [Finite 𝓐] [DecidableEq 𝓐] {hsched : ℕ → ℝ}
    (hh : Tendsto hsched atTop atTop)
    (hfe : ∀ᵐ ω ∂P, ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω) (k : 𝓐) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ pullCount A k n ω) atTop atTop := by
  filter_upwards [hfe] with ω hfeω
  exact no_starvation_pathwise ω hh hfeω k

omit [IsProbabilityMeasure P] in
omit [IsProbabilityMeasure P] in
/-- **Forced exploration switches itself off under Condition B** (pathwise). If every arm has a
*positive* limiting proportion `N_{n,k}/n → v_k > 0` and the schedule is `o(n)`, then eventually no
arm is under-explored: `U_n = ∅`.

This shows the paper's schedule condition `h(n) = o(√n)` is **not necessary** for the non-sparse
theory. Under Condition **B** the design eventually coincides with a plain `aRTS` design,
so the deviation gap is eventually `0` and every smallness condition holds trivially — for *any*
schedule with `h(n) = o(n)`, no matter how large. The consistency input `N_{n,k}/n → v_k` itself
needs only `h(n) = o(n)` (`IsExplorationSchedule.div_tendsto_zero`), so there is no circularity.

In particular D-Tracking's own `h(n) = (√n - K/2)^+`, which the paper's condition (ii) has to
exclude, becomes admissible. And schedules with `h(n) ≫ √n` — which are what make forced
exploration, rather than the data-dependent targeting rule, decide a *sparse* arm's sample size
(see `pullCount_div_sched_tendsto_one`) — become available. -/
lemma underExplored_eventually_empty [Finite 𝓐] [DecidableEq 𝓐] {hsched : ℕ → ℝ}
    (hdiv : Tendsto (fun n ↦ hsched n / (n : ℝ)) atTop (𝓝 0))
    {v : 𝓐 → ℝ} (hv : ∀ k, 0 < v k) {ω : Ω}
    (hprop : ∀ k, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v k))) :
    ∀ᶠ n in atTop, ∀ k, hsched n < (pullCount A k n ω : ℝ) := by
  refine eventually_all.mpr fun k ↦ ?_
  simpa only [count_indicator_eq_pullCount] using
    eventually_sched_lt_pullCount (A := A) (k := k) (ω := ω) hdiv (hv k)
      (by simpa only [count_indicator_eq_pullCount] using hprop k)

/-! ### Regularity of the pull counts under forced exploration

The self-normalized componentwise CLT (`AlphaRAR.estimatorError_joint_tendsto_multivariateGaussian`)
needs more than `N_{n,k} → ∞`: it needs the **regularity** `N_{n,k}/c_{k,n} → 1` for a deterministic
`c_{k,n} → ∞`. The lemmas below show that forced exploration supplies it — with the
*deterministic* schedule `h` itself as `c` — for arms whose pulls eventually all come from the
forced-exploration mechanism.

The restriction is genuine. Under the paper's `h(n) = o(√n)` a target-chasing design gives a sparse
arm `N_{n,k} ≈ n·T(θ̂_n)_k ≍ √n` (as `T ≥ 0` and `T(θ)_k = 0` force `∇T_k(θ) = 0`, so
`T(θ̂_n)_k = O(‖θ̂_n-θ‖²) = O(1/N_{n,k})`), so forced exploration does **not** set the scale for
such designs. It does for designs that stop feeding an arm they have identified as sparse. -/

omit [IsProbabilityMeasure P] in
/-- **A forced-exploration pull leaves the count at most one above the schedule** (pathwise upper
bound), up to the pulls that forced exploration did *not* cause.

`E` is any nondecreasing counter of the "non-FE" pulls of arm `k`: it must increase by at least one
whenever arm `k` is pulled at a round where no arm is under-explored (`hEstep`). Then
`N_{n,k} ≤ max (N_{n₀,k}) (h(n) + 1) + (E n - E n₀)`.

Indeed at an FE round the selected arm is itself under-explored (`N_{m,k} ≤ h(m)`), so one pull
leaves it at `h(m) + 1 ≤ h(n) + 1`; a non-FE pull adds one but is paid for by `E`; and at all other
rounds the count does not move.

Taking `E ≡ 0` recovers the case where arm `k` is fed *only* by forced exploration — which is what
the `α = 0` throttle produces (D-Tracking). For `α > 0` the throttle only makes non-FE pulls
*sporadic*, and one takes `E` to be their count. -/
lemma pullCount_le_sched_of_fe_except [DecidableEq 𝓐] (ω : Ω) {hsched : ℕ → ℝ}
    (hmono : Monotone hsched)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    {k : 𝓐} {n₀ : ℕ} (E : ℕ → ℝ) (hEmono : Monotone E)
    (hEstep : ∀ m, n₀ ≤ m → A m ω = k → (¬ ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      E m + 1 ≤ E (m + 1))
    {n : ℕ} (hn : n₀ ≤ n) :
    (pullCount A k n ω : ℝ) ≤ max (pullCount A k n₀ ω : ℝ) (hsched n + 1) + (E n - E n₀) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hmn : hsched n ≤ hsched (n + 1) := hmono (Nat.le_succ n)
    have hEmn : E n ≤ E (n + 1) := hEmono (Nat.le_succ n)
    have hmax : max (pullCount A k n₀ ω : ℝ) (hsched n + 1)
        ≤ max (pullCount A k n₀ ω : ℝ) (hsched (n + 1) + 1) :=
      max_le_max le_rfl (by linarith)
    by_cases hA : A n ω = k
    · have hstep : pullCount A k (n + 1) ω = pullCount A k n ω + 1 := by
        rw [← hA]; exact pullCount_action_eq_pullCount_add_one n ω
      rw [hstep]
      push_cast
      by_cases hFE : ∃ j, (pullCount A j n ω : ℝ) ≤ hsched n
      · -- FE round: the selected arm was under-explored, so the pull leaves it at `h(n) + 1`
        obtain ⟨hle, -⟩ := hfe n hFE
        rw [hA] at hle
        have hE0 : E n₀ ≤ E (n + 1) := hEmono (by omega)
        have hb : (pullCount A k n ω : ℝ) + 1
            ≤ max (pullCount A k n₀ ω : ℝ) (hsched (n + 1) + 1) :=
          le_max_of_le_right (by linarith)
        linarith
      · -- non-FE round: the extra pull is paid for by `E`
        have hEs := hEstep n hn hA hFE
        linarith
    · rw [pullCount_eq_pullCount_of_action_ne hA]
      linarith

omit [IsProbabilityMeasure P] in
/-- **Forced exploration pins every count to the schedule** (pathwise lower bound). If
`Fintype.card 𝓐 * L < n - s`, then every arm has `N_{n,j} ≥ min L (h s)`.

The mechanism: at a forced-exploration round the selected arm is a *least-sampled* under-explored
arm, hence sits at the global minimum. So the potential `D(m) = ∑_j (L - N_{m,j})⁺` drops by exactly
one per round, as long as the minimum stays below `L` and forced exploration keeps firing. Since
`D ≤ card 𝓐 * L`, that can persist for at most `card 𝓐 * L` rounds — so within any longer window,
either the minimum has reached `L`, or forced exploration failed to fire, which itself means every
count already exceeds `h`. This is the same potential-function device as
`no_starvation_pathwise`. -/
lemma pullCount_ge_min_sched_of_fe [Fintype 𝓐] [DecidableEq 𝓐] (ω : Ω) {hsched : ℕ → ℝ}
    (hmono : Monotone hsched)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    {s n L : ℕ} (hlen : Fintype.card 𝓐 * L < n - s) (j : 𝓐) :
    min (L : ℝ) (hsched s) ≤ (pullCount A j n ω : ℝ) := by
  by_contra hcon
  simp only [not_le, lt_min_iff] at hcon
  obtain ⟨hjL, hjs⟩ := hcon
  have hsn : s ≤ n := by omega
  have hjLn : pullCount A j n ω < L := by exact_mod_cast hjL
  -- On `[s, n)` arm `j` witnesses both "the minimum is `< L`" and "some arm is under-explored".
  have hjm : ∀ m, s ≤ m → m ≤ n →
      pullCount A j m ω < L ∧ (pullCount A j m ω : ℝ) ≤ hsched m := by
    intro m hsm hm
    have hle : pullCount A j m ω ≤ pullCount A j n ω := monotone_pullCount j ω hm
    refine ⟨lt_of_le_of_lt hle hjLn, ?_⟩
    have hcast : (pullCount A j m ω : ℝ) ≤ (pullCount A j n ω : ℝ) := by exact_mod_cast hle
    linarith [hjs, hmono hsm]
  -- The selected arm sits at the minimum, so the potential drops by exactly one each round.
  set D : ℕ → ℕ := fun m ↦ ∑ i, (L - pullCount A i m ω) with hDdef
  have hdec : ∀ m, s ≤ m → m < n → D (m + 1) + 1 = D m := by
    intro m hsm hmn
    obtain ⟨hjmL, hjmh⟩ := hjm m hsm hmn.le
    obtain ⟨-, hmin⟩ := hfe m ⟨j, hjmh⟩
    have hAL : pullCount A (A m ω) m ω < L := lt_of_le_of_lt (hmin j hjmh) hjmL
    have hsum_eq : ∑ i ∈ Finset.univ.erase (A m ω), (L - pullCount A i (m + 1) ω)
        = ∑ i ∈ Finset.univ.erase (A m ω), (L - pullCount A i m ω) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [pullCount_eq_pullCount_of_action_ne (Finset.ne_of_mem_erase hi).symm]
    simp only [hDdef]
    rw [← Finset.add_sum_erase Finset.univ (fun i ↦ L - pullCount A i (m + 1) ω)
        (Finset.mem_univ (A m ω)),
      ← Finset.add_sum_erase Finset.univ (fun i ↦ L - pullCount A i m ω)
        (Finset.mem_univ (A m ω)),
      hsum_eq, pullCount_action_eq_pullCount_add_one]
    omega
  -- Telescoping: the window length is bounded by the initial potential `≤ card 𝓐 * L`.
  have hkey : ∀ t, s + t ≤ n → D (s + t) + t = D s := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have hd := hdec (s + t) (Nat.le_add_right s t) (by omega)
      have := ih (by omega)
      change D (s + t + 1) + (t + 1) = D s
      omega
  have hDs : D s ≤ Fintype.card 𝓐 * L := by
    simp only [hDdef]
    calc ∑ i, (L - pullCount A i s ω) ≤ ∑ _i : 𝓐, L :=
          Finset.sum_le_sum fun i _ ↦ Nat.sub_le _ _
      _ = Fintype.card 𝓐 * L := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hfin := hkey (n - s) (by omega)
  omega

omit [IsProbabilityMeasure P] in
/-- **The deterministic floor that forced exploration puts under every count.** Eventually
`N_{n,k} ≥ h(n - W(n))`, where `W(n) = K⌈h(n)⌉ + 1` is the catch-up window: within any window longer
than `W(n)` the least-sampled arm has been brought up to `⌈h(n)⌉`, or forced exploration stopped
firing — which itself means every count already exceeds `h`.

The bound is **unconditional** on the design (only forced exploration's own rule `hfe` is used), and
its right-hand side is a *deterministic* function of `n`. That is what makes it usable as the `L` of
`exists_decay_of_contDiffAt`, where the loglog rate must be measured against something that does not
depend on ω. The `hshift` hypothesis of `pullCount_div_sched_tendsto_one` says exactly that this
floor is `h(n)` to first order.

The window fits inside `[0, n]` eventually because `h(n) = o(n)`. -/
lemma eventually_schedShift_le_pullCount [Fintype 𝓐] [DecidableEq 𝓐] (ω : Ω)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    (k : 𝓐) :
    ∀ᶠ n in atTop,
      hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) ≤ (pullCount A k n ω : ℝ) := by
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < hsched n := hh.tendsto_atTop.eventually_gt_atTop 0
  have hwin : ∀ᶠ n in atTop, Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1 ≤ n := by
    have hz : Tendsto (fun n ↦ ((Fintype.card 𝓐 : ℝ) + 1) * ((hsched n + 1) / n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ (hsched n + 1) / (n : ℝ)) atTop (𝓝 0) := by
        have := hh.div_tendsto_zero.add (tendsto_one_div_atTop_nhds_zero_nat)
        simpa [add_div] using this
      simpa using h1.const_mul ((Fintype.card 𝓐 : ℝ) + 1)
    filter_upwards [hz.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)),
      eventually_gt_atTop 0, hpos] with n hn hn0 hsn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hceil : (⌈hsched n⌉₊ : ℝ) ≤ hsched n + 1 := (Nat.ceil_lt_add_one hsn.le).le
    have hcnn : (0 : ℝ) ≤ (Fintype.card 𝓐 : ℝ) := Nat.cast_nonneg _
    have hcen : (0 : ℝ) ≤ (⌈hsched n⌉₊ : ℝ) := Nat.cast_nonneg _
    have hle : ((Fintype.card 𝓐 : ℝ) * ⌈hsched n⌉₊ + 1)
        ≤ ((Fintype.card 𝓐 : ℝ) + 1) * (hsched n + 1) := by nlinarith
    have hlt : ((Fintype.card 𝓐 : ℝ) + 1) * (hsched n + 1) < n := by
      rw [← div_lt_one hnR, mul_div_assoc]
      exact hn
    exact_mod_cast le_of_lt (lt_of_le_of_lt hle hlt)
  filter_upwards [hwin] with n hn
  set L := ⌈hsched n⌉₊ with hL
  set s := n - (Fintype.card 𝓐 * L + 1) with hs
  have hlen : Fintype.card 𝓐 * L < n - s := by omega
  have hb := pullCount_ge_min_sched_of_fe ω hh.mono hfe hlen k
  have hsn' : s ≤ n := by omega
  have hmin : hsched s ≤ min (L : ℝ) (hsched s) :=
    le_min (le_trans (hh.mono hsn') (Nat.le_ceil (hsched n))) le_rfl
  exact hmin.trans hb

/-- **Forced exploration makes an FE-fed arm's pull count regular** (pathwise): `N_{n,k}/h(n) → 1`.

This is exactly the regularity hypothesis that the componentwise CLT
(`AlphaRAR.estimatorError_joint_tendsto_multivariateGaussian`) requires, with the *deterministic*
schedule `h` as the normalizer `c_{k,n}` — so for such arms forced exploration earns the CLT.

`hshift` is a mild regularity of the schedule itself: shifting the argument by the
`O(h n)` catch-up window does not change `h` to first order. It holds for the paper's
`h(n) = (n^{1/3} - K/2)^+` and for any regularly varying schedule.

`E` counts the pulls of arm `k` that forced exploration did *not* cause, and is required only to be
`o(h)`: for the `α = 0` throttle there are none (take `E ≡ 0`), and for `α > 0` the throttle makes
them sporadic enough. -/
lemma pullCount_div_sched_tendsto_one [Fintype 𝓐] [DecidableEq 𝓐] (ω : Ω) {hsched : ℕ → ℝ}
    (hh : IsExplorationSchedule hsched)
    (hfe : ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    (hshift : Tendsto
      (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n) atTop (𝓝 1))
    {k : 𝓐} {n₀ : ℕ} (E : ℕ → ℝ) (hEmono : Monotone E)
    (hEstep : ∀ m, n₀ ≤ m → A m ω = k → (¬ ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      E m + 1 ≤ E (m + 1))
    (hEsmall : Tendsto (fun n ↦ E n / hsched n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / hsched n) atTop (𝓝 1) := by
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < hsched n := hh.tendsto_atTop.eventually_gt_atTop 0
  -- Upper: once the schedule has passed the initial count, `N_{n,k} ≤ h n + 1 + (E n - E n₀)`.
  have hupper : ∀ᶠ n in atTop, (pullCount A k n ω : ℝ) / hsched n
      ≤ (hsched n + 1) / hsched n + (E n - E n₀) / hsched n := by
    filter_upwards [eventually_ge_atTop n₀, hpos,
      hh.tendsto_atTop.eventually_ge_atTop ((pullCount A k n₀ ω : ℝ))] with n hn hn0 hge
    have hb := pullCount_le_sched_of_fe_except ω hh.mono hfe E hEmono hEstep hn
    rw [← add_div]
    gcongr
    exact hb.trans (by rw [max_eq_right (by linarith)])
  -- Lower: forced exploration's deterministic floor.
  have hlower : ∀ᶠ n in atTop,
      hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n
        ≤ (pullCount A k n ω : ℝ) / hsched n := by
    filter_upwards [eventually_schedShift_le_pullCount ω hh hfe k, hpos] with n hb hsn
    gcongr
  -- Squeeze: both bounds tend to `1`.
  have hone : Tendsto (fun n ↦ (hsched n + 1) / hsched n) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n ↦ (hsched n)⁻¹) atTop (𝓝 0) := hh.tendsto_atTop.inv_tendsto_atTop
    have hsum : Tendsto (fun n ↦ 1 + (hsched n)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hpos] with n hn
    field_simp
  -- The non-FE pulls are `o(h)`, so the upper majorant still tends to `1`.
  have htop : Tendsto (fun n ↦ (hsched n + 1) / hsched n + (E n - E n₀) / hsched n)
      atTop (𝓝 1) := by
    have hconst : Tendsto (fun n : ℕ ↦ E n₀ / hsched n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hh.tendsto_atTop
    have hdiff : Tendsto (fun n ↦ (E n - E n₀) / hsched n) atTop (𝓝 0) := by
      have hs := hEsmall.sub hconst
      rw [sub_zero] at hs
      exact hs.congr fun n ↦ (sub_div _ _ _).symm
    have := hone.add hdiff
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hshift htop hlower hupper

omit [IsProbabilityMeasure P] in
/-- **The throttle fires at every round where arm `k` is not under-explored** (the "Step 3" of
`maths/sparse-clt-fix.md`, pathwise).

If arm `k` is not under-explored at round `m` (`h(m) < N_{m,k}`) and its plug-in target has decayed
below `h(m)/m` (hypotheses `hdecay`, `hgh`), then `¬ aRTSFEUnder`, i.e. arm `k` is *over-sampled*
relative to its target and not under-explored — exactly the antecedent of the `aRTS` throttling
condition, which then caps its selection probability at `α ρ̂_{m,k}`.

The comparison `g(m) < h(m)/m` is where the schedule condition enters, and it is what makes the
*reversed* condition `h(n) ≫ √n` the right one: a sparse arm has `T(Θ)_k = 0` with `T ≥ 0`, so `Θ`
minimises `T_k`, giving `ρ̂_{m,k} = O(‖Θ̂_m-Θ‖²) = O(log log h(m)/h(m))` by the subsampled LIL
(`abs_estimator_sub_le_rate_loglog_N`) once `N_{m,k} ≳ h(m)`; then `g(m) < h(m)/m` reads
`h(m)² ≫ m log log m`. Under the paper's `h(n) = o(√n)` it is false, and the arm keeps being fed by
the targeting rule. -/
lemma not_aRTSFEUnder_of_sched_lt [DecidableEq 𝓐] (ω : Ω) {hsched g : ℕ → ℝ} {θ₀ : 𝓐 → ℝ}
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐} {m : ℕ} (hm : 0 < m)
    (hnot : hsched m < (pullCount A k m ω : ℝ))
    (hdecay : aRTSTarget A Y θ₀ T m ω k ≤ g m)
    (hgh : g m < hsched m / (m : ℝ)) :
    ¬ aRTSFEUnder A Y θ₀ T hsched k ω m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [aRTSFEUnder]
  simp only [not_or, not_le]
  refine ⟨?_, hnot⟩
  calc (m : ℝ) * aRTSTarget A Y θ₀ T m ω k ≤ (m : ℝ) * g m := by gcongr
    _ < (m : ℝ) * (hsched m / (m : ℝ)) := by gcongr
    _ = hsched m := by field_simp
    _ < _ := hnot

omit [IsProbabilityMeasure P] in
/-- The count `N_{m,k}` is a **previous-history** statistic: it reads only `A_0,…,A_{m-1}`. Stated
in `count` form: it is the plumbing behind the `shiftDown`-measurability of the design predicates,
whose proofs work with the indicator sums. -/
lemma measurable_shiftDown_count
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (k : 𝓐) (m : ℕ) :
    Measurable[h.filtration.shiftDown m]
      (fun ω ↦ count (fun j ↦ actionIndicator A k j ω) m) := by
  cases m with
  | zero =>
    simp only [count, Finset.range_zero, Finset.sum_empty]
    exact measurable_const
  | succ p =>
    simp only [count]
    refine Finset.measurable_sum _ fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    exact (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
      (h.adapted_action.measurable_le
        (by omega : j ≤ p)))

omit [IsProbabilityMeasure P] in
/-- The forced-exploration predicate at round `m` is a **previous-history** event: both the count
`N_{m,k}` and the plug-in target `ρ̂_{m,k}` are built from `A_0,…,A_{m-1}` and `Y_0,…,Y_{m-1}`.

This is what lets the throttle be applied *inside* a conditional expectation given `ℱ_{m-1}`, and it
is what makes the `α = 0` argument below work with no decay hypothesis at all. -/
lemma measurableSet_shiftDown_aRTSFEUnder [DecidableEq 𝓐] [Finite 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ}
    (hT : Continuous T) (hsched : ℕ → ℝ) (k : 𝓐) (m : ℕ) :
    MeasurableSet[h.filtration.shiftDown m]
      {ω | aRTSFEUnder A Y θ₀ T hsched k ω m} := by
  cases m with
  | zero =>
    have huniv : {ω | aRTSFEUnder A Y θ₀ T hsched k ω 0} = Set.univ := by
      ext ω; simp [aRTSFEUnder]
    rw [huniv]; exact MeasurableSet.univ
  | succ p =>
    set 𝔾 := h.filtration with h𝔾
    have harm : ∀ (k' : 𝓐) (j : ℕ), j ≤ p → Measurable[𝔾 p] (actionIndicator A k' j) := by
      intro k' j hj
      exact (measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k').preimage
        (h.adapted_action.measurable_le hj))
    have hcount : ∀ k' : 𝓐,
        Measurable[𝔾 p] (fun ω ↦ count (fun j ↦ actionIndicator A k' j ω) (p + 1)) :=
      fun k' ↦ measurable_shiftDown_count h k' (p + 1)
    have hnum : ∀ k' : 𝓐, Measurable[𝔾 p]
        (fun ω ↦ ∑ j ∈ Finset.range (p + 1), actionIndicator A k' j ω * Y j ω) := by
      intro k'
      refine Finset.measurable_sum _ fun j hj ↦ ?_
      rw [Finset.mem_range] at hj
      exact (harm k' j (by omega : j ≤ p)).mul
        (h.adapted_feedback.measurable_le
          (by omega : j ≤ p))
    have hest : @Measurable Ω (𝓐 → ℝ) (𝔾 p) inferInstance
        (fun ω k' ↦ estimator (fun j ↦ actionIndicator A k' j ω) (Y · ω) (θ₀ k') (p + 1)) := by
      refine @Measurable.of_eval Ω 𝓐 (fun _ ↦ ℝ) (𝔾 p) (fun _ ↦ inferInstance) _ fun k' ↦ ?_
      simp only [estimator]
      exact ((hnum k').add_const _).div ((hcount k').add_const 1)
    have htarget : Measurable[𝔾 p] (fun ω ↦ aRTSTarget A Y θ₀ T (p + 1) ω k) := by
      simp only [aRTSTarget]
      exact (measurable_pi_apply k).comp (hT.measurable.comp hest)
    simp only [aRTSFEUnder, ← count_indicator_eq_pullCount]
    exact (measurableSet_le (hcount k) (measurable_const.mul htarget)).union
      (measurableSet_le (hcount k) measurable_const)

/-- **A previous-history event on which the selection probability vanishes is never a pull.** If
`S m` is `ℱ_{m-1}`-measurable and `p_{m,k} ≤ 0` there, then almost surely `A_m ≠ k` on `S m`.

The conditional probability is nonnegative, so it is *zero* on `S m`; integrating the indicator over
the previous-history event `S m` therefore gives `0`, and a nonnegative function with zero integral
vanishes a.e. Measurability of `S m` with respect to `ℱ_{m-1}` — not merely `ℱ_m` — is what makes
`setIntegral_condExp` applicable, and is the crux: the conditioning event has to be decided before
the draw it constrains.

Both ways the aRTS family forbids a pull factor through this: the `α = 0` throttle
(`not_pulled_of_not_aRTSFEUnder_of_alpha_zero`) and forced exploration's exclusion of arms that are
not least-sampled (`fe_of_isARTSFE`). -/
lemma ae_action_ne_of_selProb_nonpos
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {k : 𝓐} {S : ℕ → Set Ω}
    (hS : ∀ m, MeasurableSet[h.filtration.shiftDown m] (S m))
    (hsel : ∀ᵐ ω ∂P, ∀ m, ω ∈ S m →
      aRTSSelProb A k h.filtration P m ω
        ≤ 0) :
    ∀ᵐ ω ∂P, ∀ m, ω ∈ S m → A m ω ≠ k := by
  set 𝔽 := h.filtration with h𝔽
  have hint : ∀ i, Integrable (actionIndicator A k i) P := fun i ↦
    (integrable_const (1 : ℝ)).indicator ((h.measurable_action i) (measurableSet_singleton k))
  have hstep : ∀ m, ∀ᵐ ω ∂P, ω ∈ S m → A m ω ≠ k := by
    intro m
    have hSmeas : MeasurableSet[𝔽.shiftDown m] (S m) := hS m
    have hzero : ∫ ω in S m, actionIndicator A k m ω ∂P = 0 := by
      rw [← setIntegral_condExp (𝔽.shiftDown.le m) (hint m) hSmeas]
      refine setIntegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hsel, condExp_nonneg (m := 𝔽.shiftDown m) (f := actionIndicator A k m)
        (ae_of_all _ fun ω ↦ actionIndicator_nonneg A k m ω)] with ω hthr hnn hωS
      exact le_antisymm (hthr m hωS) hnn
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun ω ↦ actionIndicator_nonneg A k m ω) ((hint m).restrict (s := S m))).mp hzero
    rw [Filter.EventuallyEq, ae_restrict_iff' ((𝔽.shiftDown).le m _ hSmeas)] at hae
    filter_upwards [hae] with ω hω hnot hAk
    have hval : actionIndicator A k m ω = 1 := by
      simp only [actionIndicator]
      rw [Set.indicator_of_mem (show ω ∈ {ω | A m ω = k} from hAk)]
    have hzeroω := hω hnot
    rw [hval] at hzeroω
    exact one_ne_zero hzeroω
  exact ae_all_iff.mpr hstep

/-- **`IsARTSFE` discharges the throttle hypothesis**, exactly as `throttle_of_isARTS` does for
`IsARTS`. At `m = 0` the antecedent is vacuous (`N_0 = 0 ≤ 0 · ρ̂`); at `m = n+1` it is
`IsARTSFE.throttle` transported through `aRTSSelProb_succ_ae`, `histTarget_eq` and `histCount_eq`.
The two premises of the field are the two disjuncts of `¬ aRTSFEUnder`. -/
@[specifies IsARTSFE "the `throttle` field, stated on arbitrary histories, really is the \
process-level throttle — the same bridge `IsARTS` enjoys",
  specifies aRTSFEUnder "fixes the disjunction: an arm is exempt from the throttle when it is \
under-sampled *or* under-explored, so its negation carries both premises the `throttle` field \
needs. Using a conjunction here would silently strengthen the design's obligation"]
lemma throttle_of_isARTSFE [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {hsched : ℕ → ℝ} {α : ℝ}
    (hFE : IsARTSFE alg θ₀ T hsched α) (k : 𝓐) :
    ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m →
      aRTSSelProb A k h.filtration P m ω
        ≤ α * aRTSTarget A Y θ₀ T m ω k := by
  refine ae_all_iff.mpr fun m ↦ ?_
  cases m with
  | zero =>
    filter_upwards with ω hm
    exact absurd (by simp [aRTSFEUnder] : aRTSFEUnder A Y θ₀ T hsched k ω 0) hm
  | succ n =>
    filter_upwards [aRTSSelProb_succ_ae h k n] with ω hsel hm
    rw [aRTSFEUnder, not_or, not_le, not_le] at hm
    obtain ⟨hover, hexpl⟩ := hm
    rw [hsel, ← histTarget_eq (O := O)]
    refine hFE.throttle (n + 1) (history O A Y (n + 1) ω) k ?_ ?_
    · rw [histTarget_eq, ← histCount_eq, count_indicator_eq_pullCount]
      push_cast at hover ⊢
      linarith
    · rw [← histCount_eq, count_indicator_eq_pullCount]; exact hexpl

/-- The rounds at which forced exploration **forbids** arm `k`: some arm is under-explored, yet `k`
is either not under-explored itself or not among the least-sampled. -/
def feForbidden [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (hsched : ℕ → ℝ) (k : 𝓐) (m : ℕ) : Set Ω :=
  {ω | (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) ∧
    (hsched m < (pullCount A k m ω : ℝ) ∨
      ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m ∧
        (pullCount A j m ω : ℝ) < (pullCount A k m ω : ℝ))}

omit [IsProbabilityMeasure P] in
/-- `feForbidden` is a **previous-history** event: it is built from counts alone. -/
@[specifies feForbidden "the reason the event is phrased through counts rather than through the \
action: it is measurable for the *previous*-history σ-algebra, which is what lets a selection \
probability of `0` on it be turned into \"arm `k` is a.s. not drawn\""]
lemma measurableSet_shiftDown_feForbidden [Finite 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (hsched : ℕ → ℝ) (k : 𝓐) (m : ℕ) :
    MeasurableSet[h.filtration.shiftDown m]
      (feForbidden A hsched k m) := by
  have hcount : ∀ k' : 𝓐,
      Measurable[h.filtration.shiftDown m]
        (fun ω ↦ (pullCount A k' m ω : ℝ)) := by
    intro k'
    simp only [← count_indicator_eq_pullCount]
    exact measurable_shiftDown_count h k' m
  have hex : MeasurableSet[h.filtration.shiftDown m]
      {ω | ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m} := by
    have hset : {ω | ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m}
        = ⋃ j, {ω | (pullCount A j m ω : ℝ) ≤ hsched m} := by ext ω; simp
    rw [hset]
    exact MeasurableSet.iUnion fun j ↦ measurableSet_le (hcount j) measurable_const
  have hmin : MeasurableSet[h.filtration.shiftDown m]
      {ω | ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m ∧
        (pullCount A j m ω : ℝ) < (pullCount A k m ω : ℝ)} := by
    have hset : {ω | ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m ∧
        (pullCount A j m ω : ℝ) < (pullCount A k m ω : ℝ)}
        = ⋃ j, ({ω | (pullCount A j m ω : ℝ) ≤ hsched m} ∩
          {ω | (pullCount A j m ω : ℝ) < (pullCount A k m ω : ℝ)}) := by ext ω; simp
    rw [hset]
    exact MeasurableSet.iUnion fun j ↦
      (measurableSet_le (hcount j) measurable_const).inter (measurableSet_lt (hcount j) (hcount k))
  exact hex.inter ((measurableSet_lt measurable_const (hcount k)).union hmin)

/-- **`IsARTSFE` discharges the forced-exploration hypothesis `hfe`.** Almost surely, whenever some
arm is under-explored, the arm actually drawn is under-explored and least-sampled.

The `forced` field says the policy gives every *other* arm mass zero; `aRTSSelProb_succ_ae` turns
that into `p_{m,k} = 0`, and `ae_action_ne_of_selProb_nonpos` — whose hypothesis is met because
`feForbidden` is a previous-history event — turns it into "`k` is a.s. not drawn". Ranging over the
(countably many) arms and instantiating at `k = A_m ω` gives the claim. At `m = 0` all counts are
zero, so `feForbidden` is empty and there is nothing to prove. -/
@[specifies IsARTSFE "the `forced` field, a statement about policy *mass*, delivers the \
action-level rule the asymptotic theorems consume: whenever some arm is under-explored, the arm \
actually drawn is a least-sampled under-explored one"]
lemma fe_of_isARTSFE [Finite 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {hsched : ℕ → ℝ} {α : ℝ}
    (hFE : IsARTSFE alg θ₀ T hsched α) :
    ∀ᵐ ω ∂P, ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω := by
  have hsel : ∀ k : 𝓐, ∀ᵐ ω ∂P, ∀ m, ω ∈ feForbidden A hsched k m →
      aRTSSelProb A k h.filtration P m ω
        ≤ 0 := by
    intro k
    refine ae_all_iff.mpr fun m ↦ ?_
    cases m with
    | zero =>
      filter_upwards with ω hω
      obtain ⟨⟨j, hj⟩, hbad⟩ := hω
      have hz : ∀ j' : 𝓐, (pullCount A j' 0 ω : ℝ) = 0 := fun j' ↦ by
        rw [← count_indicator_eq_pullCount]; simp [count]
      rw [hz j] at hj
      rcases hbad with hbad | ⟨j', _, hj'⟩
      · rw [hz k] at hbad; linarith
      · rw [hz j', hz k] at hj'; linarith
    | succ n =>
      filter_upwards [aRTSSelProb_succ_ae h k n] with ω hselω hω
      obtain ⟨hex, hbad⟩ := hω
      have hpc : ∀ j : 𝓐, (pullCount A j (n + 1) ω : ℝ)
          = (pullCount' (n + 1) (history O A Y (n + 1) ω) j : ℝ) := fun j ↦ by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
          (pullCount_eq_pullCount' (A := A) (O := O) (R' := Y) (a := j) (n := n + 1) (ω := ω))
      simp only [hpc] at hex hbad
      rw [hselω, hFE.forced (n + 1) (history O A Y (n + 1) ω) k hex hbad]
      simp
  have hall : ∀ᵐ ω ∂P, ∀ (k : 𝓐) (m : ℕ), ω ∈ feForbidden A hsched k m → A m ω ≠ k :=
    ae_all_iff.mpr fun k ↦ ae_action_ne_of_selProb_nonpos h
      (fun m ↦ measurableSet_shiftDown_feForbidden h hsched k m) (hsel k)
  filter_upwards [hall] with ω hω m hex
  by_contra hcon
  refine hω (A m ω) m ⟨hex, ?_⟩ rfl
  rw [not_and_or] at hcon
  rcases hcon with h1 | h2
  · exact Or.inl (lt_of_not_ge h1)
  · push Not at h2
    obtain ⟨j, hj1, hj2⟩ := h2
    exact Or.inr ⟨j, hj1, by exact_mod_cast hj2⟩

/-- **A.s. consistency of the `aRTSFE` allocation proportions** [YDK26, Theorem 5.1], consistency
direction. For a forced-exploration design — given here by the history-level design
predicate `IsARTSFE`, whose throttle is transported to the process by `throttle_of_isARTSFE` —
with an exploration schedule `hsched`, the allocation proportions converge a.s. to the common
limit of the plug-in targets: `N_{n,k}/n → v_k` and `ρ̂_{n,k} → v_k` for every arm `k`.

This is a *direct reuse* of `consistency_of_hitting`: the forced-exploration hitting time
`hitting (aRTSFEUnder …)` and the throttle discharge the generic key inequality exactly as for
`aRTS`, and the only design-specific ingredient — the smallness `N_ℓ - ℓ ρ̂_ℓ ≤ (h(ℓ))^+ = o(n)` —
is `aRTSFE_smallness`. -/
@[specifies IsExplorationSchedule "the three retained fields are enough for the design's \
consistency — no `o(√m)` condition is needed, which is precisely the point of weakening the \
paper's definition"]
theorem aRTSFE_proportion_tendsto [DecidableEq 𝓐] [Fintype 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hARTSFE : IsARTSFE alg θ₀ T hsched α) :
    ∀ᵐ ω ∂P, ∃ u : 𝓐 → ℝ, ∀ k,
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (u k))
        ∧ Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop (𝓝 (u k)) :=
  consistency_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) (fun k ↦ throttle_of_isARTSFE h hARTSFE k)
    (aRTSFE_smallness_all θ₀ T hTnn hh)

/-! ### Asymptotic normality under forced exploration (non-sparse targets)

Theorem 5.1 of the paper, normality direction: the conclusions of the paper's Theorem 4.2 for the
`aRTSFE` family. Each result is a *direct reuse* of the corresponding abstract-hitting-time theorem
with the forced-exploration predicate `aRTSFEUnder`: the design enters as `IsARTSFE` — the
process-level throttle is `throttle_of_isARTSFE` — and the new ingredients are the
forced-exploration smallness lemmas (`aRTSFE_smallness_all`/`_op`/`_upper`) discharging the generic
conditions.

Like the `aRTS` results, these state their design hypothesis as the history-level predicate rather
than as a process-level throttle, so they mention only the design, the environment and the
schedule. That is why this section sits after `throttle_of_isARTSFE`. -/

/-- **`o_p(√n)` proportion deviation under forced exploration** [YDK26, Theorem 5.1], carrying
equation (5) of Theorem 4.2 (i). `|N_{n,k} - n ρ̂_{n,k}| = o_p(√n)` for the `aRTSFE` family.
A direct reuse of `prop_dev_of_hitting`; the `o_p`-smallness is `aRTSFE_smallness_op`, whose
Condition **B** input (`hv`, `hNconv`) is the consistency this theorem already establishes. -/
@[specifies IsExplorationSchedule "the three retained fields are enough for the `√n`-scaled \
theory as well, not only for consistency: under Condition **B** forced exploration switches \
itself off, so the paper's `o(√m)` is never needed"]
theorem aRTSFE_prop_dev [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hARTSFE : IsARTSFE alg θ₀ T hsched α) (k : 𝓐) :
    IsLittleOpOne P (fun n ω ↦ ((pullCount A k n ω : ℝ)
      - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k) / √n) := by
  have hT : Continuous T := hlip.continuous
  have hthrottle := fun k' ↦ throttle_of_isARTSFE (A := A) (Y := Y) h hARTSFE k'
  have hgs := aRTSFE_smallness_all (A := A) (Y := Y) (P := P) θ₀ T hTnn hh
  have hθconv := theta_consistent_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos
  have hv := target_pos_of_theta_consistent hTpos hθconv
  have hNconv := fun k' ↦ proportion_tendsto_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos k'
  exact prop_dev_of_hitting h hνk θ₀ T hTnn hTsum α hα hα1 hlip hTpos hθconv hNconv
    (aRTSFEUnder A Y θ₀ T hsched) (fun k m ↦ measurableSet_aRTSFEUnder h θ₀ hT hsched k m)
    hthrottle (fun k' ↦ aRTSFE_smallness_op h θ₀ hT hh k' (hv k') (hNconv k')) k

/-- **A.s. `O(√(n log log n))` proportion deviation under forced exploration**
[YDK26, Theorem 5.1], carrying equation (6) of Theorem 4.2 (i).
`N_{n,k} - n ρ̂_{n,k} = O(√(n log log n))` a.s. for the `aRTSFE` family. A direct reuse of
`prop_dev_ae_of_hitting`; the loglog rate is `rho_rate_of_hitting` and the smallness is
`aRTSFE_smallness_upper`, whose Condition **B** input is the consistency this theorem already
establishes. -/
theorem aRTSFE_prop_dev_ae [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hARTSFE : IsARTSFE alg θ₀ T hsched α) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ (pullCount A k n ω : ℝ) - (n : ℝ) * aRTSTarget A Y θ₀ T n ω k)
      =O[atTop] fun n ↦ √(n * Real.log (Real.log n)) := by
  have hthrottle := fun k' ↦ throttle_of_isARTSFE (A := A) (Y := Y) h hARTSFE k'
  have hgs := aRTSFE_smallness_all (A := A) (Y := Y) (P := P) θ₀ T hTnn hh
  have hθconv := theta_consistent_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos
  have hv := target_pos_of_theta_consistent hTpos hθconv
  have hNconv := fun k' ↦ proportion_tendsto_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos k'
  exact prop_dev_ae_of_hitting h θ₀ T hT hTnn hTsum α hα hα1 hTpos hθconv
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle
    (fun k' ↦ rho_rate_of_hitting h hνk hT hTnn hTsum hα (aRTSFEUnder A Y θ₀ T hsched)
      hthrottle hgs hTpos hT_diff k')
    (fun k' ↦ aRTSFE_smallness_upper θ₀ T hh k' (hv k') (hNconv k')) k

/-- **A.s. `O(√(n log log n))` count-versus-target deviation under forced exploration**
[YDK26, Theorem 5.1], carrying equation (7) of Theorem 4.2 (i).
`N_{n,k} - n v_k = O(√(n log log n))` a.s. for the `aRTSFE` family. A direct reuse of
`count_sub_smul_ae_of_hitting`. -/
theorem aRTSFE_count_sub_smul_ae [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hARTSFE : IsARTSFE alg θ₀ T hsched α) (k : 𝓐) :
    ∀ᵐ ω ∂P, (fun n ↦ (pullCount A k n ω : ℝ) - (n : ℝ) * T ν.means k)
      =O[atTop] fun n ↦ √(n * Real.log (Real.log n)) := by
  have hthrottle := fun k' ↦ throttle_of_isARTSFE (A := A) (Y := Y) h hARTSFE k'
  have hgs := aRTSFE_smallness_all (A := A) (Y := Y) (P := P) θ₀ T hTnn hh
  have hθconv := theta_consistent_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos
  have hv := target_pos_of_theta_consistent hTpos hθconv
  have hNconv := fun k' ↦ proportion_tendsto_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos k'
  exact count_sub_smul_ae_of_hitting h θ₀ T hT hTnn hTsum α hα hα1 hTpos hθconv
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle
    (fun k' ↦ rho_rate_of_hitting h hνk hT hTnn hTsum hα (aRTSFEUnder A Y θ₀ T hsched)
      hthrottle hgs hTpos hT_diff k')
    (fun k' ↦ aRTSFE_smallness_upper θ₀ T hh k' (hv k') (hNconv k')) k

/-- **Joint central limit theorem under forced exploration** [YDK26, Theorem 5.1], carrying
equation (9) of Theorem 4.2 (ii). The `√n`-scaled joint deviation vector
`(√n(N_n/n - v), √n(ρ̂_n - v))` converges weakly to the block-Gaussian `𝒩(0, Ω)` for the `aRTSFE`
family. A direct reuse of `clt_joint_of_hitting`; the smallness conditions are
`aRTSFE_smallness_all` and `aRTSFE_smallness_op`. -/
theorem aRTSFE_clt_joint [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (G : Matrix 𝓐 𝓐 ℝ)
    (hTderiv : HasFDerivAt
      (fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (T (WithLp.ofLp x)) : EuclideanSpace ℝ 𝓐))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) G) (WithLp.toLp 2 ν.means))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hARTSFE : IsARTSFE alg θ₀ T hsched α) :
    TendstoInDistribution (jointSqrtNVec ν A Y θ₀ T (T ν.means)) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (Matrix.fromBlocks
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T ν.means a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T ν.means a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T ν.means a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T ν.means a) * Gᵀ))) := by
  have hT : Continuous T := hlip.continuous
  have hthrottle := fun k' ↦ throttle_of_isARTSFE (A := A) (Y := Y) h hARTSFE k'
  have hgs := aRTSFE_smallness_all (A := A) (Y := Y) (P := P) θ₀ T hTnn hh
  have hθconv := theta_consistent_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos
  have hv := target_pos_of_theta_consistent hTpos hθconv
  have hNconv := fun k' ↦ proportion_tendsto_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
    (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos k'
  exact clt_joint_of_hitting h hνk θ₀ T hTnn hTsum α hα hα1 hlip hTpos G hTderiv
    (aRTSFEUnder A Y θ₀ T hsched) (fun k m ↦ measurableSet_aRTSFEUnder h θ₀ hT hsched k m)
    hthrottle hgs (fun k' ↦ aRTSFE_smallness_op h θ₀ hT hh k' (hv k') (hNconv k'))

end AlphaRAR
