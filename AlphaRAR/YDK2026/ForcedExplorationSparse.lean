/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.YDK2026.ForcedExploration
public meta import TrustAnnotations

/-!
# Forced exploration with sparse targets

This file continues `AlphaRAR.YDK2026.ForcedExploration` with the sparse targets of Section 5 of
the paper, where some arms have target proportion `v_k = 0`. Under Condition **B** forced
exploration switches itself off; with a sparse target it does not, and it is what keeps a sparse arm
sampled. The file proves the consistency and the rate of a sparse arm's estimator, and the sparse
componentwise CLT, under the reversed schedule condition `(⋆) : √(m log log m) ≪ h(m) = o(m)` in
place of the paper's `h(m) = o(√m)` (see `maths/sparse-clt-fix.md`).

## Main results

* `AlphaRAR.aRTSFE_sparse_rate_of_isARTSFE` — consistency and rate for sparse targets.
* `AlphaRAR.aRTSFE_sparse_clt` — the sparse componentwise CLT, given `FEfed`.
* `AlphaRAR.aRTSFE_sparse_clt_of_contDiffAt` — the same conclusion with `FEfed` *discharged*, from
  `C²` smoothness of the target and the reversed schedule condition `(⋆)`;
  `AlphaRAR.sched23_satisfies_schedule_hypotheses` shows the schedule hypotheses are satisfiable,
  and only outside the paper's condition (ii).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Real
open scoped Topology ENNReal NNReal Matrix

namespace AlphaRAR

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- **For `α = 0` the throttle forbids throttled pulls outright** (Step 4, `α = 0`, pathwise).
Whenever arm `k` is neither under-sampled nor under-explored, it is a.s. not pulled.

This needs **no decay hypothesis at all**: the conditioning event `{¬ aRTSFEUnder}` is itself
previous-history measurable
(`measurableSet_shiftDown_aRTSFEUnder`), so the throttle applies inside the conditional expectation
directly. That matters, because the decay bound has a *random* constant (the LIL constant), so a
hypothesis of the form "`ρ̂ ≤ g` for a deterministic `g`" is not dischargeable — see
`aRTSTarget_le_loglog_of_quadratic`. The decay is then applied *pathwise* afterwards, via
`not_aRTSFEUnder_of_sched_lt`. -/
lemma not_pulled_of_not_aRTSFEUnder_of_alpha_zero [DecidableEq 𝓐] [Finite 𝓐]
    [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ}
    (hT : Continuous T) {hsched : ℕ → ℝ} (hARTSFE : IsARTSFE alg θ₀ T hsched 0) (k : 𝓐) :
    ∀ᵐ ω ∂P, ∀ m, ¬ aRTSFEUnder A Y θ₀ T hsched k ω m → A m ω ≠ k :=
  ae_action_ne_of_selProb_nonpos h
    (fun m ↦ (measurableSet_shiftDown_aRTSFEUnder h θ₀ hT hsched k m).compl)
    ((throttle_of_isARTSFE h hARTSFE k).mono fun ω hω m hm ↦ by simpa using hω m hm)

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **The plug-in target of a sparse arm decays at the loglog rate** (the `hdecay` input of
`not_aRTSFEUnder_of_sched_lt`), pathwise.

Since the target takes values in the simplex (`T ≥ 0`) and `T(Θ)_k = v_k = 0` for a sparse arm, the
point `Θ` *minimises* `x ↦ T(x)_k`; hence `∇T_k(Θ) = 0` and a `C²` target obeys a local quadratic
bound `T(x)_k ≤ Cq ‖x - Θ‖²`, which is hypothesis `hquad`. Feeding in the per-arm loglog rate
`hrate` — what the subsampled LIL `abs_estimator_sub_le_rate_loglog_N` delivers, after replacing the
random count `N_{m,j}` by a deterministic lower bound `L m` — gives `ρ̂_{m,k} = O(log log m / L m)`.

Combined with `L m ≳ h m` (forced exploration, `pullCount_ge_min_sched_of_fe`) this is the decay the
throttle step consumes: `ρ̂_{m,k} < h(m)/m` reduces to `h(m)² ≫ m log log m`, i.e. exactly `(⋆)`.

**The constant is necessarily random**: the LIL constant depends on `ω`. So the `hdecay` hypothesis
of the throttle lemmas cannot be met with a *deterministic* bound — it has to be read pathwise,
which is how `not_aRTSFEUnder_of_sched_lt` is stated. -/
lemma aRTSTarget_le_loglog_of_quadratic [Fintype 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐} {Cq C : ℝ} {L : ℕ → ℝ}
    (hCq : 0 ≤ Cq) (hLnn : ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log (Real.log m) / L m)
    (hquad : ∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k
      ≤ Cq * ∑ j, (estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m
          - ν.means j) ^ 2)
    (hrate : ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m - ν.means j|
        ≤ C * √(Real.log (Real.log m) / L m)) :
    ∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k
      ≤ (Cq * Fintype.card 𝓐 * C ^ 2) * (Real.log (Real.log m) / L m) := by
  filter_upwards [hquad, eventually_all.mpr hrate, hLnn] with m hq hr hLm
  refine hq.trans ?_
  have hterm : ∀ j ∈ (Finset.univ : Finset 𝓐),
      (estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m - ν.means j) ^ 2
        ≤ C ^ 2 * (Real.log (Real.log m) / L m) := by
    intro j _
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hr j) 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hLm] at h2
    exact h2
  calc Cq * ∑ j, (estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m
          - ν.means j) ^ 2
      ≤ Cq * ∑ _j : 𝓐, C ^ 2 * (Real.log (Real.log m) / L m) := by
        gcongr with j hj
        exact hterm j hj
    _ = (Cq * Fintype.card 𝓐 * C ^ 2) * (Real.log (Real.log m) / L m) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **The quadratic bound `hquad` comes for free from a `C²` target**, so it need not be assumed.

For a *sparse* arm `k` one has `T(Θ)_k = v_k = 0` while `T ≥ 0` everywhere (the target takes values
in the simplex), so `Θ` is a global minimum of `x ↦ T(x)_k`. Fermat's theorem kills the linear term
of the Taylor expansion, and `C²` smoothness turns the remainder into `K‖x - Θ‖²`
(`exists_eventually_sub_le_mul_sq_of_isLocalMin`) — no Hessian is ever named. Consistency `θ̂_m → Θ`
puts the plug-in point inside that neighbourhood eventually.

The sup norm of `𝓐 → ℝ` is converted to the coordinatewise sum by `sq_norm_le_sum_sq`, which is the
shape in which the per-arm rates of `aRTSTarget_le_loglog_of_quadratic` plug in. -/
lemma exists_aRTSTarget_le_mul_sum_sq [Fintype 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐}
    (hT2 : ContDiffAt ℝ 2 (T · k) ν.means)
    (hTnn : ∀ z, 0 ≤ T z k) (hTzero : T ν.means k = 0)
    (hcons : ∀ j, Tendsto
      (fun m ↦ estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m)
      atTop (𝓝 (ν.means j))) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k
      ≤ Cq * ∑ j, (estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m
          - ν.means j) ^ 2 := by
  have hmin : IsLocalMin (T · k) ν.means := by
    apply Eventually.of_forall
    intro z
    change T ν.means k ≤ T z k
    rw [hTzero]
    exact hTnn z
  obtain ⟨K, hK, hbd⟩ := exists_eventually_sub_le_mul_sq_of_isLocalMin hmin hT2
  have hest : Tendsto
      (fun m ↦ fun j ↦ estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m)
      atTop (𝓝 ν.means) := tendsto_pi_nhds.mpr hcons
  refine ⟨K, hK, ?_⟩
  filter_upwards [hest.eventually hbd] with m hm
  have hkey : T (fun j ↦ estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m) k
      - T ν.means k
      ≤ K * ‖(fun j ↦ estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m)
          - ν.means‖ ^ 2 := hm
  rw [hTzero, sub_zero] at hkey
  exact hkey.trans (mul_le_mul_of_nonneg_left (sq_norm_le_sum_sq _) hK)

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **The loglog decay of a sparse arm's plug-in target, from `C²` smoothness alone.**

This is `aRTSTarget_le_loglog_of_quadratic` with its `hquad` hypothesis discharged by
`exists_aRTSTarget_le_mul_sum_sq`: the only structural input left is that `x ↦ T(x)_k` is `C²` at
`Θ`, nonnegative, and vanishes there (sparsity). Consistency of `θ̂` is not assumed either — it
follows from `hrate` together with `log log m / L m → 0`, which `L m ≳ h m → ∞` already gives.

The constant is existentially quantified because it is genuinely `ω`-dependent: `C` is the LIL
constant. -/
lemma exists_aRTSTarget_le_loglog_of_contDiffAt [Fintype 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐} {C : ℝ} {L : ℕ → ℝ}
    (hT2 : ContDiffAt ℝ 2 (T · k) ν.means)
    (hTnn : ∀ z, 0 ≤ T z k) (hTzero : T ν.means k = 0)
    (hLnn : ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log (Real.log m) / L m)
    (hL0 : Tendsto (fun m : ℕ ↦ Real.log (Real.log m) / L m) atTop (𝓝 0))
    (hrate : ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m - ν.means j|
        ≤ C * √(Real.log (Real.log m) / L m)) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k
      ≤ Cq * (Real.log (Real.log m) / L m) := by
  have hsqrt : Tendsto (fun m : ℕ ↦ C * √(Real.log (Real.log m) / L m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ ↦ √(Real.log (Real.log m) / L m)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hL0
    simpa using h1.const_mul C
  have hcons : ∀ j, Tendsto
      (fun m ↦ estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m)
      atTop (𝓝 (ν.means j)) := by
    intro j
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun m ↦ dist_nonneg) ?_ hsqrt
    filter_upwards [hrate j] with m hm
    rwa [Real.dist_eq]
  obtain ⟨Cq, hCq, hquad⟩ := exists_aRTSTarget_le_mul_sum_sq ω hT2 hTnn hTzero hcons
  exact ⟨Cq * Fintype.card 𝓐 * C ^ 2,
    mul_nonneg (mul_nonneg hCq (Nat.cast_nonneg _)) (sq_nonneg _),
    aRTSTarget_le_loglog_of_quadratic ω hCq hLnn hquad hrate⟩

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **Condition `(⋆)` beats every constant.** If `m log log m = o(L(m) h(m))` then for *any*
constant `Cq` the loglog bound eventually sits strictly below `h(m)/m`.

Quantifying over `Cq` is the whole point: the constant coming out of the LIL is random, so the
comparison has to survive an arbitrary one. Rearranged, `Cq (log log m)/L(m) < h(m)/m` is
`Cq · m log log m < L(m) h(m)`, and with `L ≍ h` this is `h(m)² ≫ m log log m`, i.e. `(⋆)` of
`maths/sparse-clt-fix.md`. -/
lemma eventually_mul_loglog_div_lt_of_star {hsched L : ℕ → ℝ} (Cq : ℝ)
    (hpos : ∀ᶠ m : ℕ in atTop, 0 < L m ∧ 0 < hsched m)
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (L m * hsched m))
      atTop (𝓝 0)) :
    ∀ᶠ m : ℕ in atTop, Cq * (Real.log (Real.log m) / L m) < hsched m / (m : ℝ) := by
  have h1 : Tendsto (fun m : ℕ ↦ Cq * ((m : ℝ) * Real.log (Real.log m) / (L m * hsched m)))
      atTop (𝓝 0) := by simpa using hstar.const_mul Cq
  filter_upwards [hpos, h1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop 0] with m hm hlt hm0
  obtain ⟨hL, hh⟩ := hm
  have hm0' : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hstep := mul_lt_mul_of_pos_right hlt (div_pos hh hm0')
  rw [one_mul] at hstep
  calc Cq * (Real.log (Real.log m) / L m)
      = Cq * ((m : ℝ) * Real.log (Real.log m) / (L m * hsched m)) * (hsched m / (m : ℝ)) := by
        field_simp
    _ < hsched m / (m : ℝ) := hstep

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **`C²` smoothness plus `(⋆)` supply the `hdecay` input of `fEfed_of_decay`**, pathwise.

This closes the chain of `maths/sparse-clt-fix.md`: nothing about the target map is assumed beyond
`C²` at `Θ`, nonnegativity, and `T(Θ)_k = 0` (sparsity of arm `k`); the loglog rate `hrate` is what
the subsampled LIL delivers, and `(⋆)` is the reversed schedule condition
`√(m log log m) ≪ h(m) = o(m)` which replaces the paper's `h(m) = o(√m)`.

The randomness of the LIL constant is handled where it belongs: `g` is produced *inside* the
pathwise statement, and `eventually_mul_loglog_div_lt_of_star` is uniform in that constant. -/
lemma exists_decay_of_contDiffAt [Fintype 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} {k : 𝓐} {C : ℝ} {L hsched : ℕ → ℝ}
    (hT2 : ContDiffAt ℝ 2 (T · k) ν.means)
    (hTnn : ∀ z, 0 ≤ T z k) (hTzero : T ν.means k = 0)
    (hLnn : ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log (Real.log m) / L m)
    (hL0 : Tendsto (fun m : ℕ ↦ Real.log (Real.log m) / L m) atTop (𝓝 0))
    (hpos : ∀ᶠ m : ℕ in atTop, 0 < L m ∧ 0 < hsched m)
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (L m * hsched m))
      atTop (𝓝 0))
    (hrate : ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m - ν.means j|
        ≤ C * √(Real.log (Real.log m) / L m)) :
    ∃ g : ℕ → ℝ, (∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k ≤ g m) ∧
      (∀ᶠ m in atTop, g m < hsched m / (m : ℝ)) := by
  obtain ⟨Cq, _, hCq⟩ :=
    exists_aRTSTarget_le_loglog_of_contDiffAt ω hT2 hTnn hTzero hLnn hL0 hrate
  exact ⟨fun m ↦ Cq * (Real.log (Real.log m) / L m), hCq,
    eventually_mul_loglog_div_lt_of_star Cq hpos hstar⟩

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- **From the `N`-scaled loglog rate to a deterministic one.** The subsampled LIL
(`abs_estimator_sub_le_rate_loglog_N`) measures the estimator error against the arm's *own random*
count `N_{m,j}`, whereas `exists_decay_of_contDiffAt` needs it measured against a *deterministic*
`L(m)`. Given a deterministic floor `L(m) ≤ N_{m,j}` diverging to infinity, the two are compatible:

`log log N_{m,j} / N_{m,j} ≤ log log m / L(m)`,

since `N_{m,j} ≤ m` makes the numerator only smaller while `L(m) ≤ N_{m,j}` makes the denominator
only smaller. Both facts are needed — the floor alone would not control the numerator, and this is
why the argument runs through `log log m` rather than the more natural-looking `log log L(m)`.

The constants are merged into `∑ j |C_j|`, which dominates every `C_j` and is nonnegative; taking a
single constant is what lets `aRTSTarget_le_loglog_of_quadratic` sum the squared errors. -/
lemma exists_rate_loglog_of_pullCount_ge [Finite 𝓐] [DecidableEq 𝓐] (ω : Ω)
    {θ₀ : 𝓐 → ℝ} {L : ℕ → ℝ} (hLtop : Tendsto L atTop atTop)
    (hLle : ∀ j, ∀ᶠ m in atTop, L m ≤ (pullCount A j m ω : ℝ))
    (hC : ∀ j, ∃ C' : ℝ, ∀ᶠ m in atTop,
      |estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m - ν.means j|
        ≤ C' * √(Real.log (Real.log (pullCount A j m ω : ℝ))
            / (pullCount A j m ω : ℝ))) :
    ∃ C : ℝ, ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m - ν.means j|
        ≤ C * √(Real.log (Real.log m) / L m) := by
  classical
  let := Fintype.ofFinite 𝓐
  choose C' hC' using hC
  refine ⟨∑ i, |C' i|, fun j ↦ ?_⟩
  have hCnn : (0 : ℝ) ≤ ∑ i, |C' i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hCle : C' j ≤ ∑ i, |C' i| :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i ↦ |C' i|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ j))
  filter_upwards [hC' j, hLle j, hLtop.eventually_ge_atTop (Real.exp 1)] with m hm hLm hLe
  have hLpos : (0 : ℝ) < L m := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hNpos : (0 : ℝ) < (pullCount A j m ω : ℝ) := lt_of_lt_of_le hLpos hLm
  have hNm : (pullCount A j m ω : ℝ) ≤ (m : ℝ) := by exact_mod_cast pullCount_le j m ω
  -- `N ≥ e` gives `log N ≥ 1`, hence `log log N ≥ 0`; and `N ≤ m` gives `log log N ≤ log log m`.
  have hlogN : (1 : ℝ) ≤ Real.log (pullCount A j m ω : ℝ) :=
    (Real.le_log_iff_exp_le hNpos).mpr (hLe.trans hLm)
  have hlogm : Real.log (pullCount A j m ω : ℝ) ≤ Real.log m := Real.log_le_log hNpos hNm
  have hll : Real.log (Real.log (pullCount A j m ω : ℝ)) ≤ Real.log (Real.log m) :=
    Real.log_le_log (by linarith) hlogm
  have hllnn : (0 : ℝ) ≤ Real.log (Real.log (pullCount A j m ω : ℝ)) := Real.log_nonneg hlogN
  have hkey : Real.log (Real.log (pullCount A j m ω : ℝ)) / (pullCount A j m ω : ℝ)
      ≤ Real.log (Real.log m) / L m := by
    calc Real.log (Real.log (pullCount A j m ω : ℝ)) / (pullCount A j m ω : ℝ)
        ≤ Real.log (Real.log m) / (pullCount A j m ω : ℝ) := by gcongr
      _ ≤ Real.log (Real.log m) / L m := by
          gcongr
          linarith
  calc |estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m - ν.means j|
      ≤ C' j * √(Real.log (Real.log (pullCount A j m ω : ℝ))
          / (pullCount A j m ω : ℝ)) := hm
    _ ≤ (∑ i, |C' i|) * √(Real.log (Real.log (pullCount A j m ω : ℝ))
          / (pullCount A j m ω : ℝ)) := by gcongr
    _ ≤ (∑ i, |C' i|) * √(Real.log (Real.log m) / L m) := by gcongr

/-- The indicator of a **throttled pull** of arm `k`: arm `k` is selected at round `i` while it is
neither under-sampled nor under-explored — so neither the targeting rule nor forced exploration
called for it, and the `αRTS` throttle caps its probability at `α ρ̂_{i,k}`. -/
noncomputable def throttledIndicator [DecidableEq 𝓐] (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hsched : ℕ → ℝ) (k : 𝓐) (i : ℕ) : Ω → ℝ :=
  {ω | ¬ aRTSFEUnder A Y θ₀ T hsched k ω i}.indicator (actionIndicator A k i)

/-- **The throttled pulls are `o(h)`** (Step 4 of `maths/sparse-clt-fix.md`, the general `α > 0`
case, pathwise). Their count satisfies `E_n/h(n) → 0` a.s.

Doob-decompose `E_n = M_n + ∑_{i<n} P[𝟙 | ℱ_{i-1}]`. The conditioning event
`{¬ aRTSFEUnder i}` is previous-history measurable (`measurableSet_shiftDown_aRTSFEUnder`), so
`condExp_indicator` pulls it out and the throttle applies with **no side condition**, giving
`P[𝟙 | ℱ_{i-1}] ≤ α ρ̂_{i,k}` for *every* `i`; the martingale part is `O(√(n log log n))` by
`ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog`.

The compensator is compared against the *random* `∑ α ρ̂_{i,k}(ω)`, and `hsum` asks only that this
be `o(h(n))` almost surely. That is what makes the statement usable: the loglog decay of `ρ̂_{i,k}`
carries a *random* constant (the LIL constant — see `aRTSTarget_le_loglog_of_quadratic`), so a
hypothesis "`ρ̂ ≤ g` for a deterministic `g`" would not be dischargeable, whereas a random constant
is harmless inside an a.s. limit.

Step 3 (`not_aRTSFEUnder_of_sched_lt`) is what relates this count to the one
`pullCount_le_sched_of_fe_except` consumes: pathwise, and eventually, a pull at a round where arm
`k` is not under-explored *is* a throttled pull. -/
@[specifies throttledIndicator "what the indicator is built to count, and that the count is \
negligible: pulls the design was free *not* to make are `o(h(n))`, so forced exploration alone \
fixes a sparse arm's sample size to first order"]
lemma throttled_count_div_sched_tendsto_zero [DecidableEq 𝓐] [Finite 𝓐]
    [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {hsched : ℕ → ℝ} {θ₀ : 𝓐 → ℝ}
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (hTnn : ∀ z k, 0 ≤ T z k) {k : 𝓐} {α : ℝ}
    (hα : 0 ≤ α)
    (hARTSFE : IsARTSFE alg θ₀ T hsched α)
    (hsched_atTop : Tendsto hsched atTop atTop)
    (hsum : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k) / hsched n) atTop (𝓝 0))
    (hsqrt : ∀ C : ℝ,
      Tendsto (fun n : ℕ ↦ C * √((n : ℝ) * Real.log (Real.log n)) / hsched n)
        atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ count (fun i ↦ throttledIndicator A Y θ₀ T hsched k i ω) n / hsched n)
      atTop (𝓝 0) := by
  set 𝔽 := h.filtration with h𝔽
  set X : ℕ → Ω → ℝ := fun i ↦ throttledIndicator A Y θ₀ T hsched k i with hXdef
  set S : ℕ → Set Ω := fun i ↦ {ω | ¬ aRTSFEUnder A Y θ₀ T hsched k ω i} with hSdef
  have hSm : ∀ i, MeasurableSet[𝔽.shiftDown i] (S i) := fun i ↦
    (measurableSet_shiftDown_aRTSFEUnder h θ₀ hT hsched k i).compl
  have hintarm : ∀ i, Integrable (actionIndicator A k i) P := fun i ↦
    (integrable_const (1 : ℝ)).indicator ((h.measurable_action i) (measurableSet_singleton k))
  have hX0 : ∀ i ω, 0 ≤ X i ω := fun i ω ↦
    Set.indicator_nonneg (fun _ _ ↦ actionIndicator_nonneg A k i _) ω
  have hX1 : ∀ i ω, X i ω ≤ 1 := fun i ω ↦ by
    change ((S i).indicator (actionIndicator A k i)) ω ≤ 1
    rw [Set.indicator_apply]
    split_ifs with hc
    · exact actionIndicator_le_one A k i ω
    · norm_num
  have hXint : ∀ i, Integrable (X i) P := fun i ↦
    (hintarm i).indicator ((𝔽.shiftDown).le i _ (hSm i))
  have hXadapt : StronglyAdapted 𝔽 X := fun i ↦
    StronglyMeasurable.indicator
      (((measurable_const (a := (1 : ℝ))).indicator ((measurableSet_singleton k).preimage
        (h.adapted_action.measurable_le
          (le_refl i)))).stronglyMeasurable)
      (Filtration.shiftDown_le_self 𝔽 i _ (hSm i))
  -- (a) The martingale part is `O(√(n log log n))`.
  have hLIL := ae_eventually_abs_assignMart_le_sqrt_nat_mul_loglog (ℱ := 𝔽) hXadapt hXint
    (fun n ↦ ae_of_all _ fun ω ↦ hX0 n ω) (fun n ↦ ae_of_all _ fun ω ↦ hX1 n ω)
  -- (b) The compensator is bounded by `α ρ̂_{i,k}` at *every* round — no side condition.
  have hcondle : ∀ i, ∀ᵐ ω ∂P,
      (P[X i | 𝔽.shiftDown i]) ω ≤ α * aRTSTarget A Y θ₀ T i ω k := by
    intro i
    have hpull : P[X i | 𝔽.shiftDown i]
        =ᵐ[P] (S i).indicator (P[actionIndicator A k i | 𝔽.shiftDown i]) :=
      condExp_indicator (hintarm i) (hSm i)
    filter_upwards [hpull, throttle_of_isARTSFE (A := A) (Y := Y) h hARTSFE k] with ω hp hthr
    rw [hp, Set.indicator_apply]
    split_ifs with hc
    · exact hthr i hc
    · exact mul_nonneg hα (by simp only [aRTSTarget]; exact hTnn _ _)
  have hpp : ∀ᵐ ω ∂P, ∀ n, predictablePart (count X) 𝔽.shiftDown P n ω
      ≤ ∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k := by
    filter_upwards [ae_all_iff.mpr hcondle] with ω hω n
    have hterm : ∀ i, (P[count X (i + 1) - count X i | 𝔽.shiftDown i]) ω
        ≤ α * aRTSTarget A Y θ₀ T i ω k := by
      intro i
      have heq : count X (i + 1) - count X i = X i := by
        funext ω'; simp only [Pi.sub_apply, count_succ, Pi.add_apply]; ring
      rw [heq]; exact hω i
    calc predictablePart (count X) 𝔽.shiftDown P n ω
        = ∑ i ∈ Finset.range n, (P[count X (i + 1) - count X i | 𝔽.shiftDown i]) ω := by
          rw [predictablePart, Finset.sum_apply]
      _ ≤ ∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k :=
          Finset.sum_le_sum fun i _ ↦ hterm i
  -- (c) Combine and squeeze.
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < hsched n := hsched_atTop.eventually_gt_atTop 0
  filter_upwards [hLIL, hpp, hsum] with ω hlilω hppω hsumω
  obtain ⟨C, hC⟩ := hlilω
  have hmaj : Tendsto (fun n : ℕ ↦ C * √((n : ℝ) * Real.log (Real.log n)) / hsched n
      + (∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k) / hsched n) atTop (𝓝 0) := by
    have := (hsqrt C).add hsumω
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hpos] with n hn
    exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hX0 i ω) hn.le
  · filter_upwards [hC, hpos] with n hCn hn
    have hdecomp : count (X · ω) n
        = assignMart X 𝔽 P n ω + predictablePart (count X) 𝔽.shiftDown P n ω := by
      have hm : assignMart X 𝔽 P n = count X n - predictablePart (count X) 𝔽.shiftDown P n := rfl
      have happ : assignMart X 𝔽 P n ω
          = count (X · ω) n - predictablePart (count X) 𝔽.shiftDown P n ω := by
        rw [hm]; simp [count, Finset.sum_apply]
      linarith [happ]
    rw [hdecomp, ← add_div]
    gcongr
    · exact (le_abs_self _).trans hCn
    · exact hppω n


/-- **The sparse componentwise CLT for `aRTSFE`** (Corollary 5.3 of the paper), with the regularity
input discharged by forced exploration. With `D_n = diag(√N_{n,1},…,√N_{n,K})`,
`D_n(θ̂_n - θ) ⇒ 𝒩(0, diag(V_1,…,V_K))`.

Arms are split by the predicate `FEfed`:
* `FEfed a` — arm `a` is eventually fed *only* by forced exploration (hypothesis `hFE`). Its count
  is then regular against the deterministic schedule, `N_{n,a}/h(n) → 1`
  (`pullCount_div_sched_tendsto_one`). This is the sparse case: no positive proportion is needed.
* `¬ FEfed a` — arm `a` has a positive limiting proportion `v_a > 0` with `N_{n,a}/n → v_a`
  (hypotheses `hpos`, `hprop`), so its count is regular against `v_a · n`.

Both arms are then covered by the *same* per-arm normalizer
`c_{a,n} = if FEfed a then h(n) else v_a · n`, which is exactly what
`estimatorError_joint_tendsto_multivariateGaussian` consumes (at `v ≡ 1`).

The split is unavoidable: not every arm can be FE-fed, since `∑_a N_{n,a} = n` while
`card 𝓐 · h(n) = o(n)`. -/
lemma aRTSFE_sparse_clt [Fintype 𝓐] [DecidableEq 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp id 2 (ν a))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hshift : Tendsto
      (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n) atTop (𝓝 1))
    (FEfed : 𝓐 → Prop) {v : 𝓐 → ℝ} (hpos : ∀ a, ¬ FEfed a → 0 < v a)
    (hfe : ∀ᵐ ω ∂P, ∀ m, (∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
      (pullCount A (A m ω) m ω : ℝ) ≤ hsched m ∧
        ∀ j, (pullCount A j m ω : ℝ) ≤ hsched m →
          pullCount A (A m ω) m ω ≤ pullCount A j m ω)
    (hFE : ∀ᵐ ω ∂P, ∀ a, FEfed a → ∃ (n₀ : ℕ) (E : ℕ → ℝ), Monotone E ∧
      (∀ m, n₀ ≤ m → A m ω = a → (¬ ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
        E m + 1 ≤ E (m + 1)) ∧
      Tendsto (fun n ↦ E n / hsched n) atTop (𝓝 0))
    (hprop : ∀ᵐ ω ∂P, ∀ a, ¬ FEfed a →
      Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / (n : ℝ)) atTop (𝓝 (v a))) :
    TendstoInDistribution (fun n ω ↦ (WithLp.toLp 2 (fun k ↦
        √(count (fun j ↦ actionIndicator A k j ω) n)
          * (estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k))
            : EuclideanSpace ℝ 𝓐)) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (Matrix.diagonal fun a ↦ Var[id; ν a])) := by
  classical
  -- `max 0 (h n)` rather than `h n`: the schedule may start negative (e.g. `n^{1/3} - K/2`),
  -- and the CLT wants a nonnegative normalizer. The two agree eventually, since `h n → ∞`.
  set c : 𝓐 → ℕ → ℝ := fun a n ↦ if FEfed a then max 0 (hsched n) else v a * n with hc_def
  have hc : ∀ a n, 0 ≤ c a n := by
    intro a n
    simp only [hc_def]
    split_ifs with hfed
    · exact le_max_left _ _
    · exact mul_nonneg (hpos a hfed).le (Nat.cast_nonneg n)
  have hc_atTop : ∀ a, Tendsto (c a) atTop atTop := by
    intro a
    simp only [hc_def]
    split_ifs with hfed
    · exact tendsto_atTop_mono (fun n ↦ le_max_right _ _) hh.tendsto_atTop
    · exact Tendsto.const_mul_atTop (hpos a hfed) tendsto_natCast_atTop_atTop
  -- The per-arm regularity `N_{n,a}/c_{a,n} → 1`, in the `count` form the CLT consumes.
  have hNconv : ∀ᵐ ω ∂P, ∀ a,
      Tendsto (fun n ↦ count (fun j ↦ actionIndicator A a j ω) n / c a n) atTop (𝓝 1) := by
    filter_upwards [hfe, hFE, hprop] with ω hfeω hFEω hpropω a
    have hbridge : ∀ n, count (fun j ↦ actionIndicator A a j ω) n = (pullCount A a n ω : ℝ) :=
      fun n ↦ count_indicator_eq_pullCount a n ω
    simp only [hbridge, hc_def]
    split_ifs with hfed
    · obtain ⟨n₀, E, hEmono, hEstep, hEsmall⟩ := hFEω a hfed
      refine (pullCount_div_sched_tendsto_one ω hh hfeω hshift (n₀ := n₀) E hEmono hEstep
        hEsmall).congr' ?_
      filter_upwards [hh.tendsto_atTop.eventually_gt_atTop 0] with n hn
      rw [max_eq_right hn.le]
    · -- `N/(v_a n) = (N/n)/v_a → v_a/v_a = 1`
      have hva := hpos a hfed
      have hdiv := (hpropω a hfed).div_const (v a)
      rw [div_self hva.ne'] at hdiv
      refine hdiv.congr fun n ↦ ?_
      rw [div_div, mul_comm]
  exact estimatorError_joint_tendsto_multivariateGaussian h θ₀ hνk hc hc_atTop
    (v := fun _ ↦ 1) (fun _ ↦ one_pos) hNconv

/-- **The `N`-scaled loglog estimator rate** (the analytic core of the paper's Theorem 5.2). If arm
`k`'s pull count diverges a.s. (which forced exploration guarantees), then under Condition **A** the
estimator error is `O(√(log log N_{n,k} / N_{n,k}))` a.s. — normalized by the arm's *own* sample
count `N_{n,k}`, so meaningful even for sparse arms. Unlike the `√n`-scaled rate `aRTS_rho_rate`,
this uses *only* `N_{n,k} → ∞` (no positive proportion). Via the exact Bahadur identity
`estimator_sub_eq` (`θ̂_{n,k} - θ_k = (Q_{n,k} + (θ_0-θ))/(N_{n,k}+1)`) and the subsampled loglog
LIL `abs_respMart_le_sqrt_nat_mul_loglog` (`|Q_{n,k}| ≤ 2√(2 V_k N_{n,k} log log N_{n,k})`), the two
terms are `O(√(N log log N)/N)` and `O(1/N)`, both `O(√(log log N/N))` (once `log log N ≥ 1`). -/
lemma abs_estimator_sub_le_rate_loglog_N [DecidableEq 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (k : 𝓐)
    (θ₀ : ℝ) (hνk : MemLp id 2 (ν k))
    (hNinf : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop) :
    ∀ᵐ ω ∂P, ∃ C', ∀ᶠ n in atTop,
      |estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) θ₀ n - ν.means k|
        ≤ C' * √(Real.log (Real.log (pullCount A k n ω : ℝ)) / (pullCount A k n ω : ℝ)) := by
  have hk_inf : ∀ᵐ ω ∂P, {j | A j ω = k}.Infinite := by
    filter_upwards [hNinf] with ω hNω; exact infinite_setOf_eq_of_pullCount_atTop hNω
  filter_upwards [hNinf, abs_respMart_le_sqrt_nat_mul_loglog h k hk_inf hνk]
    with ω hNω hQω
  have hV : (0 : ℝ) ≤ Var[id; ν k] := variance_nonneg _ _
  refine ⟨2 * √(2 * Var[id; ν k]) + |θ₀ - ν.means k|, ?_⟩
  have hlogloginf : Tendsto (fun n ↦ Real.log (Real.log (pullCount A k n ω : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNω)
  filter_upwards [hQω 2 (by norm_num), hNω.eventually_ge_atTop 1, hlogloginf.eventually_ge_atTop 1]
    with n hQn hN1 hL1
  set N : ℝ := (pullCount A k n ω : ℝ) with hNdef
  set L : ℝ := Real.log (Real.log N) with hLdef
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1' : (1 : ℝ) ≤ L := hL1
  have hsN : (0 : ℝ) < √N := Real.sqrt_pos.mpr hNpos
  -- Bahadur identity `θ̂ - θ = (Q + (θ₀-θ))/(N+1)`.
  have hcount : count (fun j ↦ actionIndicator A k j ω) n = N := count_indicator_eq_pullCount k n ω
  have hne : count (fun j ↦ actionIndicator A k j ω) n + 1 ≠ 0 := by rw [hcount]; positivity
  rw [estimator_sub_eq (X := fun j ↦ actionIndicator A k j ω) (Y · ω) (ν.means k) θ₀ n hne,
    respMG_indicator_eq_respMart, hcount]
  have hden : (0 : ℝ) < N + 1 := by linarith
  -- `√(L/N) = √L/√N`, and `√(2 V N L) = √(2V)·√N·√L`.
  have hsLN : √(L / N) = √L / √N := Real.sqrt_div (by linarith) N
  have hsL1 : (1 : ℝ) ≤ √L := Real.one_le_sqrt.mpr (by linarith)
  have hprod : √(2 * Var[id; ν k] * N * L) = √(2 * Var[id; ν k]) * √N * √L := by
    rw [show 2 * Var[id; ν k] * N * L = 2 * Var[id; ν k] * (N * L) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul hNpos.le, mul_assoc]
  set a : ℝ := |θ₀ - ν.means k| with hadef
  have hann : (0 : ℝ) ≤ a := abs_nonneg _
  have hVs : (0 : ℝ) ≤ √(2 * Var[id; ν k]) := Real.sqrt_nonneg _
  have hNN : √N * √N = N := Real.mul_self_sqrt hNpos.le
  have hsN_le : √N ≤ N + 1 := by nlinarith [hNN, hsN.le]
  have hc : (0 : ℝ) ≤ 2 * √(2 * Var[id; ν k]) * √L := by positivity
  -- Bound `|Q + (θ₀-θ)| ≤ |Q| + |θ₀-θ| ≤ 2√(2VNL) + a`.
  have hqbound : |respMart ν A Y k n ω| ≤ 2 * (√(2 * Var[id; ν k]) * √N * √L) := by
    refine hQn.trans (le_of_eq ?_)
    rw [hprod]
  have habs : |respMart ν A Y k n ω + (θ₀ - ν.means k)|
      ≤ 2 * (√(2 * Var[id; ν k]) * √N * √L) + a :=
    (abs_add_le _ _).trans (by linarith [hqbound])
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine habs.trans ?_
  rw [hsLN]
  -- Multiply through by `√N > 0` and use `√N·√N = N`.
  rw [show (2 * √(2 * Var[id; ν k]) + a) * (√L / √N) * (N + 1)
        = ((2 * √(2 * Var[id; ν k]) + a) * √L * (N + 1)) / √N by field_simp,
    le_div_iff₀ hsN,
    show (2 * (√(2 * Var[id; ν k]) * √N * √L) + a) * √N
        = 2 * √(2 * Var[id; ν k]) * √L * (√N * √N) + a * √N by ring, hNN]
  -- `2√(2V)√L·N + a√N ≤ (2√(2V)+a)√L(N+1)`, term by term.
  have h1 : 2 * √(2 * Var[id; ν k]) * √L * N ≤ 2 * √(2 * Var[id; ν k]) * √L * (N + 1) := by
    nlinarith [hc]
  have hprodge : √N ≤ √L * (N + 1) := by
    nlinarith [hsL1, hsN_le, mul_nonneg (sub_nonneg.mpr hsL1) hden.le]
  have h2 : a * √N ≤ a * √L * (N + 1) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hprodge hann
  nlinarith [h1, h2]

/-- **Consistency and rate for sparse targets** [YDK26, Theorem 5.2]. Under Condition **A**
only (no non-sparsity), any forced-exploration design satisfies, for every arm `k`, almost surely:
`N_{n,k} → ∞`; `N_{n,k}/n → v_k = T(θ)_k` (allowing `v_k = 0`); and
`|θ̂_{n,k} - θ_k| = O(√(log log N_{n,k} / N_{n,k}))` (the estimator LIL scaled by the arm's *own*
sample count). All three follow from `aRTSFE_no_starvation` (`N → ∞`, the sparse enabler): it forces
every arm sampled infinitely often, hence `θ̂ → θ` (`estimator_ae_tendsto_of_pullCount_atTop`, no
positivity needed), whence `ρ̂ → T(θ)` and — through the matching `consistency_of_hitting` (which
never uses positivity) — `N/n → T(θ)`; the rate is `abs_estimator_sub_le_rate_loglog_N`. The design
enters through the design predicate `IsARTSFE`: its throttle field feeds the matching, its
forced-exploration field the no-starvation. -/
theorem aRTSFE_sparse_rate_of_isARTSFE [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐]
    [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (hνk : ∀ a, MemLp id 2 (ν a))
    (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hARTSFE : IsARTSFE alg θ₀ T hsched α) (k : 𝓐) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ pullCount A k n ω) atTop atTop ∧
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ))
        atTop (𝓝 (T ν.means k)) ∧
      ∃ C', ∀ᶠ n in atTop,
        |estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k|
          ≤ C' * √(Real.log (Real.log (pullCount A k n ω : ℝ)) / (pullCount A k n ω : ℝ)) := by
  have hthrottle := fun a ↦ throttle_of_isARTSFE (A := A) (Y := Y) h hARTSFE a
  have hfe := fe_of_isARTSFE (A := A) (Y := Y) h hARTSFE
  -- No starvation for every arm (`N_{n,k'} → ∞`), in real form.
  have hNinf : ∀ᵐ ω ∂P, ∀ k', Tendsto (fun n ↦ (pullCount A k' n ω : ℝ)) atTop atTop :=
    ae_all_iff.mpr fun k' ↦ (aRTSFE_no_starvation hh.tendsto_atTop hfe k').mono
      fun ω hω ↦ tendsto_natCast_atTop_atTop.comp hω
  -- Estimator vector consistency `θ̂ → θ` from infinite pulls (no positivity).
  have hθconv : ∀ᵐ ω ∂P, Tendsto (fun n k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
      (Y · ω) (θ₀ k') n) atTop (𝓝 ν.means) := by
    have hper : ∀ k', ∀ᵐ ω ∂P, Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k' j ω)
        (Y · ω) (θ₀ k') n) atTop (𝓝 (ν.means k')) := by
      intro k'
      filter_upwards [estimator_ae_tendsto_of_pullCount_atTop h k' hνk (θ₀ k'), hNinf]
        with ω hest hNall
      exact hest (hNall k')
    filter_upwards [ae_all_iff.mpr hper] with ω hω
    exact tendsto_pi_nhds.mpr hω
  -- Plug-in target consistency `ρ̂_{n,k} → T(θ)_k` by continuity.
  have hρconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop
      (𝓝 (T ν.means k)) := by
    filter_upwards [hθconv] with ω hω
    exact tendsto_pi_nhds.mp ((hT.tendsto _).comp hω) k
  -- `N/n → T(θ)_k`: the common matching limit `u_k` equals `T(θ)_k` (uniqueness with `ρ̂ → T(θ)`).
  have hprop : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ))
      atTop (𝓝 (T ν.means k)) := by
    filter_upwards [consistency_of_hitting h hνk θ₀ T hT hTnn hTsum α hα
      (aRTSFEUnder A Y θ₀ T hsched) hthrottle (aRTSFE_smallness_all θ₀ T hTnn hh), hρconv]
      with ω hmatch hρω
    obtain ⟨u, hu⟩ := hmatch
    rw [← tendsto_nhds_unique (hu k).2 hρω]
    exact (hu k).1
  filter_upwards [aRTSFE_no_starvation hh.tendsto_atTop hfe k, hprop,
    abs_estimator_sub_le_rate_loglog_N h k (θ₀ k) (hνk k)
      (hNinf.mono fun ω hω ↦ hω k)] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-! ### A concrete admissible schedule

`h(n) = n^{2/3}` satisfies every hypothesis the sparse theory imposes, and is **excluded** by the
paper's condition (ii) `h(n) = o(√n)`. So the hypothesis stack is satisfiable, and it is satisfiable
exactly in the regime the paper's definition rules out. -/

/-- The concrete exploration schedule `h(n) = n^{2/3}`. -/
noncomputable def sched23 : ℕ → ℝ := fun n ↦ (n : ℝ) ^ ((2 : ℝ) / 3)

lemma sched23_nonneg (n : ℕ) : 0 ≤ sched23 n := Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- `n^{2/3}` is a legitimate exploration schedule in the weakened sense: nondecreasing, divergent,
and `o(n)`. -/
@[specifies IsExplorationSchedule "the predicate is non-vacuous: a concrete schedule satisfies it"]
lemma isExplorationSchedule_sched23 : IsExplorationSchedule sched23 where
  mono := fun a b hab ↦
    Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) (by norm_num)
  tendsto_atTop := (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  div_tendsto_zero := by
    have hthird : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
    refine hthird.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hnR _
    rw [sched23, div_eq_div_iff hp.ne' hnR.ne', one_mul, ← Real.rpow_add hnR,
      show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.rpow_one]

/-- **`n^{2/3}` is not `o(√n)`** — it is excluded by the paper's condition (ii), and that is exactly
what puts a sparse arm in the forced-exploration-dominated regime. -/
lemma not_isSqrtSmall_sched23 : ¬ IsSqrtSmall sched23 := by
  have hgrow : Tendsto (fun n : ℕ ↦ sched23 n / √n) atTop atTop := by
    have hsixth : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine hsixth.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hnR _
    rw [sched23, Real.sqrt_eq_rpow, eq_div_iff hp.ne', ← Real.rpow_add hnR,
      show (1 : ℝ) / 6 + 1 / 2 = 2 / 3 by norm_num]
  intro hcon
  exact not_tendsto_nhds_of_tendsto_atTop hgrow 0 hcon

/-- The **schedule-regularity** hypothesis `hshift` of `pullCount_div_sched_tendsto_one` holds for
`n^{2/3}`: shifting the argument by the `O(h n)` catch-up window changes `h` only to second order,
since `K⌈n^{2/3}⌉ + 1 = o(n)`. -/
lemma sched23_shift (K : ℕ) :
    Tendsto (fun n ↦ sched23 (n - (K * ⌈sched23 n⌉₊ + 1)) / sched23 n) atTop (𝓝 1) := by
  -- the shifted index is `n(1 - o(1))`
  have hshrink : Tendsto (fun n : ℕ ↦ ((n - (K * ⌈sched23 n⌉₊ + 1) : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ ↦ ((K : ℝ) * (sched23 n + 1) + 1) / (n : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ sched23 n / (n : ℝ)) atTop (𝓝 0) :=
        isExplorationSchedule_sched23.div_tendsto_zero
      have h2 : Tendsto (fun n : ℕ ↦ ((K : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have := (h1.const_mul (K : ℝ)).add h2
      simp only [mul_zero, add_zero] at this
      refine this.congr fun n ↦ ?_
      field_simp
      ring
    have hsq : Tendsto (fun n : ℕ ↦ 1 - ((K : ℝ) * (sched23 n + 1) + 1) / (n : ℝ))
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hz
    rw [sub_zero] at hsq
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsq tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have hceil : ((⌈sched23 n⌉₊ : ℝ)) ≤ sched23 n + 1 :=
        (Nat.ceil_lt_add_one (sched23_nonneg n)).le
      have hnum : (n : ℝ) - ((K : ℝ) * (sched23 n + 1) + 1)
          ≤ ((n - (K * ⌈sched23 n⌉₊ + 1) : ℕ) : ℝ) := by
        by_cases hle : K * ⌈sched23 n⌉₊ + 1 ≤ n
        · rw [Nat.cast_sub hle]; push_cast; nlinarith
        · have h0 : n - (K * ⌈sched23 n⌉₊ + 1) = 0 := by omega
          have hcast : (n : ℝ) ≤ (K : ℝ) * (⌈sched23 n⌉₊ : ℝ) + 1 := by
            have : n ≤ K * ⌈sched23 n⌉₊ + 1 := by omega
            exact_mod_cast this
          rw [h0, Nat.cast_zero]
          nlinarith
      calc 1 - ((K : ℝ) * (sched23 n + 1) + 1) / (n : ℝ)
          = ((n : ℝ) - ((K : ℝ) * (sched23 n + 1) + 1)) / (n : ℝ) := by field_simp
        _ ≤ ((n - (K * ⌈sched23 n⌉₊ + 1) : ℕ) : ℝ) / (n : ℝ) := by gcongr
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_one hnR]
      exact_mod_cast Nat.sub_le _ _
  -- `x ↦ x^{2/3}` is continuous at `1`, with value `1`
  have hcont : Tendsto (fun x : ℝ ↦ x ^ ((2 : ℝ) / 3)) (𝓝 1) (𝓝 1) := by
    have := (Real.continuousAt_rpow_const (1 : ℝ) ((2 : ℝ) / 3) (Or.inl one_ne_zero)).tendsto
    simpa using this
  refine (hcont.comp hshrink).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply, sched23]
  rw [← Real.div_rpow (Nat.cast_nonneg _) hnR.le]

/-- `log log n = o(n^p)` for every `p > 0`: iterating the logarithm only helps, so this follows from
`log n = o(n^p)` by `log log n ≤ log n`. It is the single growth fact behind both `sched23_sqrt` and
`sched23_star`. -/
lemma tendsto_loglog_div_rpow {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log n) / (n : ℝ) ^ p) atTop (𝓝 0) := by
  have hlogtop : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := hlogtop.eventually_ge_atTop 1
  have hcomp : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ p) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hcomp
  · filter_upwards [hev] with n hn
    have h1 : (0 : ℝ) ≤ Real.log (Real.log n) := Real.log_nonneg hn
    positivity
  · filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hppos : (0 : ℝ) < (n : ℝ) ^ p := Real.rpow_pos_of_pos hnR _
    gcongr
    exact Real.log_le_self (by linarith)

/-- The `(⋆)` comparison `√(n log log n) = o(h n)` holds for `n^{2/3}` — the `hsqrt` hypothesis of
`throttled_count_div_sched_tendsto_zero`. It reduces to `log log n = o(n^{1/3})`, since
`√(n log log n)/n^{2/3} = √(log log n / n^{1/3})`. -/
lemma sched23_sqrt (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C * √((n : ℝ) * Real.log (Real.log n)) / sched23 n)
      atTop (𝓝 0) := by
  have hlogtop : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := hlogtop.eventually_ge_atTop 1
  have hLL : Tendsto (fun n : ℕ ↦ Real.log (Real.log n) / (n : ℝ) ^ ((1 : ℝ) / 3))
      atTop (𝓝 0) := tendsto_loglog_div_rpow (by norm_num)
  have hsq : Tendsto (fun n : ℕ ↦
      √(Real.log (Real.log n) / (n : ℝ) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hLL
    simpa [Function.comp_def] using this
  have hmain : Tendsto (fun n : ℕ ↦ √((n : ℝ) * Real.log (Real.log n)) / sched23 n)
      atTop (𝓝 0) := by
    refine hsq.congr' ?_
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hL0 : (0 : ℝ) ≤ Real.log (Real.log n) := Real.log_nonneg hn
    have hnL : (0 : ℝ) ≤ (n : ℝ) * Real.log (Real.log n) := by positivity
    have h43 : (n : ℝ) ^ ((4 : ℝ) / 3) = (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add hnR, Real.rpow_one]
    have hs43 : √((n : ℝ) ^ ((4 : ℝ) / 3)) = (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnR.le]; norm_num
    simp only [sched23]
    rw [← hs43, ← Real.sqrt_div hnL]
    congr 1
    rw [h43, mul_div_mul_left _ _ hnR.ne']
  have hC := hmain.const_mul C
  rw [mul_zero] at hC
  exact hC.congr fun n ↦ (mul_div_assoc C _ _).symm

/-- **The schedule `n^{2/3}` satisfies `(⋆)`** in the form consumed by `exists_decay_of_contDiffAt`,
with `L ≍ h`: `n log log n / h(n)² = log log n / n^{1/3} → 0` since `h(n)² = n^{4/3}`.

Read together with `not_isSqrtSmall_sched23`, this is what makes the fix non-vacuous: `(⋆)` is
satisfiable *precisely* in the regime `h(n) ≫ √n` that the paper's condition (ii) excludes. -/
lemma sched23_star :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / (sched23 n * sched23 n))
      atTop (𝓝 0) := by
  refine (tendsto_loglog_div_rpow (p := (1 : ℝ) / 3) (by norm_num)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have h43 : sched23 n * sched23 n = (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 3) := by
    simp only [sched23]
    rw [← Real.rpow_add hnR, show (2 : ℝ) / 3 + 2 / 3 = 1 + 1 / 3 by norm_num,
      Real.rpow_add hnR, Real.rpow_one]
  rw [h43, mul_div_mul_left _ _ hnR.ne']

/-- **The schedule hypotheses of `aRTSFE_sparse_clt_of_contDiffAt` are jointly satisfiable** — and
satisfiable only outside condition (ii) of the paper's Definition 5.1. `h(n) = n^{2/3}` supplies all
three (`hh`, `hshift`, `hstar`) while failing `IsSqrtSmall`, so the capstone is not vacuous. -/
@[specifies sched23 "the exponent `2/3` is chosen to sit strictly between the two constraints: \
large enough that `√(m log log m) ≪ h(m)` (condition `(⋆)`), small enough that `h(m) = o(m)`. \
That it fails `IsSqrtSmall` is the point, not a defect — it witnesses that the sparse regime lies \
outside the paper's schedule condition"]
lemma sched23_satisfies_schedule_hypotheses :
    IsExplorationSchedule sched23 ∧
    (∀ K : ℕ, Tendsto (fun n ↦ sched23 (n - (K * ⌈sched23 n⌉₊ + 1)) / sched23 n) atTop (𝓝 1)) ∧
    Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (sched23 m * sched23 m))
      atTop (𝓝 0) ∧
    ¬ IsSqrtSmall sched23 :=
  ⟨isExplorationSchedule_sched23, sched23_shift, sched23_star, not_isSqrtSmall_sched23⟩

/-- **`√(n log log n) = o(h(n))` is exactly what `(⋆)` says**, in the scaled form the martingale
part of `throttled_count_div_sched_tendsto_zero` consumes: `√(n log log n)/h(n)` is the square root
of `n log log n / h(n)²`. -/
lemma tendsto_const_mul_sqrt_loglog_div_sched {hsched : ℕ → ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 0 < hsched n)
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (hsched m * hsched m))
      atTop (𝓝 0)) (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C * √((n : ℝ) * Real.log (Real.log n)) / hsched n)
      atTop (𝓝 0) := by
  have hlog1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hbase : Tendsto (fun n : ℕ ↦ √((n : ℝ) * Real.log (Real.log n)) / hsched n)
      atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ ↦
        √((n : ℝ) * Real.log (Real.log n) / (hsched n * hsched n))) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hstar
    refine hs.congr' ?_
    filter_upwards [hspos, hlog1, eventually_gt_atTop 0] with n hn hll hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnum : (0 : ℝ) ≤ (n : ℝ) * Real.log (Real.log n) :=
      mul_nonneg hnR.le (Real.log_nonneg hll)
    rw [Real.sqrt_div hnum, Real.sqrt_mul_self hn.le]
  have hC := hbase.const_mul C
  rw [mul_zero] at hC
  exact hC.congr fun n ↦ (mul_div_assoc C _ _).symm

/-- **A nonnegative sequence decaying at the loglog rate has partial sums `o(h(n))`** — under `(⋆)`
and nothing else. This is the `hsum` input of `throttled_count_div_sched_tendsto_zero`, *derived*
rather than assumed.

The point is that `(⋆)` already pins the schedule tightly enough to sum the decay. Writing `(⋆)` as
`i log log i < h(i)²`, i.e. `h(i) > √(i log log i)`, the majorant telescopes into a square root:

`log log i / h(i) ≤ log log i / √(i log log i) = √(log log i) / √i`,

so `∑_{i<n} f i ≲ √(log log n) · ∑_{i<n} 1/√i ≤ 2√(n log log n)` by `sum_one_div_sqrt_le` — and
`√(n log log n) = o(h(n))` is `(⋆)` once more. The finitely many initial terms, where the decay has
not yet started, contribute a constant, which `h(n) → ∞` kills. -/
lemma tendsto_sum_div_sched_of_loglog_decay {f : ℕ → ℝ} {hsched : ℕ → ℝ} {c : ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hsched_atTop : Tendsto hsched atTop atTop)
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (hsched m * hsched m))
      atTop (𝓝 0))
    (hdecay : ∀ᶠ i in atTop, f i ≤ c * (Real.log (Real.log i) / hsched i)) :
    Tendsto (fun n ↦ (∑ i ∈ Finset.range n, f i) / hsched n) atTop (𝓝 0) := by
  have hspos : ∀ᶠ n : ℕ in atTop, 0 < hsched n := hsched_atTop.eventually_gt_atTop 0
  have hloglog1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ Real.log (Real.log i) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  have hstar1 : ∀ᶠ i : ℕ in atTop, (i : ℝ) * Real.log (Real.log i) < hsched i * hsched i := by
    filter_upwards [hstar.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)), hspos]
      with i hi hs
    rwa [div_lt_one (by positivity)] at hi
  have hlog1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ Real.log i :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp
    (hdecay.and (hloglog1.and (hlog1.and (hstar1.and (hspos.and (eventually_gt_atTop 0))))))
  -- Pointwise: the loglog majorant is at most `|c|·√(log log i)/√i`.
  have hpt : ∀ i, i₀ ≤ i →
      f i ≤ (|c| * √(Real.log (Real.log i))) * (1 / √i) := by
    intro i hi
    obtain ⟨hdec, hll, -, hst, hs, hi0⟩ := hi₀ i hi
    have hiR : (0 : ℝ) < i := by exact_mod_cast hi0
    have hll0 : (0 : ℝ) < Real.log (Real.log i) := lt_of_lt_of_le one_pos hll
    have hspos' : (0 : ℝ) < √((i : ℝ) * Real.log (Real.log i)) :=
      Real.sqrt_pos.mpr (by positivity)
    have hsq : √((i : ℝ) * Real.log (Real.log i)) < hsched i := by
      have hlt := Real.sqrt_lt_sqrt (by positivity) hst
      rwa [Real.sqrt_mul_self hs.le] at hlt
    have heq : Real.log (Real.log i) / √((i : ℝ) * Real.log (Real.log i))
        = √(Real.log (Real.log i)) * (1 / √i) := by
      rw [Real.sqrt_mul hiR.le,
        mul_comm (√(i : ℝ)) (√(Real.log (Real.log i))),
        ← div_div, Real.div_sqrt, mul_one_div]
    have hkey : Real.log (Real.log i) / hsched i
        ≤ √(Real.log (Real.log i)) * (1 / √i) := by
      rw [← heq]
      gcongr
    calc f i ≤ c * (Real.log (Real.log i) / hsched i) := hdec
      _ ≤ |c| * (Real.log (Real.log i) / hsched i) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (div_nonneg hll0.le hs.le)
      _ ≤ |c| * (√(Real.log (Real.log i)) * (1 / √i)) :=
          mul_le_mul_of_nonneg_left hkey (abs_nonneg c)
      _ = (|c| * √(Real.log (Real.log i))) * (1 / √i) := by ring
  -- Sum the majorant.
  have hbound : ∀ n, i₀ ≤ n → ∑ i ∈ Finset.range n, f i
      ≤ (∑ i ∈ Finset.range i₀, f i)
        + |c| * 2 * √((n : ℝ) * Real.log (Real.log n)) := by
    intro n hn
    have hsplit : ∑ i ∈ Finset.range n, f i
        = (∑ i ∈ Finset.range i₀, f i) + ∑ i ∈ Finset.Ico i₀ n, f i := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive f (Nat.zero_le i₀) hn]
    rw [hsplit]
    gcongr
    have htail : ∑ i ∈ Finset.Ico i₀ n, f i
        ≤ ∑ i ∈ Finset.range n, (|c| * √(Real.log (Real.log n))) * (1 / √i) := by
      refine (Finset.sum_le_sum (fun i hi ↦ ?_)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2)
          (fun i _ _ ↦ by positivity))
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
      obtain ⟨-, -, hlogi, -, -, hi0⟩ := hi₀ i hi1
      have hiR : (0 : ℝ) < i := by exact_mod_cast hi0
      refine (hpt i hi1).trans ?_
      gcongr
    refine htail.trans ?_
    rw [← Finset.mul_sum]
    calc (|c| * √(Real.log (Real.log n))) * ∑ i ∈ Finset.range n, 1 / √i
        ≤ (|c| * √(Real.log (Real.log n))) * (2 * √n) := by
          gcongr
          exact sum_one_div_sqrt_le n
      _ = |c| * 2 * √((n : ℝ) * Real.log (Real.log n)) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n)]; ring
  -- Squeeze.
  refine squeeze_zero' ?_ ?_ (?_ : Tendsto (fun n ↦ (∑ i ∈ Finset.range i₀, f i) / hsched n
    + |c| * 2 * √((n : ℝ) * Real.log (Real.log n)) / hsched n) atTop (𝓝 0))
  · filter_upwards [hspos] with n hn
    exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hf0 i) hn.le
  · filter_upwards [eventually_ge_atTop i₀, hspos] with n hn hs
    rw [← add_div]
    gcongr
    exact hbound n hn
  · have h1 : Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range i₀, f i) / hsched n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsched_atTop
    have h2 := tendsto_const_mul_sqrt_loglog_div_sched hspos hstar (|c| * 2)
    simpa using h1.add h2

/-- **Discharging the `FEfed` hypothesis of `aRTSFE_sparse_clt`** — the final assembly of Steps 3–4.

For an arm `k` whose plug-in target has decayed past the schedule (`hdecay`: pathwise, eventually
`ρ̂_{m,k} ≤ g m < h(m)/m`, which is what `aRTSTarget_le_loglog_of_quadratic` supplies under `(⋆)`),
the counter `E n = ∑_{i<n} 𝟙{throttled pull of k at i}` has all three properties that
`pullCount_div_sched_tendsto_one` asks for:

* it is monotone;
* it increases by one at every non-forced-exploration pull of `k` — because at such a round `k` is
  not under-explored, so Step 3 (`not_aRTSFEUnder_of_sched_lt`) makes the pull a *throttled* one;
* it is `o(h)`, by Step 4 (`throttled_count_div_sched_tendsto_zero`).

Note `n₀` and `g` are allowed to depend on `ω`, which is essential: the decay constant comes
from the law of the iterated logarithm and is genuinely random. -/
lemma fEfed_of_decay [Finite 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {hsched : ℕ → ℝ} {θ₀ : 𝓐 → ℝ}
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (hTnn : ∀ z k, 0 ≤ T z k) {k : 𝓐} {α : ℝ}
    (hα : 0 ≤ α)
    (hARTSFE : IsARTSFE alg θ₀ T hsched α)
    (hsched_atTop : Tendsto hsched atTop atTop)
    (hsum : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω k) / hsched n) atTop (𝓝 0))
    (hsqrt : ∀ C : ℝ,
      Tendsto (fun n : ℕ ↦ C * √((n : ℝ) * Real.log (Real.log n)) / hsched n)
        atTop (𝓝 0))
    (hdecay : ∀ᵐ ω ∂P, ∃ g : ℕ → ℝ,
      (∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω k ≤ g m) ∧
      (∀ᶠ m in atTop, g m < hsched m / (m : ℝ))) :
    ∀ᵐ ω ∂P, ∃ (n₀ : ℕ) (E : ℕ → ℝ), Monotone E ∧
      (∀ m, n₀ ≤ m → A m ω = k → (¬ ∃ j, (pullCount A j m ω : ℝ) ≤ hsched m) →
        E m + 1 ≤ E (m + 1)) ∧
      Tendsto (fun n ↦ E n / hsched n) atTop (𝓝 0) := by
  have hX0 : ∀ i ω, 0 ≤ throttledIndicator A Y θ₀ T hsched k i ω := fun i ω ↦
    Set.indicator_nonneg (fun _ _ ↦ actionIndicator_nonneg A k i _) ω
  filter_upwards [hdecay,
    throttled_count_div_sched_tendsto_zero h hT hTnn hα hARTSFE hsched_atTop hsum hsqrt]
    with ω hdecayω hlimω
  obtain ⟨g, hg1, hg2⟩ := hdecayω
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hg1.and (hg2.and (eventually_gt_atTop 0)))
  refine ⟨n₀, fun n ↦ count (fun i ↦ throttledIndicator A Y θ₀ T hsched k i ω) n, ?_, ?_, hlimω⟩
  · intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx ↦ ?_) (fun i _ _ ↦ hX0 i ω)
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hab)
  · intro m hm hAm hnotU
    obtain ⟨hdec, hgh, hmpos⟩ := hn₀ m hm
    -- arm `k` is not under-explored at `m`, so Step 3 makes this a *throttled* pull
    have hlt : hsched m < (pullCount A k m ω : ℝ) := by
      by_contra hcon
      exact hnotU ⟨k, not_lt.mp hcon⟩
    have hnot := not_aRTSFEUnder_of_sched_lt ω hmpos hlt hdec hgh
    have hval : throttledIndicator A Y θ₀ T hsched k m ω = 1 := by
      rw [throttledIndicator, Set.indicator_of_mem hnot, actionIndicator]
      exact Set.indicator_of_mem (show ω ∈ {ω | A m ω = k} from hAm) _
    change count (fun i ↦ throttledIndicator A Y θ₀ T hsched k i ω) m + 1
      ≤ count (fun i ↦ throttledIndicator A Y θ₀ T hsched k i ω) (m + 1)
    rw [count_succ, hval]

/-- **The sparse componentwise CLT for `aRTSFE`, with the `FEfed` hypothesis discharged**
[YDK26, Corollary 5.3], under a corrected schedule condition (erratum E2 of
`notes/paper-errata.md`). This is the capstone of `maths/sparse-clt-fix.md`: `aRTSFE_sparse_clt`
assumes that each sparse arm is eventually fed only by forced exploration; here that assumption is
*proved*, from

* `hstar` — the reversed schedule condition `(⋆) : m log log m = o(h(m)²)`, which replaces the
  paper's `h(m) = o(√m)` and is satisfiable exactly where the paper's condition fails
  (`sched23_star`, `not_isSqrtSmall_sched23`);
* `hT2` — the target is `C²` at `Θ` on the sparse arms. -/
theorem aRTSFE_sparse_clt_of_contDiffAt [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐]
    [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (θ₀ : 𝓐 → ℝ)
    (hνk : ∀ a, MemLp id 2 (ν a))
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hshift : Tendsto
      (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n) atTop (𝓝 1))
    (hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * log (log m) / (hsched m * hsched m)) atTop (𝓝 0))
    {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T) (hTnn : ∀ z a, 0 ≤ T z a)
    (hTsum : ∀ z, ∑ a, T z a = 1)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (hARTSFE : IsARTSFE alg θ₀ T hsched α)
    (hT2 : ∀ a, T ν.means a = 0 → ContDiffAt ℝ 2 (T · a) ν.means) :
    TendstoInDistribution (fun n ω ↦ (WithLp.toLp 2 (fun k ↦
        √(count (actionIndicator A k · ω) n)
          * (estimator (actionIndicator A k · ω) (Y · ω) (θ₀ k) n - ν.means k))
            : EuclideanSpace ℝ 𝓐)) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (Matrix.diagonal (fun a ↦ Var[id; ν a]))) := by
  classical
  have hfe := fe_of_isARTSFE h hARTSFE
  have hthrottle := fun a ↦ throttle_of_isARTSFE h hARTSFE a
  -- Condition **A** already gives, for *every* arm, that the count diverges, that the proportion
  -- converges to `T(Θ)_a` (no positivity needed), and the `N`-scaled loglog rate.
  have hsr : ∀ᵐ ω ∂P, ∀ a : 𝓐,
      Tendsto (fun n ↦ pullCount A a n ω) atTop atTop ∧
      Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / (n : ℝ))
        atTop (𝓝 (T ν.means a)) ∧
      ∃ C' : ℝ, ∀ᶠ n in atTop,
        |estimator (fun j ↦ actionIndicator A a j ω) (Y · ω) (θ₀ a) n - ν.means a|
          ≤ C' * √(Real.log (Real.log (pullCount A a n ω : ℝ))
              / (pullCount A a n ω : ℝ)) :=
    ae_all_iff.mpr fun a ↦ aRTSFE_sparse_rate_of_isARTSFE h hνk θ₀ T hT hTnn hTsum α hα
      hh hARTSFE a
  have hprop : ∀ᵐ ω ∂P, ∀ a : 𝓐, T ν.means a ≠ 0 →
      Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / (n : ℝ)) atTop
        (𝓝 (T ν.means a)) := by
    filter_upwards [hsr] with ω hω a _
    exact (hω a).2.1
  refine aRTSFE_sparse_clt (v := fun a ↦ T ν.means a) h θ₀ hνk hh hshift
    (fun a ↦ T ν.means a = 0)
    (fun a ha ↦ lt_of_le_of_ne (hTnn _ a) (Ne.symm ha)) hfe ?_ hprop
  -- The deterministic floor `L(n) = h(n - W(n))` that forced exploration guarantees.
  set L : ℕ → ℝ := fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) with hLdef
  have hspos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < hsched n := hh.tendsto_atTop.eventually_gt_atTop 0
  -- `L ≍ h`: eventually `L ≥ h/2`, so `L → ∞`, and `h/L → 1`.
  have hhalf : ∀ᶠ n : ℕ in atTop, hsched n / 2 ≤ L n := by
    filter_upwards [hshift.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1)), hspos]
      with n hn hs
    rw [lt_div_iff₀ hs] at hn
    linarith
  have hLtop : Tendsto L atTop atTop :=
    tendsto_atTop_mono' atTop hhalf (hh.tendsto_atTop.atTop_div_const (by norm_num))
  have hLpos : ∀ᶠ m : ℕ in atTop, 0 < L m ∧ 0 < hsched m := by
    filter_upwards [hLtop.eventually_gt_atTop 0, hspos] with m h1 h2 using ⟨h1, h2⟩
  have hinv : Tendsto (fun n : ℕ ↦ hsched n / L n) atTop (𝓝 1) := by
    have hi := hshift.inv₀ (by norm_num)
    rw [inv_one] at hi
    exact hi.congr fun n ↦ inv_div _ _
  -- `(⋆)` transported from `h²` to `L·h`, and the resulting `log log m / L m → 0`.
  have hstarL : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.log (Real.log m) / (L m * hsched m))
      atTop (𝓝 0) := by
    have hmul := hstar.mul hinv
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [hLpos] with m hm
    have hL' := hm.1.ne'
    have hs' := hm.2.ne'
    field_simp
  have hL0 : Tendsto (fun m : ℕ ↦ Real.log (Real.log m) / L m) atTop (𝓝 0) := by
    have hmul := hstarL.mul hh.div_tendsto_zero
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [hLpos, eventually_gt_atTop 0] with m hm hm0
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    have hL' := hm.1.ne'
    have hs' := hm.2.ne'
    field_simp
  have hlog1 : ∀ᶠ m : ℕ in atTop, (1 : ℝ) ≤ Real.log m :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hLnn : ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log (Real.log m) / L m := by
    filter_upwards [hlog1, hLpos] with m hm hLm
    exact div_nonneg (Real.log_nonneg hm) hLm.1.le
  -- `(⋆)` also gives the martingale-part majorant `√(n log log n) = o(h(n))`.
  have hsqrt : ∀ C : ℝ, Tendsto
      (fun n : ℕ ↦ C * √((n : ℝ) * Real.log (Real.log n)) / hsched n) atTop (𝓝 0) :=
    tendsto_const_mul_sqrt_loglog_div_sched hspos hstar
  -- The LIL rate re-expressed against the deterministic floor.
  have hrate_ae : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ j, ∀ᶠ m in atTop,
      |estimator (fun i ↦ actionIndicator A j i ω) (Y · ω) (θ₀ j) m - ν.means j|
        ≤ C * √(Real.log (Real.log m) / L m) := by
    filter_upwards [hfe, hsr] with ω hfeω hsrω
    exact exists_rate_loglog_of_pullCount_ge ω hLtop
      (fun j ↦ eventually_schedShift_le_pullCount ω hh hfeω j) (fun a ↦ (hsrω a).2.2)
  -- Arm by arm: decay ⇒ `FEfed`.
  refine ae_all_iff.mpr fun a ↦ ?_
  by_cases hfed : T ν.means a = 0
  · -- The loglog decay of `ρ̂_{·,a}`, in the explicit form that both inputs of `fEfed_of_decay`
    -- are read off from.
    have hCq_ae : ∀ᵐ ω ∂P, ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ᶠ m in atTop,
        aRTSTarget A Y θ₀ T m ω a ≤ Cq * (Real.log (Real.log m) / L m) := by
      filter_upwards [hrate_ae] with ω hω
      obtain ⟨C, hC⟩ := hω
      exact exists_aRTSTarget_le_loglog_of_contDiffAt ω (hT2 a hfed) (hTnn · a) hfed
        hLnn hL0 hC
    have hdecay : ∀ᵐ ω ∂P, ∃ g : ℕ → ℝ,
        (∀ᶠ m in atTop, aRTSTarget A Y θ₀ T m ω a ≤ g m) ∧
        (∀ᶠ m in atTop, g m < hsched m / (m : ℝ)) := by
      filter_upwards [hCq_ae] with ω hω
      obtain ⟨Cq, -, hCq⟩ := hω
      exact ⟨fun m ↦ Cq * (Real.log (Real.log m) / L m), hCq,
        eventually_mul_loglog_div_lt_of_star Cq hLpos hstarL⟩
    -- The compensator bound is the *same* decay, summed: `(⋆)` makes `∑ α ρ̂_{i,a} = o(h(n))`.
    have hsum : ∀ᵐ ω ∂P, Tendsto
        (fun n ↦ (∑ i ∈ Finset.range n, α * aRTSTarget A Y θ₀ T i ω a) / hsched n)
        atTop (𝓝 0) := by
      filter_upwards [hCq_ae] with ω hω
      obtain ⟨Cq, hCq0, hCq⟩ := hω
      refine tendsto_sum_div_sched_of_loglog_decay (c := α * (2 * Cq))
        (fun i ↦ mul_nonneg hα.1 (hTnn _ a)) hh.tendsto_atTop hstar ?_
      filter_upwards [hCq, hhalf, hLpos, hlog1] with i hi hhalfi hLposi hlogi
      have hllnn : (0 : ℝ) ≤ Real.log (Real.log i) := Real.log_nonneg hlogi
      have hstep : Real.log (Real.log i) / L i ≤ 2 * (Real.log (Real.log i) / hsched i) := by
        have hhalf0 : (0 : ℝ) < hsched i / 2 := by linarith [hLposi.2]
        have hmono : Real.log (Real.log i) / L i
            ≤ Real.log (Real.log i) / (hsched i / 2) := by gcongr
        refine hmono.trans_eq ?_
        field_simp
      calc α * aRTSTarget A Y θ₀ T i ω a
          ≤ α * (Cq * (Real.log (Real.log i) / L i)) := mul_le_mul_of_nonneg_left hi hα.1
        _ ≤ α * (Cq * (2 * (Real.log (Real.log i) / hsched i))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hCq0) hα.1
        _ = α * (2 * Cq) * (Real.log (Real.log i) / hsched i) := by ring
    filter_upwards [fEfed_of_decay (k := a) h hT hTnn hα.1 hARTSFE hh.tendsto_atTop hsum hsqrt
      hdecay] with ω hω _
    exact hω
  · exact ae_of_all _ fun ω hcon ↦ absurd hcon hfed

end AlphaRAR
