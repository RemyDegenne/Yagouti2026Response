/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import AlphaRAR.ForLMLExplore.Probability.HartmanWintnerTruncation

/-!
# The i.i.d. Hartman–Wintner law of the iterated logarithm

This file develops the finite-variance (i.i.d.) case of the loglog LIL (Hartman–Wintner 1941).
A sum of i.i.d. centred increments with only a second moment is split into three levels — low
`|Y|≤b_i`, medium `b_i<|Y|≤√i`, high `|Y|>√i` — with the `log`-level cutoff `b_i = √(i/log(i+2))`.
The main (low) part satisfies the growing-increment hypothesis of `LIL.lean` and gets the
loglog rate; the high part vanishes eventually; the drift and medium parts are `o(√(n log log n))`.
The ingredients of the three parts are in `HartmanWintnerTruncation.lean`.

## Main results

* `AlphaRAR.logCutoff`: the log-level cutoff `b_j = √(j/log(j+2))`.
* `AlphaRAR.sum_integral_truncation_add_mediumTrunc_le`: the deterministic drift bound
  `∑_{j<m}(E Y_j^L + E Y_j^M) ≤ 2σ²√m + E|Y_0|`.
* `AlphaRAR.iid_hartmanWintner_limsup_le_one`: the upper half of the Hartman–Wintner LIL, a.s.
  `limsup_m (∑_{j<m} Y_j) / √(2σ² m log log m) ≤ 1` for i.i.d. centred `L²` increments with
  `σ² = E[Y_0²] > 0` (eventual, coboundedness-free form:
  `AlphaRAR.ae_forall_one_lt_eventually_sum_le_sqrt_nat_mul_loglog`).
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Real

open scoped Topology ENNReal NNReal

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The log-level Hartman–Wintner low cutoff `b_j = √(j/log(j+2))`. -/
noncomputable def logCutoff (j : ℕ) : ℝ := √((j : ℝ) / log ((j : ℝ) + 2))

/-- `x/log(x+2) < (x+1)/log(x+3)` for `x ≥ 0`: `x ↦ x/log(x+2)` is strictly increasing. -/
lemma div_log_add_two_lt {x : ℝ} (hx : 0 ≤ x) : x / log (x + 2) < (x + 1) / log (x + 3) := by
  have hlog2 : (0 : ℝ) < log (x + 2) := log_pos (by linarith)
  have hlog3 : (0 : ℝ) < log (x + 3) := log_pos (by linarith)
  rw [div_lt_div_iff₀ hlog2 hlog3]
  have hkey : log (x + 3) - log (x + 2) ≤ 1 / (x + 2) := by
    rw [← log_div (show (0 : ℝ) < x + 3 by linarith).ne' (show (0 : ℝ) < x + 2 by linarith).ne',
      show (x + 3) / (x + 2) = 1 + 1 / (x + 2) by field_simp; ring]
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (x + 2) by positivity)
    linarith
  have hfrac : x / (x + 2) < log (x + 2) := by
    have h1 : (1 : ℝ) - 1 / (x + 2) < log (x + 2) := by
      have h := log_lt_sub_one_of_pos (show (0 : ℝ) < (x + 2)⁻¹ by positivity)
        (by intro h; have := inv_eq_one.mp h; linarith)
      rw [log_inv, inv_eq_one_div] at h; linarith
    have h2 : x / (x + 2) < 1 - 1 / (x + 2) := by
      rw [show (1 : ℝ) - 1 / (x + 2) = (x + 1) / (x + 2) by field_simp; ring,
        div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  have hm : x * (log (x + 3) - log (x + 2)) ≤ x / (x + 2) := by
    have := mul_le_mul_of_nonneg_left hkey hx; rwa [mul_one_div] at this
  nlinarith [hm, hfrac]

lemma strictMono_nat_div_log_add_two :
    StrictMono (fun i : ℕ ↦ (i : ℝ) / log ((i : ℝ) + 2)) := by
  refine strictMono_nat_of_lt_succ (fun i ↦ ?_)
  have h := div_log_add_two_lt (show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i)
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (i : ℝ) + 1 + 2 = (i : ℝ) + 3 by ring]
  exact h

/-- The log-level cutoff `b_j = √(j/log(j+2))` is strictly monotone. -/
lemma strictMono_logCutoff : StrictMono logCutoff := by
  intro i j hij
  simp only [logCutoff]
  refine Real.sqrt_lt_sqrt ?_ (strictMono_nat_div_log_add_two hij)
  exact div_nonneg (Nat.cast_nonneg i)
    (log_pos (by have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith)).le

lemma logCutoff_nonneg (j : ℕ) : 0 ≤ logCutoff j := Real.sqrt_nonneg _

lemma monotone_logCutoff : Monotone logCutoff := strictMono_logCutoff.monotone

/-- `j ↦ -b_j` is injective (the singletons `{-b_j}` are pairwise distinct). -/
lemma injective_neg_logCutoff : Function.Injective (fun j : ℕ ↦ -logCutoff j) :=
  neg_injective.comp strictMono_logCutoff.injective

/-- **Pointwise upper decomposition.** With `0 ≤ bj ≤ sj`, every real `x` is bounded above by the
sum of its low `(-bj,bj]`-truncation, its medium `{bj<|·|≤sj}`-part, and its high `{sj<|·|}`-part.
Equality holds except at `x = -bj` (where the LHS `-bj ≤ 0 =` RHS): the half-open low truncation and
the strict medium lower bound leave `-bj` uncovered, but the inequality still holds since `-bj ≤ 0`.
This is what lets the boundary atom be dropped when proving the Hartman–Wintner upper bound. -/
lemma le_lowMedHigh {bj sj x : ℝ} (hb : 0 ≤ bj) (hbs : bj ≤ sj) :
    x ≤ (Set.Ioc (-bj) bj).indicator id x
      + ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x
      + ({y : ℝ | sj < |y|}).indicator id x := by
  by_cases hR : sj < |x|
  · have e1 : (Set.Ioc (-bj) bj).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
      have : |x| ≤ bj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
    have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; rintro ⟨_, hxs⟩; linarith
    have e3 : ({y : ℝ | sj < |y|}).indicator id x = x :=
      Set.indicator_of_mem (by rw [Set.mem_ofPred_eq]; exact hR) id
    rw [e1, e2, e3]; simp
  · rw [not_lt] at hR
    by_cases hM : bj < |x|
    · have e1 : (Set.Ioc (-bj) bj).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
        have : |x| ≤ bj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
      have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = x :=
        Set.indicator_of_mem (by rw [Set.mem_ofPred_eq]; exact ⟨hM, hR⟩) id
      have e3 : ({y : ℝ | sj < |y|}).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; exact not_lt.mpr hR
      rw [e1, e2, e3]; simp
    · rw [not_lt] at hM
      have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; rintro ⟨h, _⟩; linarith
      have e3 : ({y : ℝ | sj < |y|}).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; intro h; linarith
      rw [e2, e3, add_zero, add_zero]
      by_cases hIoc : x ∈ Set.Ioc (-bj) bj
      · rw [Set.indicator_of_mem hIoc]; exact le_rfl
      · rw [Set.indicator_of_notMem hIoc]
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hIoc
        have hxabs := abs_le.mp hM
        rcases hIoc with h | h
        · exact h.trans (neg_nonpos.mpr hb)
        · linarith [hxabs.2]

/-- **Pointwise low+medium bound.** With `0 ≤ bj ≤ sj`, the low `(-bj,bj]`-truncation plus the
medium `{bj<|·|≤sj}`-part is at most the `(-sj,sj]`-truncation plus a boundary atom `bj` at `x=-bj`.
Integrating gives the Hartman–Wintner drift bound
`∫trunc(Y,b_j) + ∫Y^M ≤ ∫trunc(Y,√j) + b_j μ{Y=-b_j}`. -/
lemma lowMed_le {bj sj x : ℝ} (hb : 0 ≤ bj) (hbs : bj ≤ sj) :
    (Set.Ioc (-bj) bj).indicator id x + ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x
      ≤ (Set.Ioc (-sj) sj).indicator id x + (if x = -bj then bj else 0) := by
  by_cases hR : sj < |x|
  · have e1 : (Set.Ioc (-bj) bj).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
      have : |x| ≤ bj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
    have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; rintro ⟨_, hxs⟩; linarith
    have e3 : (Set.Ioc (-sj) sj).indicator id x = 0 := by
      apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
      have : |x| ≤ sj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
    have e4 : (if x = -bj then bj else 0) = 0 := by
      rw [ite_eq_right]; intro h; rw [h, abs_neg, abs_of_nonneg hb] at hR; linarith
    rw [e1, e2, e3, e4]
  · rw [not_lt] at hR
    by_cases hM : bj < |x|
    · have e1 : (Set.Ioc (-bj) bj).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_Ioc]; rintro ⟨hxa, hxb⟩
        have : |x| ≤ bj := abs_le.mpr ⟨by linarith, hxb⟩; linarith
      have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = x :=
        Set.indicator_of_mem (by rw [Set.mem_ofPred_eq]; exact ⟨hM, hR⟩) id
      have e4 : (if x = -bj then bj else 0) = 0 := by
        rw [ite_eq_right]; intro h; rw [h, abs_neg, abs_of_nonneg hb] at hM; linarith
      rw [e1, e2, e4, zero_add, add_zero]
      by_cases hmem : x ∈ Set.Ioc (-sj) sj
      · rw [Set.indicator_of_mem hmem]; exact le_rfl
      · rw [Set.indicator_of_notMem hmem]
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hmem
        rcases hmem with h | h
        · linarith [hb, hbs]
        · linarith [le_abs_self x]
    · rw [not_lt] at hM
      have e2 : ({y : ℝ | bj < |y| ∧ |y| ≤ sj}).indicator id x = 0 := by
        apply Set.indicator_of_notMem; rw [Set.mem_ofPred_eq]; rintro ⟨h, _⟩; linarith
      rw [e2, add_zero]
      by_cases hbmem : x ∈ Set.Ioc (-bj) bj
      · rw [Set.indicator_of_mem hbmem]
        have hxmem : x ∈ Set.Ioc (-sj) sj := by
          rw [Set.mem_Ioc] at hbmem ⊢
          exact ⟨by linarith [hbmem.1], by linarith [hbmem.2]⟩
        rw [Set.indicator_of_mem hxmem]
        have hatomnn : (0 : ℝ) ≤ (if x = -bj then bj else 0) := by split_ifs; exacts [hb, le_rfl]
        simp only [id_eq]; linarith
      · rw [Set.indicator_of_notMem hbmem]
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hbmem
        have hxabs := abs_le.mp hM
        have hxeq : x = -bj := by
          rcases hbmem with h | h
          · linarith [hxabs.1]
          · linarith [hxabs.2]
        rw [ite_eq_left hxeq]
        by_cases hmem : x ∈ Set.Ioc (-sj) sj
        · rw [Set.indicator_of_mem hmem, hxeq]; simp
        · rw [Set.indicator_of_notMem hmem]; simpa using hb

/-- **Atom-sum bound.** For identically distributed `Y` with `E|Y_0| < ∞`, the boundary atoms at
`-b_j` (`b_j = √(j/log(j+2))`) contribute a uniformly bounded total:
`∑_{j<m} b_j · μ{Y_j = -b_j} ≤ E|Y_0|`. Since `b_j` are distinct (`injective_neg_logCutoff`), the
events `{Y_0 = -b_j}` are disjoint, and on `{Y_0 = -b_j}` we have `|Y_0| = b_j`, so
`b_j μ{Y_0=-b_j} = ∫_{Y_0=-b_j}|Y_0|` and the disjoint sum is `≤ ∫|Y_0|`. This lets the boundary
term be absorbed into the (deterministic) Hartman–Wintner drift. -/
lemma sum_atom_le {Y : ℕ → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hint : Integrable (fun ω ↦ |Y 0 ω|) μ) (m : ℕ) :
    ∑ j ∈ Finset.range m, logCutoff j * (μ {ω | Y j ω = -logCutoff j}).toReal
      ≤ ∫ ω, |Y 0 ω| ∂μ := by
  set A : ℕ → Set Ω := fun j ↦ Y 0 ⁻¹' {-logCutoff j} with hAdef
  have hAmeas : ∀ j, MeasurableSet (A j) := fun j ↦ hY 0 (measurableSet_singleton _)
  have hmeas_eq : ∀ j, (μ {ω | Y j ω = -logCutoff j}).toReal = (μ (A j)).toReal := by
    intro j; congr 1
    rw [show {ω | Y j ω = -logCutoff j} = Y j ⁻¹' {-logCutoff j} by ext ω; simp,
      (hident j).measure_mem_eq (measurableSet_singleton (-logCutoff j))]
  have hdisj : Pairwise fun i j ↦ Disjoint (A i) (A j) := by
    intro i j hij
    refine Set.disjoint_left.mpr (fun ω hωi hωj ↦ hij ?_)
    simp only [hAdef, Set.mem_preimage, Set.mem_singleton_iff] at hωi hωj
    exact injective_neg_logCutoff (by rw [← hωi, ← hωj] : -logCutoff i = -logCutoff j)
  have hInt : IntegrableOn (fun ω ↦ |Y 0 ω|) (⋃ j, A j) μ := hint.integrableOn
  have hsum := hasSum_integral_iUnion hAmeas hdisj hInt
  have hterm : ∀ j, ∫ ω in A j, |Y 0 ω| ∂μ = logCutoff j * (μ (A j)).toReal := by
    intro j
    have heqon : Set.EqOn (fun ω ↦ |Y 0 ω|) (fun _ ↦ logCutoff j) (A j) := by
      intro ω hω
      simp only [hAdef, Set.mem_preimage, Set.mem_singleton_iff] at hω
      simp only [hω, abs_neg]
      exact abs_of_nonneg (logCutoff_nonneg j)
    rw [setIntegral_congr_fun (hAmeas j) heqon, setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  have hnn : ∀ j, 0 ≤ ∫ ω in A j, |Y 0 ω| ∂μ := fun j ↦ by
    rw [hterm]; exact mul_nonneg (logCutoff_nonneg j) ENNReal.toReal_nonneg
  calc ∑ j ∈ Finset.range m, logCutoff j * (μ {ω | Y j ω = -logCutoff j}).toReal
      = ∑ j ∈ Finset.range m, ∫ ω in A j, |Y 0 ω| ∂μ :=
        Finset.sum_congr rfl (fun j _ ↦ by rw [hmeas_eq j, hterm j])
    _ ≤ ∑' j, ∫ ω in A j, |Y 0 ω| ∂μ := hsum.summable.sum_le_tsum _ (fun j _ ↦ hnn j)
    _ = ∫ ω in ⋃ j, A j, |Y 0 ω| ∂μ := hsum.tsum_eq
    _ ≤ ∫ ω, |Y 0 ω| ∂μ :=
        setIntegral_le_integral hint (Eventually.of_forall (fun ω ↦ abs_nonneg _))

/-- `1 ≤ log(j+2)` for `j ≥ 1` (since `j+2 ≥ 3 > e`). -/
lemma one_le_log_add_two {j : ℕ} (hj : 1 ≤ j) : (1 : ℝ) ≤ log ((j : ℝ) + 2) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  exact one_lt_log_three.le.trans (Real.log_le_log (by norm_num) (by linarith))

/-- **Condition (H) for the log-level cutoff.** `b_n √(loglog n / n) → 0`, since
`b_n √(loglog n/n) = √(loglog n / log(n+2)) → 0` as `loglog n ≪ log(n+2)`. -/
lemma tendsto_logCutoff_mul_sqrt_loglog_div :
    Tendsto (fun n : ℕ ↦ logCutoff n * √(log (log n) / n)) atTop (𝓝 0) := by
  simp only [logCutoff]
  have hlogdiv : Tendsto (fun x : ℝ ↦ log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hg2 : Tendsto (fun n : ℕ ↦ log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hub0 : Tendsto (fun n : ℕ ↦ log (log ((n : ℝ) + 2)) / log ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlogdiv.comp hg2
  have hubsqrt : Tendsto (fun n : ℕ ↦ √(log (log ((n : ℝ) + 2)) / log ((n : ℝ) + 2)))
      atTop (𝓝 0) := by
    have hcont : Tendsto (fun t : ℝ ↦ √t) (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    simpa [Function.comp_def] using hcont.comp hub0
  refine squeeze_zero' ?_ ?_ hubsqrt
  · filter_upwards [eventually_ge_atTop 3] with n _hn; positivity
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : 1 < log (n : ℝ) :=
      one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hn3)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn2pos : (0 : ℝ) < log ((n : ℝ) + 2) := log_pos (by linarith)
    have hprod : √((n : ℝ) / log ((n : ℝ) + 2)) * √(log (log n) / n)
        = √(log (log n) / log ((n : ℝ) + 2)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    rw [hprod]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff_of_pos_right hlogn2pos]
    exact loglog_le_loglog hn3 (by linarith)

/-- `b_j ≤ √j`: the low cutoff is below the high cutoff. -/
lemma logCutoff_le_sqrt (j : ℕ) : logCutoff j ≤ √(j : ℝ) := by
  rw [logCutoff]
  refine Real.sqrt_le_sqrt ?_
  rcases Nat.eq_zero_or_pos j with hj | hj
  · simp [hj]
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hlog := one_le_log_add_two hj
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log ((j : ℝ) + 2))]
    nlinarith

-- === ratio helpers ===
lemma tendsto_loglog_atTop : Tendsto (fun m : ℕ ↦ log (log (m : ℝ))) atTop atTop := by
  simpa [Function.comp_def] using
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma tendsto_sqrt_mul_loglog_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ ↦ √(2 * c * (m : ℝ) * log (log (m : ℝ)))) atTop atTop := by
  have hmL : Tendsto (fun m : ℕ ↦ (m : ℝ) * log (log (m : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ tendsto_loglog_atTop
  have h : Tendsto (fun m : ℕ ↦ 2 * c * (m : ℝ) * log (log (m : ℝ))) atTop atTop := by
    have h2c := Tendsto.const_mul_atTop (r := 2 * c) (by positivity) hmL
    exact h2c.congr fun m => by ring
  simpa [Function.comp_def] using Real.tendsto_sqrt_atTop.comp h

lemma tendsto_sqrt_div_sqrt_mul_loglog {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ ↦ √(m : ℝ) / √(2 * c * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
  have hLL : Tendsto (fun m : ℕ ↦ 2 * c * log (log (m : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop (r := 2 * c) (by positivity) tendsto_loglog_atTop
  have hsqrt : Tendsto (fun m : ℕ ↦ √(2 * c * log (log (m : ℝ)))) atTop atTop := by
    simpa [Function.comp_def] using Real.tendsto_sqrt_atTop.comp hLL
  have hinv : Tendsto (fun m : ℕ ↦ (√(2 * c * log (log (m : ℝ))))⁻¹) atTop (𝓝 0) :=
    hsqrt.inv_tendsto_atTop
  have key : ∀ᶠ m : ℕ in atTop,
      √(m : ℝ) / √(2 * c * (m : ℝ) * log (log (m : ℝ)))
        = (√(2 * c * log (log (m : ℝ))))⁻¹ := by
    filter_upwards [eventually_ge_atTop 3] with m hm
    have h3m : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hLpos : 0 < log (log (m : ℝ)) := loglog_pos_of_three_le h3m
    have hcoef : 0 ≤ 2 * c * log (log (m : ℝ)) := mul_nonneg (by positivity) hLpos.le
    have hmne : √(m : ℝ) ≠ 0 := by rw [Real.sqrt_ne_zero']; linarith
    have harg : 2 * c * log (log (m : ℝ)) * (m : ℝ)
        = 2 * c * (m : ℝ) * log (log (m : ℝ)) := by ring
    rw [← harg, Real.sqrt_mul hcoef, mul_comm (√(2 * c * log (log (m : ℝ)))) (√(m : ℝ)),
      ← div_div, div_self hmne, one_div]
  exact hinv.congr' (key.mono fun m h => h.symm)

lemma sqrt_add_three_mul_loglog_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      √(2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3)))
        ≤ (2 / √c) * √(2 * c * (m : ℝ) * log (log (m : ℝ))) := by
  filter_upwards [eventually_ge_atTop 21] with m hm
  have h21m : (21 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hexp3 : exp 3 < 21 := by
    have hb : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hb]
    calc exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 3
      _ < 21 := by norm_num
  have hlog3m : (3 : ℝ) ≤ log (m : ℝ) := by
    rw [← Real.log_exp 3]; exact Real.log_le_log (exp_pos 3) (by linarith)
  have hlogm_pos : 0 < log (m : ℝ) := by linarith
  have hlogm3_pos : 0 < log ((m : ℝ) + 3) := Real.log_pos (by linarith)
  have hcube : (m : ℝ) + 3 ≤ (m : ℝ) ^ 3 := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) - 21 := by linarith
    nlinarith [h0, mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
  have hlog_le : log ((m : ℝ) + 3) ≤ 3 * log (m : ℝ) := by
    have h := Real.log_le_log (by positivity) hcube
    rw [Real.log_pow] at h; push_cast at h; linarith
  have hLm3_le : log (log ((m : ℝ) + 3)) ≤ log 3 + log (log (m : ℝ)) := by
    have h := Real.log_le_log hlogm3_pos hlog_le
    rwa [Real.log_mul (by norm_num) (ne_of_gt hlogm_pos)] at h
  have hlog3_le_Lm : log 3 ≤ log (log (m : ℝ)) := Real.log_le_log (by norm_num) hlog3m
  have hb : log (log ((m : ℝ) + 3)) ≤ 2 * log (log (m : ℝ)) := by linarith
  have hLm_nonneg : 0 ≤ log (log (m : ℝ)) := Real.log_nonneg (by linarith)
  have hlogm_le_m3 : log (m : ℝ) ≤ log ((m : ℝ) + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hLm3_nonneg : 0 ≤ log (log ((m : ℝ) + 3)) := Real.log_nonneg (by linarith)
  have ha : (m : ℝ) + 3 ≤ 2 * (m : ℝ) := by linarith
  have hstep : ((m : ℝ) + 3) * log (log ((m : ℝ) + 3))
      ≤ 4 * (m : ℝ) * log (log (m : ℝ)) := by
    have hmul := mul_le_mul ha hb hLm3_nonneg (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ))
    nlinarith [hmul]
  have hcoef4 : (0 : ℝ) ≤ 4 / c := by positivity
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hRHS : (2 / √c) * √(2 * c * (m : ℝ) * log (log (m : ℝ)))
      = √((4 / c) * (2 * c * (m : ℝ) * log (log (m : ℝ)))) := by
    rw [Real.sqrt_mul hcoef4, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4) c, hsqrt4]
  have hinner : 2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3))
      ≤ (4 / c) * (2 * c * (m : ℝ) * log (log (m : ℝ))) := by
    have hcc : (4 / c) * (2 * c * (m : ℝ) * log (log (m : ℝ)))
        = 8 * (m : ℝ) * log (log (m : ℝ)) := by field_simp; ring
    rw [hcc]; nlinarith [hstep]
  rw [hRHS]; exact Real.sqrt_le_sqrt hinner

/-- **Deterministic Hartman–Wintner drift bound.** `Drift_m = ∑_{j<m}(𝔼 Y_j^L + 𝔼 Y_j^M)
≤ 2σ²√m + 𝔼|Y_0|`: the low+medium truncated means, combined, are the `√j`-truncated mean up to the
boundary atom, bounded by the deterministic drift `2σ²√m` (`abs_sum_integral_truncation_le`) plus
the atom total `𝔼|Y_0|` (`sum_atom_le`). -/
lemma sum_integral_truncation_add_mediumTrunc_le [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i))
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ) (hint2 : MemLp (Y 0) 2 μ)
    (hcent : ∫ ω, Y 0 ω ∂μ = 0) (m : ℕ) :
    ∑ j ∈ Finset.range m,
        (∫ x, truncation (Y j) (logCutoff j) x ∂μ + ∫ x, mediumTrunc j (Y j x) ∂μ)
      ≤ 2 * (∫ x, Y 0 x ^ 2 ∂μ) * √(m : ℝ) + ∫ x, |Y 0 x| ∂μ := by
  have hmeasset : ∀ j, MeasurableSet {ω | Y j ω = -logCutoff j} := fun j ↦
    (hY j).measurable (measurableSet_singleton _)
  have hcj_ej : ∀ j, ∫ x, truncation (Y j) (logCutoff j) x ∂μ + ∫ x, mediumTrunc j (Y j x) ∂μ
      ≤ (∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ)
        + logCutoff j * (μ {ω | Y j ω = -logCutoff j}).toReal := by
    intro j
    have hint_low : Integrable (fun ω ↦ truncation (Y j) (logCutoff j) ω) μ :=
      (hY j).aestronglyMeasurable.integrable_truncation
    have hint_med : Integrable (fun ω ↦ mediumTrunc j (Y j ω)) μ :=
      (memLp_two_mediumTrunc hY j).integrable one_le_two
    have hint_hi : Integrable (fun ω ↦ truncation (Y j) (√(j : ℝ)) ω) μ :=
      (hY j).aestronglyMeasurable.integrable_truncation
    have hint_atom : Integrable
        (fun ω ↦ ({ω | Y j ω = -logCutoff j}).indicator (fun _ ↦ logCutoff j) ω) μ :=
      (integrable_const (logCutoff j)).indicator (hmeasset j)
    rw [← integral_add hint_low hint_med]
    have hptw : ∀ ω, truncation (Y j) (logCutoff j) ω + mediumTrunc j (Y j ω)
        ≤ truncation (Y j) (√(j : ℝ)) ω
          + ({ω | Y j ω = -logCutoff j}).indicator (fun _ ↦ logCutoff j) ω := fun ω ↦
      lowMed_le (logCutoff_nonneg j) (logCutoff_le_sqrt j)
    calc ∫ ω, (truncation (Y j) (logCutoff j) ω + mediumTrunc j (Y j ω)) ∂μ
        ≤ ∫ ω, (truncation (Y j) (√(j : ℝ)) ω
            + ({ω | Y j ω = -logCutoff j}).indicator (fun _ ↦ logCutoff j) ω) ∂μ :=
          integral_mono (hint_low.add hint_med) (hint_hi.add hint_atom) hptw
      _ = (∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ)
          + logCutoff j * (μ {ω | Y j ω = -logCutoff j}).toReal := by
        rw [integral_add hint_hi hint_atom, integral_indicator_const _ (hmeasset j),
          smul_eq_mul, mul_comm, measureReal_def]
  calc ∑ j ∈ Finset.range m,
        (∫ x, truncation (Y j) (logCutoff j) x ∂μ + ∫ x, mediumTrunc j (Y j x) ∂μ)
      ≤ ∑ j ∈ Finset.range m, ((∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ)
          + logCutoff j * (μ {ω | Y j ω = -logCutoff j}).toReal) :=
        Finset.sum_le_sum (fun j _ ↦ hcj_ej j)
    _ = (∑ j ∈ Finset.range m, ∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ)
        + ∑ j ∈ Finset.range m, logCutoff j * (μ {ω | Y j ω = -logCutoff j}).toReal :=
        Finset.sum_add_distrib
    _ ≤ 2 * (∫ x, Y 0 x ^ 2 ∂μ) * √(m : ℝ) + ∫ x, |Y 0 x| ∂μ := by
        refine add_le_add ?_ (sum_atom_le (fun i ↦ (hY i).measurable) hident
          (hint2.integrable one_le_two).abs m)
        have heq : ∑ j ∈ Finset.range m, ∫ x, truncation (Y j) (√(j : ℝ)) x ∂μ
            = ∑ j ∈ Finset.range m, ∫ x, truncation (Y 0) (√(j : ℝ)) x ∂μ :=
          Finset.sum_congr rfl fun j _ ↦
            ((hident j).comp (measurable_id.indicator measurableSet_Ioc)).integral_eq
        rw [heq]
        exact (le_abs_self _).trans (abs_sum_integral_truncation_le hint2 hcent m)

/-- **Hartman–Wintner upper bound, eventually form** (coboundedness-free core). For an i.i.d.,
centred, `L²` sequence, a.s. `∀ β>1`, eventually
`S_m = ∑_{j<m} Y_j ≤ β √(2σ² m log log m)` with `σ² = 𝔼[Y_0²]`. Combining the sharp low part
(`limsup ≤ 1`), the medium `o(√(m L(m)))`, the eventually-vanishing high part and the deterministic
drift.

No positivity of `σ²` is needed: if `σ² = 0` then every `Y_j` vanishes a.s. and both sides are `0`.
(The *limsup* form `iid_hartmanWintner_limsup_le_one` does need `σ² > 0`, since it divides by
`√(2σ² m log log m)`.) -/
lemma ae_forall_one_lt_eventually_sum_le_sqrt_nat_mul_loglog [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} (hY : ∀ i, StronglyMeasurable (Y i))
    (hindep : iIndepFun Y μ) (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hint2 : MemLp (Y 0) 2 μ) (hcent : ∫ ω, Y 0 ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, ∀ β : ℝ, 1 < β → ∀ᶠ m in atTop,
      (∑ j ∈ Finset.range m, Y j ω)
        ≤ β * √(2 * (∫ x, Y 0 x ^ 2 ∂μ) * (m : ℝ) * log (log (m : ℝ))) := by
  rcases eq_or_lt_of_le (integral_nonneg (fun ω ↦ sq_nonneg (Y 0 ω)) :
      (0 : ℝ) ≤ ∫ ω, Y 0 ω ^ 2 ∂μ) with hσ | hσ
  · -- Degenerate case `σ² = 0`: every `Y j` vanishes a.s., and both sides are `0`.
    have hY0 : Y 0 =ᵐ[μ] 0 := by
      have hz := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun ω ↦ sq_nonneg (Y 0 ω)) hint2.integrable_sq).mp hσ.symm
      filter_upwards [hz] with ω hω
      have h2 : Y 0 ω ^ 2 = 0 := hω
      simpa using sq_eq_zero_iff.mp h2
    have hYj : ∀ j, Y j =ᵐ[μ] 0 := by
      intro j
      have h0 : μ (Y 0 ⁻¹' ({(0 : ℝ)}ᶜ)) = 0 := by
        simpa [Set.preimage, Pi.zero_apply] using ae_iff.mp hY0
      have hj : μ (Y j ⁻¹' ({(0 : ℝ)}ᶜ)) = 0 := by
        rw [(hident j).measure_mem_eq (measurableSet_singleton (0 : ℝ)).compl]; exact h0
      refine ae_iff.mpr ?_
      simpa [Set.preimage, Pi.zero_apply] using hj
    filter_upwards [ae_all_iff.mpr hYj] with ω hω β _
    filter_upwards with m
    rw [Finset.sum_eq_zero fun j _ ↦ hω j, ← hσ]
    simp
  set σ2 := ∫ x, Y 0 x ^ 2 ∂μ with hσ2def
  set K := ∫ x, |Y 0 x| ∂μ with hKdef
  have hint0 : Integrable (Y 0) μ := hint2.integrable one_le_two
  have hident2 : ∀ j, IdentDistrib (fun ω ↦ Y j ω ^ 2) (fun ω ↦ Y 0 ω ^ 2) μ μ := fun j ↦
    (hident j).comp (u := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  have hint_i : ∀ i, Integrable (Y i) μ := fun i ↦ ((hident i).integrable_iff).mpr hint0
  have hint2_i : ∀ i, MemLp (Y i) 2 μ := fun i ↦
    (memLp_two_iff_integrable_sq (hY i).aestronglyMeasurable).mpr
      (((hident2 i).integrable_iff).mpr hint2.integrable_sq)
  have hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2 := fun i ↦ le_of_eq (hident2 i).integral_eq
  have hdrift := sum_integral_truncation_add_mediumTrunc_le hY hident hint2 hcent
  have ha_top : Tendsto (fun m : ℕ ↦ √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop atTop :=
    tendsto_sqrt_mul_loglog_atTop hσ
  have ha_pos : ∀ᶠ m : ℕ in atTop, 0 < √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) :=
    ha_top.eventually_gt_atTop 0
  have hw_pos : ∀ᶠ m : ℕ in atTop, 0 < √(2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3))) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hlt : (1 : ℝ) < log ((m : ℝ) + 3) :=
      one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by linarith))
    exact Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) (by linarith)) (Real.log_pos hlt))
  filter_upwards [ae_forall_one_lt_eventually_abs_le_sqrt_nat_mul_loglog_centeredTruncation
    hY hindep
      hint2_i hσ hv (b := logCutoff) monotone_logCutoff logCutoff_nonneg
      tendsto_logCutoff_mul_sqrt_loglog_div,
    ae_medium_div_weight_tendsto_zero hY hindep hident hint2,
    ae_eventually_abs_le_sqrt_of_identDistrib (fun i ↦ (hY i).measurable) hident hint2]
    with ω hlowω hmedω hhighω
  intro β hβ
  have hβ₁1 : (1 : ℝ) < (1 + β) / 2 := by linarith
  have hβ₁β : (1 + β) / 2 < β := by linarith
  set β₁ := (1 + β) / 2 with hβ₁def
  -- Low part: `|S̃_m| ≤ β₁ a_m` eventually.
  have hlowβ : ∀ᶠ m in atTop, |∑ j ∈ Finset.range m,
      (truncation (Y j) (logCutoff j) ω - ∫ x, truncation (Y j) (logCutoff j) x ∂μ)|
        ≤ β₁ * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) := by
    filter_upwards [hlowω β₁ hβ₁1] with m hm
    rwa [Finset.sum_apply] at hm
  -- Medium part: `W_m / a_m → 0`.
  have hWa : Tendsto (fun m ↦ (∑ j ∈ Finset.range m,
      (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
        / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
    have hbound : Tendsto (fun m ↦ (2 / √σ2) * |(∑ j ∈ Finset.range m,
        (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
          / √(2 * ((m : ℝ) + 3) * log (log ((m : ℝ) + 3)))|) atTop (𝓝 0) := by
      simpa using hmedω.abs.const_mul (2 / √σ2)
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [sqrt_add_three_mul_loglog_le hσ, ha_pos, hw_pos] with m hwle hapos hwpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hapos, abs_div, abs_of_pos hwpos]
    rw [div_le_iff₀ hapos, mul_comm (2 / √σ2), mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hwpos]
    have hWnn : 0 ≤ |∑ j ∈ Finset.range m,
        (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ)| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hwle hWnn]
  -- High part: eventually constant, so `H_m / a_m → 0`.
  have hHa : Tendsto (fun m ↦ (∑ j ∈ Finset.range m,
      ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
        / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
    have hzero : ∀ᶠ j : ℕ in atTop,
        ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω) = 0 := by
      filter_upwards [hhighω] with j hj
      apply Set.indicator_of_notMem
      simp only [Set.mem_ofPred_eq, not_lt]; exact hj
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hzero
    have hconst : ∀ᶠ m : ℕ in atTop, (∑ j ∈ Finset.range m,
        ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
          = ∑ j ∈ Finset.range J, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω) := by
      filter_upwards [eventually_ge_atTop J] with m hm
      refine (Finset.sum_subset (fun x hx ↦ Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hm)) (fun j _ hjnr ↦ ?_)).symm
      exact hJ j (by simpa using hjnr)
    have hCa : Tendsto (fun m : ℕ ↦ (∑ j ∈ Finset.range J,
        ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
          / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using ha_top.inv_tendsto_atTop.const_mul
        (∑ j ∈ Finset.range J, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
    exact hCa.congr' (hconst.mono (fun m h ↦ by simp only [h]))
  -- Drift scale and constant `/ a_m → 0`.
  have hSqa : Tendsto (fun m : ℕ ↦ (2 * σ2 * √(m : ℝ))
      / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
    have h : Tendsto (fun m : ℕ ↦ 2 * σ2 * (√(m : ℝ)
        / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))))) atTop (𝓝 0) := by
      simpa using (tendsto_sqrt_div_sqrt_mul_loglog hσ (c := σ2)).const_mul (2 * σ2)
    exact Tendsto.congr (fun m ↦ (mul_div_assoc _ _ _).symm) h
  have hKa : Tendsto (fun m : ℕ ↦ K / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ha_top.inv_tendsto_atTop.const_mul K
  -- Combined remainder `/ a_m → 0`, hence eventually `≤ (β - β₁) a_m`.
  have hrembd : ∀ᶠ m in atTop, (∑ j ∈ Finset.range m,
      (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
      + (∑ j ∈ Finset.range m, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
      + 2 * σ2 * √(m : ℝ) + K ≤ (β - β₁) * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) := by
    have hrem : Tendsto (fun m ↦ ((∑ j ∈ Finset.range m,
        (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
        + (∑ j ∈ Finset.range m, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
        + 2 * σ2 * √(m : ℝ) + K) / √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))) atTop (𝓝 0) := by
      have h4 := ((hWa.add hHa).add hSqa).add hKa
      simp only [add_zero] at h4
      exact Tendsto.congr (fun m ↦ by ring) h4
    filter_upwards [hrem.eventually_lt_const (show (0 : ℝ) < β - β₁ by linarith), ha_pos]
      with m hm hapos
    rw [div_lt_iff₀ hapos] at hm
    linarith
  -- Pointwise decomposition bound.
  have hSbound : ∀ m, (∑ j ∈ Finset.range m, Y j ω)
      ≤ (∑ j ∈ Finset.range m,
          (truncation (Y j) (logCutoff j) ω - ∫ x, truncation (Y j) (logCutoff j) x ∂μ))
        + (∑ j ∈ Finset.range m,
            (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
        + (∑ j ∈ Finset.range m, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
        + (∑ j ∈ Finset.range m,
            (∫ x, truncation (Y j) (logCutoff j) x ∂μ + ∫ x, mediumTrunc j (Y j x) ∂μ)) := by
    intro m
    calc (∑ j ∈ Finset.range m, Y j ω)
        ≤ ∑ j ∈ Finset.range m, (truncation (Y j) (logCutoff j) ω + mediumTrunc j (Y j ω)
            + ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω)) :=
          Finset.sum_le_sum fun j _ ↦ le_lowMedHigh (logCutoff_nonneg j) (logCutoff_le_sqrt j)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring
  -- Assemble the eventual bound `S_m ≤ β a_m`.
  filter_upwards [hlowβ, hrembd] with m hlm hrm
  calc (∑ j ∈ Finset.range m, Y j ω)
      ≤ _ := hSbound m
    _ ≤ |∑ j ∈ Finset.range m,
          (truncation (Y j) (logCutoff j) ω - ∫ x, truncation (Y j) (logCutoff j) x ∂μ)|
        + ((∑ j ∈ Finset.range m,
            (mediumTrunc j (Y j ω) - ∫ x, mediumTrunc j (Y j x) ∂μ))
          + (∑ j ∈ Finset.range m, ({y : ℝ | √(j : ℝ) < |y|}).indicator id (Y j ω))
          + 2 * σ2 * √(m : ℝ) + K) := by
        have := hdrift m; have := le_abs_self (∑ j ∈ Finset.range m,
          (truncation (Y j) (logCutoff j) ω - ∫ x, truncation (Y j) (logCutoff j) x ∂μ)); linarith
    _ ≤ β₁ * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ)))
        + (β - β₁) * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) := by linarith
    _ = β * √(2 * σ2 * (m : ℝ) * log (log (m : ℝ))) := by ring

/-- **Sharp i.i.d. Hartman–Wintner LIL, upper half** (Hartman–Wintner 1941). For an i.i.d., centred,
`L²` sequence with `σ² = 𝔼[Y_0²] > 0`, almost surely
`limsup_m (∑_{j<m} Y_j) / √(2σ² m log log m) ≤ 1`. Assembled from the coboundedness-free eventual
bound `ae_forall_one_lt_eventually_sum_le_sqrt_nat_mul_loglog` applied to `Y` (upper bound) and
to `-Y` (lower bound, giving coboundedness of
`S_m/a_m`), then `limsup_le_of_le`. -/
theorem iid_hartmanWintner_limsup_le_one [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hindep : iIndepFun Y μ)
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) μ μ)
    (hint2 : MemLp (Y 0) 2 μ) (hcent : ∫ ω, Y 0 ω ∂μ = 0)
    (hσ : 0 < ∫ ω, Y 0 ω ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, limsup (fun m ↦ (∑ j ∈ Finset.range m, Y j ω)
      / √(2 * (∫ x, Y 0 x ^ 2 ∂μ) * (m : ℝ) * log (log (m : ℝ)))) atTop ≤ 1 := by
  have hσeq : (∫ x, (-Y 0 x) ^ 2 ∂μ) = ∫ x, Y 0 x ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x ↦ neg_sq (Y 0 x))
  have ha_pos : ∀ᶠ m : ℕ in atTop,
      0 < √(2 * (∫ x, Y 0 x ^ 2 ∂μ) * (m : ℝ) * log (log (m : ℝ))) :=
    (tendsto_sqrt_mul_loglog_atTop hσ).eventually_gt_atTop 0
  have hY_ev := ae_forall_one_lt_eventually_sum_le_sqrt_nat_mul_loglog hY hindep hident hint2 hcent
  have hnegY_ev := ae_forall_one_lt_eventually_sum_le_sqrt_nat_mul_loglog (Y := fun i ω ↦ -Y i ω)
    (fun i ↦ (hY i).neg)
    (hindep.comp (fun _ ↦ (- ·)) (fun _ ↦ measurable_neg))
    (fun j ↦ (hident j).comp (u := fun x : ℝ ↦ -x) measurable_neg)
    hint2.neg
    (by simp only [integral_neg, hcent, neg_zero])
  simp only [hσeq] at hnegY_ev
  filter_upwards [hY_ev, hnegY_ev] with ω h1 h2
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun m ↦ (∑ j ∈ Finset.range m, Y j ω)
      / √(2 * (∫ x, Y 0 x ^ 2 ∂μ) * (m : ℝ) * log (log (m : ℝ)))) := by
    refine IsCoboundedUnder.of_frequently_ge (a := -2) (Eventually.frequently ?_)
    filter_upwards [h2 2 (by norm_num), ha_pos] with m hm hpos
    rw [le_div_iff₀ hpos]
    rw [Finset.sum_neg_distrib] at hm
    linarith
  exact limsup_div_le_one_of_forall_one_lt (fun _ ↦ sqrt_nonneg _) hcobdd h1

end AlphaRAR
