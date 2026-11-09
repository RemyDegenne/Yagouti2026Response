/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Process.Filtration

/-!
# Analytic ingredients of the martingale central limit theorem

Bounds on the complex and real exponentials, conditional characteristic increments, and bounded
convergence in probability: the analytic ingredients of the martingale central limit theorem of
`MartingaleCLT.lean`, stated for their own sake.

## Main results

* `AlphaRAR.norm_expI_sub_taylor_le` : `‖e^{ix} - (1 + ix - x²/2)‖ ≤ min (2x²) |x|³`,
  the second-order expansion of the complex exponential on the imaginary axis, valid for every
  real `x` (Mathlib's `Complex.norm_exp_sub_one_sub_id_le` needs `‖x‖ ≤ 1`).
* `AlphaRAR.abs_exp_mul_one_sub_le'` : `|eʸ(1-y) - 1| ≤ y² eʸ` for `y ≥ 0`.
* `AlphaRAR.tendsto_integral_of_tendstoInMeasure` : bounded convergence in probability,
  `∫ g n → ∫ f` when `g n → f` in measure and `‖g n‖ ≤ C` a.e.
* `AlphaRAR.tendsto_integral_sq_indicator_gt` : `∫ Z² 𝟙{|Z| > c} → 0` as `c → ∞` for `Z ∈ L²`, the
  analytic heart of every i.i.d. Lindeberg condition.
-/

@[expose] public section

open Complex intervalIntegral MeasureTheory
open scoped ENNReal ProbabilityTheory Real Topology

namespace AlphaRAR

section ExpBound

/-- Derivative of `s ↦ (s : ℂ)`. -/
lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 x := by
  simpa using (hasDerivAt_id x).ofReal_comp

/-- Derivative of `s ↦ (s : ℂ) * I`. -/
lemma hasDerivAt_ofReal_mul_I (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (s : ℂ) * I) I x := by
  simpa using (hasDerivAt_ofReal x).mul_const I

/-- Derivative of `s ↦ exp (s * I)` as a map `ℝ → ℂ`. -/
lemma hasDerivAt_expI (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (s * I)) (Complex.exp (x * I) * I) x :=
  (hasDerivAt_ofReal_mul_I x).cexp

/-- Derivative of `s ↦ (s : ℂ)² / 2`. -/
lemma hasDerivAt_ofReal_sq_div_two (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (s : ℂ) ^ 2 / 2) (x : ℂ) x := by
  have hr : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) x x := by
    have h : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * x) x := by
      simpa [pow_one] using hasDerivAt_pow 2 x
    have hd := h.div_const 2
    rw [show (2 * x) / 2 = x by ring] at hd
    exact hd
  simpa [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat] using hr.ofReal_comp

/-- On the segment between `0` and `x`, points have absolute value `≤ |x|`. -/
lemma abs_le_of_mem_uIoc {x s : ℝ} (hs : s ∈ Set.uIoc 0 x) : |s| ≤ |x| := by
  simp only [Set.uIoc, Set.mem_Ioc] at hs
  obtain ⟨h1, h2⟩ := hs
  have hmin : -|x| ≤ (0 ⊓ x) := le_min (neg_nonpos.mpr (abs_nonneg x)) (neg_abs_le x)
  have hmax : (0 ⊔ x) ≤ |x| := max_le (abs_nonneg x) (le_abs_self x)
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- First-order bound: `‖e^{ix} - 1‖ ≤ |x|`. -/
lemma norm_expI_sub_one_le (x : ℝ) : ‖Complex.exp (x * I) - 1‖ ≤ |x| := by
  have key : Complex.exp (x * I) - 1 = ∫ s in (0 : ℝ)..x, Complex.exp (s * I) * I := by
    have h := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (f := fun s : ℝ ↦ Complex.exp (s * I))
      (f' := fun s : ℝ ↦ Complex.exp (s * I) * I)
      (fun s _ ↦ hasDerivAt_expI s)
      (by apply Continuous.intervalIntegrable; fun_prop)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h
    exact h.symm
  rw [key]
  calc ‖∫ s in (0 : ℝ)..x, Complex.exp (s * I) * I‖
      ≤ 1 * |x - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s _
        simp [Complex.norm_exp_ofReal_mul_I]
    _ = |x| := by rw [one_mul, sub_zero]

/-- Second-order bound: `‖e^{ix} - 1 - ix‖ ≤ x²`. -/
lemma norm_expI_sub_one_sub_le (x : ℝ) :
    ‖Complex.exp (x * I) - 1 - x * I‖ ≤ x ^ 2 := by
  have key : Complex.exp (x * I) - 1 - x * I
      = ∫ s in (0 : ℝ)..x, (Complex.exp (s * I) * I - I) := by
    have h := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (f := fun s : ℝ ↦ Complex.exp (s * I) - 1 - s * I)
      (f' := fun s : ℝ ↦ Complex.exp (s * I) * I - I)
      (fun s _ ↦ ((hasDerivAt_expI s).sub_const 1).sub (hasDerivAt_ofReal_mul_I s))
      (by apply Continuous.intervalIntegrable; fun_prop)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero] at h
    exact h.symm
  rw [key]
  calc ‖∫ s in (0 : ℝ)..x, (Complex.exp (s * I) * I - I)‖
      ≤ |x| * |x - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        have heq : Complex.exp (s * I) * I - I = (Complex.exp (s * I) - 1) * I := by ring
        rw [heq, norm_mul, Complex.norm_I, mul_one]
        exact le_trans (norm_expI_sub_one_le s) (abs_le_of_mem_uIoc hs)
    _ = x ^ 2 := by rw [sub_zero, ← sq_abs x, pow_two]

/-- **Complex exponential expansion**: the second-order Taylor remainder of `e^{ix}` on the
imaginary axis is `O(min(x², |x|³))`. -/
lemma norm_expI_sub_taylor_le (x : ℝ) :
    ‖Complex.exp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2‖ ≤ min (2 * x ^ 2) (|x| ^ 3) := by
  rw [le_min_iff]
  refine ⟨?_, ?_⟩
  · -- quadratic bound `2 x²` via the triangle inequality
    have h2 : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by
      have hcast : ((x : ℂ) ^ 2 / 2) = ((x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖Complex.exp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2‖
        ≤ ‖Complex.exp (x * I) - 1 - x * I‖ + ‖(x : ℂ) ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ x ^ 2 + x ^ 2 / 2 := by rw [h2]; linarith [norm_expI_sub_one_sub_le x]
      _ ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg x]
  · -- cubic bound `|x|³` via a third integration
    have key : Complex.exp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2
        = ∫ s in (0 : ℝ)..x, (Complex.exp (s * I) * I - I + s) := by
      have h := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
        (f := fun s : ℝ ↦ Complex.exp (s * I) - 1 - s * I + (s : ℂ) ^ 2 / 2)
        (f' := fun s : ℝ ↦ Complex.exp (s * I) * I - I + s)
        (fun s _ ↦ (((hasDerivAt_expI s).sub_const 1).sub (hasDerivAt_ofReal_mul_I s)).add
          (hasDerivAt_ofReal_sq_div_two s))
        (by apply Continuous.intervalIntegrable; fun_prop)
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, sub_zero] at h
      exact h.symm
    rw [key]
    calc ‖∫ s in (0 : ℝ)..x, (Complex.exp (s * I) * I - I + s)‖
        ≤ x ^ 2 * |x - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro s hs
          have heq : Complex.exp (s * I) * I - I + (s : ℂ)
              = (Complex.exp (s * I) - 1 - s * I) * I := by
            rw [sub_mul, sub_mul, one_mul, mul_assoc, Complex.I_mul_I]; ring
          rw [heq, norm_mul, Complex.norm_I, mul_one]
          refine le_trans (norm_expI_sub_one_sub_le s) ?_
          nlinarith [abs_le_of_mem_uIoc hs, abs_nonneg s, abs_nonneg x, sq_abs s, sq_abs x]
      _ = |x| ^ 3 := by rw [sub_zero, ← sq_abs x]; ring

end ExpBound

section RealExpBound

/-- **Real elementary bound**: `|eʸ(1-y) - 1| ≤ y²·eʸ` for every `y ≥ 0`. The factor `eʸ` is what
makes it valid past `y = 1`; on `[0, 1]` the bound `y²` would do, but the predictable variation the
bound is applied to is only known to be bounded, not `≤ 1`. -/
lemma abs_exp_mul_one_sub_le' {y : ℝ} (hy : 0 ≤ y) :
    |Real.exp y * (1 - y) - 1| ≤ y ^ 2 * Real.exp y := by
  have hle : Real.exp y * (1 - y) ≤ 1 := by
    have h1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos y).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
  have hquad : (0 : ℝ) ≤ 1 - y + y ^ 2 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have hge : 1 ≤ Real.exp y * (1 - y) + y ^ 2 * Real.exp y := by
    have hexp : (1 : ℝ) + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    nlinarith [mul_le_mul_of_nonneg_right hexp hquad, pow_nonneg hy 3, Real.exp_pos y]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **`exp(-·)` is `1`-Lipschitz on `[0,∞)`**: for `a, b ≥ 0`, `|e^{-a} - e^{-b}| ≤ |a - b|`.
Used to transfer `V_n → σ²` in probability through the map `x ↦ e^{-(t²/2)x}`. -/
lemma abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a]
    exact this hb ha (not_le.mp hab).le
  have hfac : Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    rw [mul_sub, mul_one, ← Real.exp_add, show -a + -(b - a) = -b from by ring]
  have hle1 : Real.exp (-a) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hpos : 0 ≤ 1 - Real.exp (-(b - a)) := by
    have : Real.exp (-(b - a)) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hub : 1 - Real.exp (-(b - a)) ≤ b - a := by
    have := Real.add_one_le_exp (-(b - a)); linarith
  have h2 : Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    rw [hfac]
    calc Real.exp (-a) * (1 - Real.exp (-(b - a)))
        ≤ 1 * (1 - Real.exp (-(b - a))) := mul_le_mul_of_nonneg_right hle1 hpos
      _ = 1 - Real.exp (-(b - a)) := one_mul _
      _ ≤ b - a := hub
  have h3 : 0 ≤ Real.exp (-a) - Real.exp (-b) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  rw [abs_of_nonneg h3, abs_of_nonpos (by linarith : a - b ≤ 0)]
  linarith [h2]

/-- **Factor bound behind the one-step `Z`-increment estimate.** For `v ≥ 0` and a complex `w`
approximating `1 - (t²/2)v` with error `‖w - (1 - (t²/2)v)‖ ≤ ρ`, the multiplicative increment
`e^{(t²/2)v} w - 1` has modulus
`‖e^{(t²/2)v} w - 1‖ ≤ e^{(t²/2)v}·((t⁴/4)v² + ρ)`.
Split `e^{y}w - 1 = e^{y}(w-(1-y)) + (e^{y}(1-y)-1)` with `y = (t²/2)v`; the first term is
bounded by `e^{y}ρ`, the second by `y²e^{y}` via `abs_exp_mul_one_sub_le'`. The `e^{y}` factor is
essential — `y` is only known to be bounded, not `≤ 1`. -/
lemma norm_expVar_mul_sub_one_le {t v ρ : ℝ} (hv : 0 ≤ v) {w : ℂ}
    (hw : ‖w - (1 - ((t ^ 2 / 2 * v : ℝ) : ℂ))‖ ≤ ρ) :
    ‖Complex.exp ((t ^ 2 / 2 * v : ℝ) : ℂ) * w - 1‖
      ≤ Real.exp (t ^ 2 / 2 * v) * (t ^ 4 / 4 * v ^ 2 + ρ) := by
  set y : ℝ := t ^ 2 / 2 * v with hy
  have hy_nn : 0 ≤ y := by rw [hy]; exact mul_nonneg (by positivity) hv
  have hnorm_expy : ‖Complex.exp (y : ℂ)‖ = Real.exp y := by
    rw [Complex.norm_exp, Complex.ofReal_re]
  have he : ((Real.exp y * (1 - y) - 1 : ℝ) : ℂ) = Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1 := by
    push_cast; ring
  have hbound2 : ‖Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1‖ ≤ y ^ 2 * Real.exp y := by
    rw [← he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_exp_mul_one_sub_le' hy_nn
  have hsplit : Complex.exp (y : ℂ) * w - 1
      = Complex.exp (y : ℂ) * (w - (1 - (y : ℂ))) + (Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1) := by
    ring
  calc ‖Complex.exp (y : ℂ) * w - 1‖
      = ‖Complex.exp (y : ℂ) * (w - (1 - (y : ℂ)))
          + (Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1)‖ := by rw [hsplit]
    _ ≤ ‖Complex.exp (y : ℂ) * (w - (1 - (y : ℂ)))‖
          + ‖Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1‖ := norm_add_le _ _
    _ = Real.exp y * ‖w - (1 - (y : ℂ))‖ + ‖Complex.exp (y : ℂ) * (1 - (y : ℂ)) - 1‖ := by
        rw [norm_mul, hnorm_expy]
    _ ≤ Real.exp y * ρ + y ^ 2 * Real.exp y :=
        add_le_add (mul_le_mul_of_nonneg_left hw (Real.exp_pos y).le) hbound2
    _ = Real.exp y * (t ^ 4 / 4 * v ^ 2 + ρ) := by rw [hy]; ring

end RealExpBound

section CondChar

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **Conditional characteristic increment**: for a centered square-integrable increment `Δ` and a
sub-σ-algebra `m`, the conditional characteristic function `E[e^{itΔ}|m]` agrees with
`1 - (t²/2)E[Δ²|m]` up to an error whose norm is bounded a.e. by the conditional expectation of
`min(2t²Δ², |t|³|Δ|³)`. -/
lemma norm_condExp_expI_sub_le [IsProbabilityMeasure P] (hm : m ≤ m0)
    {Δ : Ω → ℝ} (hΔ : MemLp Δ 2 P) (hcent : P[Δ | m] =ᵐ[P] 0) (t : ℝ) :
    (fun ω ↦ ‖(P[fun ω' ↦ Complex.exp (((t * Δ ω' : ℝ) : ℂ) * I) | m]) ω
        - (1 - (((t ^ 2 / 2) * (P[fun ω' ↦ (Δ ω') ^ 2 | m]) ω : ℝ) : ℂ))‖)
      ≤ᵐ[P] P[fun ω' ↦ min (2 * t ^ 2 * (Δ ω') ^ 2) (|t| ^ 3 * |Δ ω'| ^ 3) | m] := by
  classical
  have hΔ1 : Integrable Δ P := hΔ.integrable one_le_two
  have hΔ2 : Integrable (fun ω ↦ (Δ ω) ^ 2) P := hΔ.integrable_sq
  have haesm : AEStronglyMeasurable Δ P := hΔ.aestronglyMeasurable
  -- integrand functions
  set g : Ω → ℂ := fun ω' ↦ Complex.exp (((t * Δ ω' : ℝ) : ℂ) * I) with hg_def
  set lin : Ω → ℂ := fun ω' ↦ ((t * Δ ω' : ℝ) : ℂ) * I with hlin_def
  set quad : Ω → ℂ := fun ω' ↦ (((t * Δ ω' : ℝ) : ℂ)) ^ 2 / 2 with hquad_def
  let R : Ω → ℂ := fun ω' ↦ g ω' - 1 - lin ω' + quad ω'
  let v : Ω → ℝ := P[fun ω' ↦ (Δ ω') ^ 2 | m]
  let φ : Ω → ℝ := fun ω' ↦ min (2 * t ^ 2 * (Δ ω') ^ 2) (|t| ^ 3 * |Δ ω'| ^ 3)
  -- helper: condExp commutes with the coercion ℝ → ℂ
  have hofReal : ∀ (f : Ω → ℝ), Integrable f P →
      (P[fun ω ↦ ((f ω : ℝ) : ℂ) | m]) =ᵐ[P] fun ω ↦ ((P[f | m] ω : ℝ) : ℂ) :=
    fun f hf ↦ (Complex.ofRealCLM.comp_condExp_comm hf).symm
  -- integrabilities
  have hg_aesm : AEStronglyMeasurable g P :=
    Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (haesm.const_mul t)).mul aestronglyMeasurable_const)
  have hg_int : Integrable g P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hg_aesm (ae_of_all _ fun ω ↦ ?_)
    simp only [hg_def]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (t * Δ ω))
  have hlin_int : Integrable lin P :=
    (Complex.ofRealCLM.integrable_comp (hΔ1.const_mul t)).mul_const I
  have hquad_eq : quad = fun ω ↦ ((t ^ 2 / 2 * (Δ ω) ^ 2 : ℝ) : ℂ) := by
    funext ω; simp only [hquad_def]; push_cast; ring
  have hquad_int : Integrable quad P := by
    rw [hquad_eq]
    exact Complex.ofRealCLM.integrable_comp (hΔ2.const_mul (t ^ 2 / 2))
  have hR_int : Integrable R P := ((hg_int.sub (integrable_const 1)).sub hlin_int).add hquad_int
  -- pointwise bound on the remainder R
  have hR_le : ∀ ω, ‖R ω‖ ≤ φ ω := fun ω ↦ by
    have h := norm_expI_sub_taylor_le (t * Δ ω)
    have e1 : (2 : ℝ) * (t * Δ ω) ^ 2 = 2 * t ^ 2 * (Δ ω) ^ 2 := by ring
    have e2 : |t * Δ ω| ^ 3 = |t| ^ 3 * |Δ ω| ^ 3 := by rw [abs_mul, mul_pow]
    rw [e1, e2] at h
    exact h
  -- helper: pull a real scalar out of a real conditional expectation
  have hcond_smul : ∀ (c : ℝ) (f : Ω → ℝ),
      P[fun ω ↦ c * f ω | m] =ᵐ[P] fun ω ↦ c * P[f | m] ω := by
    intro c f
    have hcf : (fun ω ↦ c * f ω) = c • f := by funext ω; simp [Pi.smul_apply]
    rw [hcf]
    filter_upwards [condExp_smul c f m] with ω hω
    rw [hω]; simp [Pi.smul_apply]
  -- condExp of the three easy pieces
  have hc1 : P[fun _ : Ω ↦ (1 : ℂ) | m] = fun _ ↦ 1 := condExp_const hm 1
  have hclin : P[lin | m] =ᵐ[P] 0 := by
    have hI : lin = fun ω ↦ (↑t * I) • ((Δ ω : ℝ) : ℂ) := by
      funext ω; simp only [hlin_def, smul_eq_mul]; push_cast; ring
    rw [hI]
    have hz : P[fun ω ↦ ((Δ ω : ℝ) : ℂ) | m] =ᵐ[P] 0 := by
      filter_upwards [hofReal Δ hΔ1, hcent] with ω hω hω0
      rw [hω, hω0]; simp
    calc P[fun ω ↦ ((t : ℂ) * I) • ((Δ ω : ℝ) : ℂ) | m]
        =ᵐ[P] ((t : ℂ) * I) • P[fun ω ↦ ((Δ ω : ℝ) : ℂ) | m] :=
          condExp_smul ((t : ℂ) * I) (fun ω ↦ ((Δ ω : ℝ) : ℂ)) m
      _ =ᵐ[P] 0 := by filter_upwards [hz] with ω hω; rw [Pi.smul_apply, hω]; simp
  have hcquad : P[quad | m] =ᵐ[P] fun ω ↦ ((t ^ 2 / 2 * v ω : ℝ) : ℂ) := by
    rw [hquad_eq]
    calc P[fun ω ↦ ((t ^ 2 / 2 * (Δ ω) ^ 2 : ℝ) : ℂ) | m]
        =ᵐ[P] fun ω ↦ ((P[fun ω' ↦ t ^ 2 / 2 * (Δ ω') ^ 2 | m] ω : ℝ) : ℂ) :=
          hofReal _ (hΔ2.const_mul (t ^ 2 / 2))
      _ =ᵐ[P] fun ω ↦ ((t ^ 2 / 2 * v ω : ℝ) : ℂ) := by
          filter_upwards [hcond_smul (t ^ 2 / 2) (fun ω ↦ (Δ ω) ^ 2)] with ω hω
          rw [hω]
  -- the key identity: `E[g|m] - (1 - ↑(t²/2·v)) =ᵐ E[R|m]`
  have hgR : (fun ω ↦ (P[g | m]) ω - (1 - ((t ^ 2 / 2 * v ω : ℝ) : ℂ))) =ᵐ[P] P[R | m] := by
    have hRexp : P[R | m] =ᵐ[P]
        fun ω ↦ (P[g | m]) ω - 1 - (P[lin | m]) ω + (P[quad | m]) ω := by
      have hR_eq : R = g - (fun _ ↦ 1) - lin + quad := rfl
      rw [hR_eq]
      filter_upwards
        [condExp_add ((hg_int.sub (integrable_const 1)).sub hlin_int) hquad_int m,
          condExp_sub (hg_int.sub (integrable_const 1)) hlin_int m,
          condExp_sub hg_int (integrable_const 1) m] with ω hadd hsub1 hsub2
      simp only [Pi.add_apply, Pi.sub_apply, hc1] at hadd hsub1 hsub2 ⊢
      rw [hadd, hsub1, hsub2]
    filter_upwards [hRexp, hclin, hcquad] with ω hR hlin0 hquad0
    rw [hR]
    simp only [Pi.zero_apply] at hlin0
    rw [hlin0, hquad0]; ring
  -- assemble the norm bound
  have hφ_aesm : AEStronglyMeasurable φ P := by
    have hcont : Continuous (fun x : ℝ ↦ min (2 * t ^ 2 * x ^ 2) (|t| ^ 3 * |x| ^ 3)) := by
      fun_prop
    exact hcont.comp_aestronglyMeasurable haesm
  have hφ_nonneg : ∀ ω, 0 ≤ φ ω := fun ω ↦ le_min (by positivity) (by positivity)
  have hφ_int : Integrable φ P :=
    (hΔ2.const_mul (2 * t ^ 2)).mono' hφ_aesm
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφ_nonneg ω)]; exact min_le_left _ _)
  have hnorm : (fun ω ↦ ‖(P[R | m]) ω‖) ≤ᵐ[P] P[fun ω ↦ ‖R ω‖ | m] := norm_condExp_le R
  have hmono : P[fun ω ↦ ‖R ω‖ | m] ≤ᵐ[P] P[φ | m] :=
    condExp_mono hR_int.norm hφ_int (ae_of_all _ hR_le)
  filter_upwards [hgR, hnorm, hmono] with ω h1 h2 h3
  rw [h1]
  exact le_trans h2 h3

/-- Conditional variance split at level `ε` (per-cell core):
`E[d²|m] ≤ ε² + E[d²·𝟙{|d|>ε}|m]` a.e. -/
lemma condExp_sq_le [IsProbabilityMeasure P] {d : Ω → ℝ} (hd : Measurable d)
    (hd2 : MemLp d 2 P) (hm : m ≤ m0) (ε : ℝ) :
    P[fun ω ↦ (d ω) ^ 2 | m] ≤ᵐ[P]
      fun ω ↦ ε ^ 2 + (P[{ω | ε < |d ω|}.indicator (fun ω ↦ (d ω) ^ 2) | m]) ω := by
  set s : Set Ω := {ω | ε < |d ω|} with hs_def
  have hs : MeasurableSet s := measurableSet_lt measurable_const hd.abs
  have hind_int : Integrable (s.indicator (fun ω ↦ (d ω) ^ 2)) P :=
    hd2.integrable_sq.indicator hs
  have hle : ((fun ω ↦ (d ω) ^ 2) - s.indicator (fun ω ↦ (d ω) ^ 2)) ≤ᵐ[P] fun _ ↦ ε ^ 2 := by
    filter_upwards with ω
    simp only [Pi.sub_apply]
    by_cases h : ω ∈ s
    · rw [Set.indicator_of_mem h, sub_self]; exact sq_nonneg ε
    · rw [Set.indicator_of_notMem h, sub_zero]
      have hd_le : |d ω| ≤ ε := by simpa only [hs_def, Set.mem_ofPred_eq, not_lt] using h
      nlinarith [sq_abs (d ω), abs_nonneg (d ω), hd_le]
  have hsub : P[(fun ω ↦ (d ω) ^ 2) - s.indicator (fun ω ↦ (d ω) ^ 2) | m]
      ≤ᵐ[P] fun _ ↦ ε ^ 2 := by
    rw [← condExp_const (μ := P) hm (ε ^ 2)]
    exact condExp_mono (hd2.integrable_sq.sub hind_int) (integrable_const _) hle
  filter_upwards [condExp_sub hd2.integrable_sq hind_int m, hsub] with ω hsplit hb
  rw [hsplit] at hb
  simp only [Pi.sub_apply] at hb
  linarith

/-- Pull a real scalar out of a real conditional expectation. -/
lemma condExp_const_mul (c : ℝ) (f : Ω → ℝ) :
    P[fun ω ↦ c * f ω | m] =ᵐ[P] fun ω ↦ c * (P[f | m]) ω := condExp_smul c f m

/-- Split the conditional expectation of `min(2t²d², |t|³|d|³)` at level `ε ≥ 0` into a
`v`-term and a Lindeberg term (per-cell core). -/
lemma condExp_min_le {d : Ω → ℝ} (hd : Measurable d)
    (hd2 : MemLp d 2 P) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    P[fun ω ↦ min (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3) | m] ≤ᵐ[P]
      fun ω ↦ |t| ^ 3 * ε * (P[fun ω ↦ (d ω) ^ 2 | m]) ω
        + 2 * t ^ 2 * (P[{ω | ε < |d ω|}.indicator (fun ω ↦ (d ω) ^ 2) | m]) ω := by
  set s : Set Ω := {ω | ε < |d ω|} with hs_def
  have hs : MeasurableSet s := measurableSet_lt measurable_const hd.abs
  have hind_int : Integrable (s.indicator (fun ω ↦ (d ω) ^ 2)) P :=
    hd2.integrable_sq.indicator hs
  have hmin_int :
      Integrable (fun ω ↦ min (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3)) P := by
    have hcont : Continuous (fun x : ℝ ↦ min (2 * t ^ 2 * x ^ 2) (|t| ^ 3 * |x| ^ 3)) := by
      fun_prop
    refine (hd2.integrable_sq.const_mul (2 * t ^ 2)).mono'
      (hcont.comp_aestronglyMeasurable hd.aestronglyMeasurable) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (by positivity))]
    exact min_le_left _ _
  have hle : ∀ ω, min (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3) ≤
      |t| ^ 3 * ε * (d ω) ^ 2 + 2 * t ^ 2 * (s.indicator (fun ω ↦ (d ω) ^ 2) ω) := by
    intro ω
    have hnn0 : 0 ≤ |t| ^ 3 * ε * (d ω) ^ 2 := by positivity
    by_cases h : ω ∈ s
    · rw [Set.indicator_of_mem h]
      have hml := min_le_left (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3)
      linarith
    · rw [Set.indicator_of_notMem h, mul_zero, add_zero]
      have hd_le : |d ω| ≤ ε := by simpa only [hs_def, Set.mem_ofPred_eq, not_lt] using h
      have hmr := min_le_right (2 * t ^ 2 * (d ω) ^ 2) (|t| ^ 3 * |d ω| ^ 3)
      have hcube : |t| ^ 3 * |d ω| ^ 3 ≤ |t| ^ 3 * ε * (d ω) ^ 2 := by
        have h2 : |d ω| ^ 3 = |d ω| * (d ω) ^ 2 := by rw [pow_succ, sq_abs]; ring
        have hi : |d ω| ^ 3 ≤ ε * (d ω) ^ 2 := by
          rw [h2]; exact mul_le_mul_of_nonneg_right hd_le (sq_nonneg _)
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hi (pow_nonneg (abs_nonneg t) 3)
      linarith
  have hg_int := (hd2.integrable_sq.const_mul (|t| ^ 3 * ε)).add
    (hind_int.const_mul (2 * t ^ 2))
  have hmono := condExp_mono (m := m) hmin_int hg_int (ae_of_all _ hle)
  filter_upwards [hmono,
    condExp_add (hd2.integrable_sq.const_mul (|t| ^ 3 * ε)) (hind_int.const_mul (2 * t ^ 2)) m,
    condExp_const_mul (m := m) (|t| ^ 3 * ε) (fun ω ↦ (d ω) ^ 2),
    condExp_const_mul (m := m) (2 * t ^ 2) (s.indicator (fun ω ↦ (d ω) ^ 2))]
    with ω hm1 hadd h1 h2
  rw [hadd] at hm1
  simp only [Pi.add_apply] at hm1
  rw [h1, h2] at hm1
  exact hm1

end CondChar

section BoundedConvergence

open Filter

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Bounded convergence in probability.** On a finite measure, if `g n → f` in measure and
`‖g n‖ ≤ C` a.e. uniformly in `n`, then `∫ g n → ∫ f`. Every subsequence has a further subsequence
converging a.e. (`TendstoInMeasure.exists_seq_tendsto_ae`), along which dominated convergence
applies. This is the quantitative core of the bounded-convergence steps of the martingale CLT
(`V_n →ᵖ σ²` and `L_n(ε) →ᵖ 0`). -/
lemma tendsto_integral_of_tendstoInMeasure [IsFiniteMeasure P] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ → Ω → E} {f : Ω → E} {C : ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (g n) P) (hbdd : ∀ n, ∀ᵐ ω ∂P, ‖g n ω‖ ≤ C)
    (hconv : TendstoInMeasure P g atTop f) :
    Tendsto (fun n ↦ ∫ ω, g n ω ∂P) atTop (𝓝 (∫ ω, f ω ∂P)) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ms, -, hae⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  exact ⟨ms, tendsto_integral_of_dominated_convergence (fun _ ↦ C) (fun _ ↦ hmeas _)
    (integrable_const C) (fun _ ↦ hbdd _) hae⟩

/-- **Bounded × (→ 0 in measure) = → 0 in measure.** If `‖f n‖ ≤ C` a.e. and `h n → 0` in
measure, then `f n · h n → 0` in measure. -/
lemma tendstoInMeasure_bdd_mul {f h : ℕ → Ω → ℂ} {C : ℝ}
    (hf : ∀ n, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ C) (hh : TendstoInMeasure P h atTop 0) :
    TendstoInMeasure P (fun n ω ↦ f n ω * h n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_dist]
  rw [tendstoInMeasure_iff_dist] at hh
  intro ε hε
  let C' := max C 1
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : ∀ n, {ω | ε ≤ dist (f n ω * h n ω) 0} ≤ᵐ[P] {ω | ε / C' ≤ dist (h n ω) 0} := by
    intro n
    filter_upwards [hf n] with ω hbd hmem
    have h1 : ε ≤ ‖f n ω‖ * ‖h n ω‖ := by
      have hd : ε ≤ dist (f n ω * h n ω) 0 := hmem
      rwa [dist_zero_right, norm_mul] at hd
    change ε / C' ≤ dist (h n ω) 0
    rw [dist_zero_right, div_le_iff₀ hC'0]
    calc ε ≤ ‖f n ω‖ * ‖h n ω‖ := h1
      _ ≤ C' * ‖h n ω‖ :=
          mul_le_mul_of_nonneg_right (le_trans hbd (le_max_left _ _)) (norm_nonneg _)
      _ = ‖h n ω‖ * C' := mul_comm _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hh (ε / C') (by positivity))
    (fun _ ↦ zero_le) (fun n ↦ measure_mono_ae (hsub n))

/-- **Domination for convergence in measure.** If `0 ≤ g n ≤ h n` a.e. and `h n → 0` in measure,
then `g n → 0` in measure. -/
lemma tendstoInMeasure_zero_of_le {g h : ℕ → Ω → ℝ}
    (hg0 : ∀ n, (0 : Ω → ℝ) ≤ᵐ[P] g n) (hgh : ∀ n, g n ≤ᵐ[P] h n)
    (hh : TendstoInMeasure P h atTop 0) : TendstoInMeasure P g atTop 0 := by
  rw [tendstoInMeasure_iff_dist]
  rw [tendstoInMeasure_iff_dist] at hh
  intro ε hε
  have hsub : ∀ n, {ω | ε ≤ dist (g n ω) 0} ≤ᵐ[P] {ω | ε ≤ dist (h n ω) 0} := by
    intro n
    filter_upwards [hg0 n, hgh n] with ω h0 h1 hmem
    simp only [Pi.zero_apply] at h0
    have hg : ε ≤ dist (g n ω) 0 := hmem
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0] at hg
    change ε ≤ dist (h n ω) 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_trans h0 h1)]
    exact le_trans hg h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hh ε hε)
    (fun _ ↦ zero_le) (fun n ↦ measure_mono_ae (hsub n))

/-- **Tail of a square-integrable variable vanishes.** If `Z²` is integrable, then
`∫ Z²·𝟙{|Z|>c} → 0` as `c → ∞`. This is the analytic heart of the i.i.d. Lindeberg condition:
each cell's conditional Lindeberg quantity is (a proportion times) `E[(ξ-θ)²𝟙{|ξ-θ|>c_n}]` with
`c_n → ∞`. -/
lemma tendsto_integral_sq_indicator_gt {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ2 : MemLp Z 2 P) :
    Tendsto (fun c : ℝ ↦ ∫ ω, {ω | c < |Z ω|}.indicator (fun ω ↦ (Z ω) ^ 2) ω ∂P)
      atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∫ _ω, (0 : ℝ) ∂P by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun ω ↦ (Z ω) ^ 2)
    (Eventually.of_forall fun c ↦ (hZ2.integrable_sq.aestronglyMeasurable).indicator
      (measurableSet_lt measurable_const hZ.abs))
    (Eventually.of_forall fun c ↦ ae_of_all _ fun ω ↦ ?_) hZ2.integrable_sq
    (ae_of_all _ fun ω ↦ ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω)]
    exact Set.indicator_le_self' (fun a _ ↦ sq_nonneg (Z a)) ω
  · apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_gt_atTop (|Z ω|)] with c hc
    exact Set.indicator_of_notMem (show ω ∉ {ω | c < |Z ω|} from not_lt.mpr hc.le) _

end BoundedConvergence

end AlphaRAR
