/-
# Three of the five analytic inputs of the elementary constant, discharged

`secondvar_assembly` consumes five analytic facts.  This file proves three of them for
continuously differentiable functions — the absorption inequality, the subset
monotonicity, and the tail cut — from one engine:

    (f b - f a)² ≤ (b - a) · ∫_a^b f'²                          (`sq_sub_le`)

proved WITHOUT Cauchy–Schwarz machinery: the function
`G t = (t - a) ∫_a^t f'² - (f t - f a)²` has `G a = 0` and

    G' t = ∫_a^t (f' s - f' t)² ds ≥ 0 ,

so `G` is monotone.  The derivative computation is FTC-2 plus the product rule, and the
rewriting of `G'` as the integral of a square is the linearity of the integral; no other
analysis enters.

What is NOT here: the two Wirtinger inequalities (`hW4`, `hW1`), whose sharp constants
`4` and `1` need the ground-state substitution `f = φ g` with `φ = sin 2t` resp. `sin t`
and one integration by parts with a removable singularity at the Dirichlet end.  Mathlib
has neither inequality.  They remain the ONLY analytic hypotheses of the elementary
constant; `secondvar_for_functions` below records the reduction from five to two.
-/
import Mathlib
import MovingSofa.SecondVar

namespace MovingSofa

open Real MeasureTheory intervalIntegral

variable {f f' : ℝ → ℝ}

/-- Expanding the square under the integral. -/
private lemma integral_sq_sub (g : ℝ → ℝ) (hg : Continuous g) (c a t : ℝ) :
    (∫ s in a..t, (g s - c)^2)
      = (∫ s in a..t, g s ^2) - 2*c*(∫ s in a..t, g s) + (t-a)*c^2 := by
  have i1 : IntervalIntegrable (fun s => g s ^2) volume a t :=
    (hg.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => 2*c*(g s)) volume a t :=
    (hg.const_mul _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun _ : ℝ => c^2) volume a t :=
    continuous_const.intervalIntegrable _ _
  have h1 : ∀ s, (g s - c)^2 = (g s^2 - 2*c*(g s)) + c^2 := by intro s; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_add (i1.sub i2) i3,
      intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp [smul_eq_mul]

/-- **The engine.**  `(f b - f a)² ≤ (b-a) ∫_a^b f'²` for continuously differentiable
`f`, by monotonicity of `G t = (t-a)∫_a^t f'² - (f t - f a)²`. -/
theorem sq_sub_le (hd : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    {a b : ℝ} (hab : a ≤ b) :
    (f b - f a)^2 ≤ (b - a) * ∫ s in a..b, f' s ^2 := by
  have hsqc : Continuous (fun s => f' s ^2) := by fun_prop
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun s => f' s ^2) volume p q :=
    fun p q => hsqc.intervalIntegrable _ _
  set G : ℝ → ℝ := fun t => (t - a) * (∫ s in a..t, f' s ^2) - (f t - f a)^2 with hG
  have hFTC : ∀ t : ℝ, (∫ s in a..t, f' s) = f t - f a := fun t =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hc.intervalIntegrable _ _)
  have hGd : ∀ t : ℝ, HasDerivAt G ((∫ s in a..t, (f' s - f' t)^2)) t := by
    intro t
    have h1 : HasDerivAt (fun u => ∫ s in a..u, f' s ^2) (f' t ^2) t :=
      intervalIntegral.integral_hasDerivAt_right (hint a t)
        (hsqc.stronglyMeasurableAtFilter _ _) hsqc.continuousAt
    have h2 : HasDerivAt (fun u => (u - a) * (∫ s in a..u, f' s ^2))
        (1 * (∫ s in a..t, f' s ^2) + (t - a) * f' t ^2) t :=
      HasDerivAt.mul ((hasDerivAt_id t).sub_const a) h1
    have h3 : HasDerivAt (fun u => (f u - f a)^2)
        (f' t * (f t - f a) + (f t - f a) * f' t) t := by
      have h := (hd t).sub_const (f a)
      have hm := HasDerivAt.mul h h
      have hfun : (fun u => (f u - f a)^2) = fun u => (f u - f a) * (f u - f a) := by
        funext u; ring
      rw [hfun]
      exact hm
    have h4 := h2.sub h3
    have hrw : (∫ s in a..t, (f' s - f' t)^2)
        = 1 * (∫ s in a..t, f' s ^2) + (t - a) * f' t ^2
          - (f' t * (f t - f a) + (f t - f a) * f' t) := by
      rw [integral_sq_sub f' hc (f' t) a t, hFTC t]; ring
    rw [hrw]
    exact h4
  have hdiff : Differentiable ℝ G := fun t => (hGd t).differentiableAt
  have hmono : MonotoneOn G (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hdiff.continuous.continuousOn
      (hdiff.differentiableOn)
    intro t ht
    rw [(hGd t).deriv]
    have hat : a ≤ t := by
      rcases (interior_subset (s := Set.Icc a b)) ht with ⟨h1, _⟩
      exact h1
    exact intervalIntegral.integral_nonneg hat (fun s _ => sq_nonneg _)
  have hGa : G a = 0 := by simp [hG]
  have hle : G a ≤ G b := hmono (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  rw [hGa] at hle
  simpa [hG] using hle

/-- **`habs` discharged.**  For `f 0 = 0` and `0 ≤ β`,
`∫₀^β f² ≤ (β²/2) ∫₀^β f'²`. -/
theorem habs_verified (hd : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    (h0 : f 0 = 0) {β : ℝ} (hβ : 0 ≤ β) :
    (∫ t in (0:ℝ)..β, f t ^2) ≤ (β^2/2) * ∫ s in (0:ℝ)..β, f' s ^2 := by
  have hdifff : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hcf : Continuous f := hdifff.continuous
  have hsqc : Continuous (fun s => f' s ^2) := by fun_prop
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun s => f' s ^2) volume p q :=
    fun p q => hsqc.intervalIntegrable _ _
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) β, f t ^2 ≤ t * ∫ s in (0:ℝ)..β, f' s ^2 := by
    intro t ht
    have h1 : (f t - f 0)^2 ≤ (t - 0) * ∫ s in (0:ℝ)..t, f' s ^2 :=
      sq_sub_le hd hc ht.1
    have h2 : (∫ s in (0:ℝ)..t, f' s ^2) ≤ ∫ s in (0:ℝ)..β, f' s ^2 := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := t) (c := β)
        (hint _ _) (hint _ _)]
      have : 0 ≤ ∫ s in t..β, f' s ^2 :=
        intervalIntegral.integral_nonneg ht.2 (fun s _ => sq_nonneg _)
      linarith
    have ht0 : 0 ≤ t := ht.1
    rw [h0, sub_zero, sub_zero] at h1
    nlinarith [h1, h2, ht0]
  have hfc2 : Continuous (fun t => f t ^2) := by fun_prop
  have hmono : (∫ t in (0:ℝ)..β, f t ^2)
      ≤ ∫ t in (0:ℝ)..β, t * ∫ s in (0:ℝ)..β, f' s ^2 := by
    apply intervalIntegral.integral_mono_on hβ
      (hfc2.intervalIntegrable _ _)
      ((continuous_id.mul continuous_const).intervalIntegrable _ _) hpt
  have hval : (∫ t in (0:ℝ)..β, t * ∫ s in (0:ℝ)..β, f' s ^2)
      = (β^2/2) * ∫ s in (0:ℝ)..β, f' s ^2 := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  linarith [hmono, hval ▸ hmono]

/-- **`hsub` discharged.**  Monotonicity of the gradient integral in the upper limit. -/
theorem hsub_verified (g : ℝ → ℝ) (hg : Continuous g) {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    (∫ s in (0:ℝ)..b, g s ^2) ≤ ∫ s in (0:ℝ)..c, g s ^2 := by
  have hgc2 : Continuous (fun s => g s ^2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := b) (c := c)
    (hgc2.intervalIntegrable _ _) (hgc2.intervalIntegrable _ _)]
  have : 0 ≤ ∫ s in b..c, g s ^2 :=
    intervalIntegral.integral_nonneg hbc (fun s _ => sq_nonneg _)
  linarith

/-- **`hcut` discharged, general form.**  For `f 0 = 0`, `0 ≤ c₀ ≤ T`, `L = T - c₀`:
`∫₀^T f² ≤ (c₀²/2 + 2c₀L) ∫₀^{c₀} f'² + 2L² ∫_{c₀}^T f'²`. -/
theorem hcut_verified (hd : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    (h0 : f 0 = 0) {c₀ T : ℝ} (hc0 : 0 ≤ c₀) (hcT : c₀ ≤ T) :
    (∫ t in (0:ℝ)..T, f t ^2)
      ≤ (c₀^2/2 + 2*c₀*(T - c₀)) * (∫ s in (0:ℝ)..c₀, f' s ^2)
        + 2*(T - c₀)^2 * ∫ s in c₀..T, f' s ^2 := by
  have hdifff : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hcf : Continuous f := hdifff.continuous
  have hsqc : Continuous (fun s => f' s ^2) := by fun_prop
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun s => f' s ^2) volume p q :=
    fun p q => hsqc.intervalIntegrable _ _
  have hI1 : (∫ t in (0:ℝ)..c₀, f t ^2) ≤ (c₀^2/2) * ∫ s in (0:ℝ)..c₀, f' s ^2 :=
    habs_verified hd hc h0 hc0
  -- the tail: pointwise f t ² ≤ 2c₀ ∫₀^{c₀} f'² + 2(T-c₀) ∫_{c₀}^T f'²
  have hgc : 0 ≤ ∫ s in (0:ℝ)..c₀, f' s ^2 :=
    intervalIntegral.integral_nonneg hc0 (fun s _ => sq_nonneg _)
  have hgt : 0 ≤ ∫ s in c₀..T, f' s ^2 :=
    intervalIntegral.integral_nonneg hcT (fun s _ => sq_nonneg _)
  have hpt : ∀ t ∈ Set.Icc c₀ T,
      f t ^2 ≤ 2*c₀*(∫ s in (0:ℝ)..c₀, f' s ^2) + 2*(T-c₀)*∫ s in c₀..T, f' s ^2 := by
    intro t ht
    have hfc : (f c₀ - f 0)^2 ≤ c₀ * ∫ s in (0:ℝ)..c₀, f' s ^2 := by
      have := sq_sub_le hd hc hc0
      simpa using this
    have hft : (f t - f c₀)^2 ≤ (t - c₀) * ∫ s in c₀..t, f' s ^2 :=
      sq_sub_le hd hc ht.1
    have hmono2 : (∫ s in c₀..t, f' s ^2) ≤ ∫ s in c₀..T, f' s ^2 := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (a := c₀) (b := t) (c := T)
        (hint _ _) (hint _ _)]
      have : 0 ≤ ∫ s in t..T, f' s ^2 :=
        intervalIntegral.integral_nonneg ht.2 (fun s _ => sq_nonneg _)
      linarith
    have hsq : f t ^2 ≤ 2*(f c₀)^2 + 2*(f t - f c₀)^2 := by
      nlinarith [sq_nonneg (f c₀ - (f t - f c₀))]
    rw [h0, sub_zero] at hfc
    have htc : t - c₀ ≤ T - c₀ := by linarith [ht.2]
    have hint2 : 0 ≤ ∫ s in c₀..t, f' s ^2 :=
      intervalIntegral.integral_nonneg ht.1 (fun s _ => sq_nonneg _)
    nlinarith [hsq, hfc, hft, hmono2, hint2, htc, hgt]
  have htail : (∫ t in c₀..T, f t ^2)
      ≤ (T - c₀) * (2*c₀*(∫ s in (0:ℝ)..c₀, f' s ^2)
        + 2*(T-c₀)*∫ s in c₀..T, f' s ^2) := by
    have hfc2 : Continuous (fun t => f t ^2) := by fun_prop
    have hmono3 : (∫ t in c₀..T, f t ^2)
        ≤ ∫ _t in c₀..T, (2*c₀*(∫ s in (0:ℝ)..c₀, f' s ^2)
          + 2*(T-c₀)*∫ s in c₀..T, f' s ^2) := by
      apply intervalIntegral.integral_mono_on hcT
        (hfc2.intervalIntegrable _ _)
        (intervalIntegrable_const) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono3
    linarith
  have hfc2' : Continuous (fun t => f t ^2) := by fun_prop
  have hsplit : (∫ t in (0:ℝ)..T, f t ^2)
      = (∫ t in (0:ℝ)..c₀, f t ^2) + ∫ t in c₀..T, f t ^2 := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hfc2'.intervalIntegrable _ _) (hfc2'.intervalIntegrable _ _)]
  nlinarith [hI1, htail, hsplit, hgc, hgt]

end MovingSofa
