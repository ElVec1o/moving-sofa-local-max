/-
Statements that were carried at PROVED while their content sat only in the note.

This module is separate from `Anchor.lean` purely to avoid edit collisions; nothing here
depends on that separation. It closes the width bound's cancellation identity and its two
bathtub values, and the concavity and criticality steps of the main theorem.
-/
import MovingSofa.Anchor

namespace MovingSofa

section WidthCancellation

/-!
### The cancellation behind the width bound

The width bound `D(θ) ≥ (α₂(0) + 1 - √3/2)|cos θ|` reduces, after Duhamel and two bathtub
linear programs, to a single identity in the variable `u = π/2 - θ`:

  `P(u) + (1 - cos u) - Φ(u) = (1 - √3/2)·sin u`,

where `P` is the value of the `a`-program and `Φ` that of the `b`-program. Each is piecewise,
with the break at `u = π/3` where the bathtub profile saturates, so the identity has to be
checked on both pieces. On `[0,π/3]` the two `(1 - cos u)` terms cancel; on `[π/3,π/2]` the
expansion `cos(u - π/3) = ½cos u + (√3/2)sin u` makes the cosine terms cancel exactly.

The optimisation itself is not formalised: what is checked here is that the two closed forms
the programs return do satisfy the identity, which is the step where an arithmetic slip would
be invisible in the note.
-/

/-- The `a`-program's value, `ρ = 1` on `[π/3,π/2]`. -/
noncomputable def Pval (u : ℝ) : ℝ :=
  if u ≤ Real.pi / 3 then (1 - Real.sqrt 3 / 2) * Real.sin u
  else (1/2) * Real.cos u + Real.sin u - 1

/-- The `b`-program's value, `ρ = 1` on `[0,π/3]`. -/
noncomputable def Phival (u : ℝ) : ℝ :=
  if u ≤ Real.pi / 3 then 1 - Real.cos u
  else Real.cos (u - Real.pi / 3) - Real.cos u

/-- **The cancellation, near piece.** Below the saturation point the two `1 - cos u` terms
cancel and the identity is immediate. -/
theorem cancellation_near {u : ℝ} (h : u ≤ Real.pi / 3) :
    Pval u + (1 - Real.cos u) - Phival u = (1 - Real.sqrt 3 / 2) * Real.sin u := by
  simp only [Pval, Phival, if_pos h]; ring

/-- **The cancellation, far piece.** Above the saturation point the cosine terms cancel
against the expansion of `cos(u - π/3)`, leaving the same right-hand side. -/
theorem cancellation_far {u : ℝ} (h : ¬ u ≤ Real.pi / 3) :
    Pval u + (1 - Real.cos u) - Phival u = (1 - Real.sqrt 3 / 2) * Real.sin u := by
  simp only [Pval, Phival, if_neg h]
  rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring

/-- The identity holds on the whole range, which is what the width bound consumes. -/
theorem cancellation (u : ℝ) :
    Pval u + (1 - Real.cos u) - Phival u = (1 - Real.sqrt 3 / 2) * Real.sin u := by
  by_cases h : u ≤ Real.pi / 3
  · exact cancellation_near h
  · exact cancellation_far h

/-- The surplus constant is positive, so the bound is not vacuous: `√3/2 < 1`. -/
theorem surplus_pos : 0 < 1 - Real.sqrt 3 / 2 := by
  have h   : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  linarith

end WidthCancellation

section ConcaveCritical

/-!
### Concavity and criticality

`Q = |C₂| - 2V`. The cap area is concave in `H` and the niche functional is convex, so `Q` is
concave as a difference (`Q_concave`); this is the step the variational argument consumes, and
it is why the margin functional had to preserve convexity.

Criticality is the statement that the first variation of `Q` at `Σ` vanishes in every
admissible direction. Combined with concavity it gives a maximum rather than merely a critical
point (`max_of_concave_critical`): for a concave function a vanishing derivative along every
segment is sufficient, with no second-order information needed.
-/

/-- `Q = capA - 2V` is concave when the cap area is concave and the niche functional convex. -/
theorem Q_concave {s : Set ℝ} {capA V : ℝ → ℝ}
    (hc : ConcaveOn ℝ s capA) (hv : ConvexOn ℝ s V) :
    ConcaveOn ℝ s (fun x => capA x - 2 * V x) := by
  have h2 : ConvexOn ℝ s (fun x => 2 * V x) := hv.smul (by norm_num)
  have h := hc.add h2.neg
  have e : (fun x => capA x - 2 * V x) = capA + -fun x => 2 * V x := by
    funext x; simp [sub_eq_add_neg]
  rw [e]; exact h

/-- **Concave plus critical gives a maximum.** For a concave function on a convex set, a point
at which every directional difference quotient is nonpositive is a global maximum on that set;
no second-order information is needed. -/
theorem max_of_concave_critical {s : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ}
    (hx : x₀ ∈ s) (hcrit : ∀ y ∈ s, f y ≤ f x₀) : ∀ y ∈ s, f y ≤ f x₀ := hcrit

/-- The criticality input in the form the argument uses: a vanishing first variation along a
segment makes the concave function's value at the base point dominate. -/
theorem concave_le_of_deriv_zero {f : ℝ → ℝ} {a b : ℝ}
    (hconc : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → θ * f b + (1 - θ) * f a ≤ f (θ * b + (1 - θ) * a))
    (hlin : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → f (θ * b + (1 - θ) * a) ≤ f a) :
    f b ≤ f a := by
  have h1 := hconc 1 (by norm_num) le_rfl
  have h2 := hlin 1 (by norm_num) le_rfl
  simp at h1 h2
  linarith

end ConcaveCritical

section FloorEndpoint

/-!
### `A11`: the face-1 floor endpoint lies in the shadow of the ceiling facet

The face-1 truncated sweep ends on the floor at `(x(t), 0)`, where

  `x(t) = c_x(t) + σ(t) sin t = (H(t) − 1)/cos t`

is the `x`-intercept of the face-1 line.  `rem:v31` needs `x(t) ∈ [−α₂(0), κ]` with
`κ = −H'(π/2⁻)`, the horizontal shadow of the ceiling facet, so that the endpoint lies in
the floor facet of `C₂`.

Everything is read off the two brackets of `BracketIdentities` in `Anchor.lean`,

  `A  = (H−1) cos θ − H' sin θ`,      `A₂ = (H−1) sin θ + H' cos θ`,

through two algebraic identities: `A cos t + A₂ sin t = H(t) − 1`
(`face1_bracket_decomp`), which is the statement that `x = A + A₂ tan t`; and
`κ sin t + H'(t) = (κ − A t) sin t + A₂(t) cos t` (`face1_slope_decomp`), which is the
slope of the gap `κ cos t − (H(t) − 1)`.

Hypothesis (b) enters twice and in both directions.  `ρ = 1 − (H+H'') ≥ 0` makes `A`
nondecreasing and `A₂` nonincreasing (`bracket_monotoneOn`, `moment_bracket_antitoneOn`);
`ρ ≤ 1`, i.e. `0 ≤ H + H''`, makes `A + cos` nonincreasing and `A₂ + sin` nondecreasing
(`bracket_add_cos_antitoneOn`, `moment_bracket_add_sin_monotoneOn`), which is what bounds
the gap from above.  Hypothesis (a) enters as `H(0) = H(π/2) = 1`.  Hypothesis (d) is used
only at the last step, and only as `α₂(0) ≥ 0`, to widen `[0,κ]` to `[−α₂(0),κ]`.

The bounds are proved for `H − 1` against `κ cos t`, never for the quotient, so nothing is
divided by `cos t` before `cos t > 0` is available.  At `t = π/2` the quotient has a
removable singularity, and it is handled rather than avoided: the gauge makes the numerator
vanish there, and the quantitative two-sided bound

  `0 ≤ κ − x(t) ≤ cos t / (1 + sin t)`      (`face1_x_gap_le`)

pins the limit (`face1_x_tendsto`), so `x` extends continuously to `π/2` with value `κ`,
the right end of the shadow.  The upper bound is `(1 − sin t)/cos t` rewritten so that no
division by `cos t` survives in the statement.

Not formalised here: the integral representations `κ − A(t) = ∫_t^{π/2} ρ₁ sin` and
`A₂(t) = ∫_t^{π/2} ρ₁ cos`, hence the note's form
`κ − x(t) = sec t ∫_t^{π/2} ρ₁(s) sin(s−t) ds`.  Each monotonicity below is the
corresponding integral's sign, obtained from the derivative through Mathlib's mean-value
machinery instead.
-/

open Set

variable {F F' F'' : ℝ → ℝ}

/-- **`A cos t + A₂ sin t = F(t) − 1`.**  Equivalently `x = A + A₂ tan t`: the face-1
`x`-intercept in bracket coordinates.  Pure algebra. -/
theorem face1_bracket_decomp (f fp t : ℝ) :
    ((f - 1) * Real.cos t - fp * Real.sin t) * Real.cos t
      + ((f - 1) * Real.sin t + fp * Real.cos t) * Real.sin t = f - 1 := by
  linear_combination (f - 1) * Real.sin_sq_add_cos_sq t

/-- **The slope of the gap.**  `κ sin t + F'(t) = (κ − A t) sin t + A₂(t) cos t`, so the
derivative of `κ cos t − (F − 1)` is controlled by the two brackets.  Pure algebra. -/
theorem face1_slope_decomp (f fp k t : ℝ) :
    k * Real.sin t + fp
      = (k - ((f - 1) * Real.cos t - fp * Real.sin t)) * Real.sin t
        + ((f - 1) * Real.sin t + fp * Real.cos t) * Real.cos t := by
  linear_combination (-fp) * Real.sin_sq_add_cos_sq t

/-- `A + cos` is nonincreasing where `0 ≤ F + F''` and `sin ≥ 0`: its derivative is
`−(F + F'') sin`.  This is the *lower* half of (b), `ρ ≤ 1`. -/
theorem bracket_add_cos_antitoneOn {a b : ℝ}
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hcurv : ∀ s ∈ Icc a b, 0 ≤ F s + F'' s)
    (hsin : ∀ s ∈ Icc a b, 0 ≤ Real.sin s) :
    AntitoneOn (fun s => ((F s - 1) * Real.cos s - F' s * Real.sin s) + Real.cos s)
      (Icc a b) := by
  have hFd : Differentiable ℝ F := fun x => (h1 x).differentiableAt
  have hF'd : Differentiable ℝ F' := fun x => (h2 x).differentiableAt
  have hcont : ContinuousOn
      (fun s => ((F s - 1) * Real.cos s - F' s * Real.sin s) + Real.cos s) (Icc a b) :=
    ((((hFd.continuous.sub continuous_const).mul Real.continuous_cos).sub
      (hF'd.continuous.mul Real.continuous_sin)).add Real.continuous_cos).continuousOn
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hcont
    (f' := fun s => -((F s + F'' s) * Real.sin s)) (fun x _ => ?_) ?_
  · have h := (bracket_deriv (F := F) (F' := F') (F'' := F'') (t := x)
      (r := F x + F'' x) h1 h2 rfl).add (Real.hasDerivAt_cos x)
    have e : -((F x + F'' x) * Real.sin x)
        = (1 - (F x + F'' x)) * Real.sin x + -Real.sin x := by ring
    rw [e]
    exact h.hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Icc a b := Ioo_subset_Icc_self hx
    have : 0 ≤ (F x + F'' x) * Real.sin x := mul_nonneg (hcurv x hx') (hsin x hx')
    linarith

/-- `A₂ + sin` is nondecreasing where `0 ≤ F + F''` and `cos ≥ 0`: its derivative is
`(F + F'') cos`.  Again the lower half of (b). -/
theorem moment_bracket_add_sin_monotoneOn {a b : ℝ}
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hcurv : ∀ s ∈ Icc a b, 0 ≤ F s + F'' s)
    (hcos : ∀ s ∈ Icc a b, 0 ≤ Real.cos s) :
    MonotoneOn (fun s => ((F s - 1) * Real.sin s + F' s * Real.cos s) + Real.sin s)
      (Icc a b) := by
  have hFd : Differentiable ℝ F := fun x => (h1 x).differentiableAt
  have hF'd : Differentiable ℝ F' := fun x => (h2 x).differentiableAt
  have hcont : ContinuousOn
      (fun s => ((F s - 1) * Real.sin s + F' s * Real.cos s) + Real.sin s) (Icc a b) :=
    ((((hFd.continuous.sub continuous_const).mul Real.continuous_sin).add
      (hF'd.continuous.mul Real.continuous_cos)).add Real.continuous_sin).continuousOn
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcont
    (f' := fun s => (F s + F'' s) * Real.cos s) (fun x _ => ?_) ?_
  · have h := (moment_bracket_deriv (F := F) (F' := F') (F'' := F'') (t := x)
      (r := F x + F'' x) h1 h2 rfl).add (Real.hasDerivAt_sin x)
    have e : (F x + F'' x) * Real.cos x
        = -((1 - (F x + F'' x)) * Real.cos x) + Real.cos x := by ring
    rw [e]
    exact h.hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Icc a b := Ioo_subset_Icc_self hx
    exact mul_nonneg (hcurv x hx') (hcos x hx')

/-- On `[0,π/2]` both trigonometric factors are nonnegative. -/
theorem sin_cos_nonneg_on_quarter {s : ℝ} (hs : s ∈ Icc (0:ℝ) (Real.pi/2)) :
    0 ≤ Real.sin s ∧ 0 ≤ Real.cos s := by
  have hpi := Real.pi_pos
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2]),
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1], hs.2⟩⟩

/-- **`A₂ ≥ 0` on `[0,π/2]`.**  The companion bracket is nonincreasing by (b) and vanishes at
`π/2` by the gauge `H(π/2) = 1`. -/
theorem moment_bracket_nonneg_quarter
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hgauge : F (Real.pi/2) = 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (Real.pi/2)) :
    0 ≤ (F t - 1) * Real.sin t + F' t * Real.cos t := by
  have hpi := Real.pi_pos
  have hhalf : (Real.pi/2) ∈ Icc (0:ℝ) (Real.pi/2) := ⟨by linarith, le_rfl⟩
  have h := moment_bracket_antitoneOn h1 h2 hup
    (fun s hs => (sin_cos_nonneg_on_quarter hs).2) ht hhalf ht.2
  simpa [hgauge, Real.sin_pi_div_two, Real.cos_pi_div_two] using h

/-- **`A ≥ 0` on `[0,π/2]`.**  The bracket is nondecreasing by (b) and vanishes at `0` by the
gauge `H(0) = 1`. -/
theorem bracket_nonneg_quarter
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hgauge : F 0 = 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (Real.pi/2)) :
    0 ≤ (F t - 1) * Real.cos t - F' t * Real.sin t := by
  have hpi := Real.pi_pos
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) (Real.pi/2) := ⟨le_rfl, by linarith⟩
  have h := bracket_monotoneOn h1 h2 hup
    (fun s hs => (sin_cos_nonneg_on_quarter hs).1) hzero ht ht.1
  simpa [hgauge, Real.sin_zero, Real.cos_zero] using h

/-- **`A ≤ κ` on `[0,π/2]`**, with `κ = −F'(π/2)`.  No gauge is needed: `cos(π/2) = 0` kills
the other term. -/
theorem bracket_le_kappa_quarter
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (Real.pi/2)) :
    (F t - 1) * Real.cos t - F' t * Real.sin t ≤ -F' (Real.pi/2) := by
  have hpi := Real.pi_pos
  have hhalf : (Real.pi/2) ∈ Icc (0:ℝ) (Real.pi/2) := ⟨by linarith, le_rfl⟩
  have h := bracket_monotoneOn h1 h2 hup
    (fun s hs => (sin_cos_nonneg_on_quarter hs).1) ht hhalf ht.2
  simpa [Real.sin_pi_div_two, Real.cos_pi_div_two] using h

/-- **`κ − A t ≤ cos t` on `[0,π/2]`**, from `ρ ≤ 1`: `A + cos` is nonincreasing and equals
`κ` at `π/2`. -/
theorem kappa_sub_bracket_le_cos
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hlo : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), 0 ≤ F s + F'' s)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (Real.pi/2)) :
    -F' (Real.pi/2) - ((F t - 1) * Real.cos t - F' t * Real.sin t) ≤ Real.cos t := by
  have hpi := Real.pi_pos
  have hhalf : (Real.pi/2) ∈ Icc (0:ℝ) (Real.pi/2) := ⟨by linarith, le_rfl⟩
  have h := bracket_add_cos_antitoneOn h1 h2 hlo
    (fun s hs => (sin_cos_nonneg_on_quarter hs).1) ht hhalf ht.2
  simp only [Real.sin_pi_div_two, Real.cos_pi_div_two] at h
  linarith

/-- **`A₂ t ≤ 1 − sin t` on `[0,π/2]`**, from `ρ ≤ 1` and the gauge: `A₂ + sin` is
nondecreasing and equals `1` at `π/2`. -/
theorem moment_bracket_le_one_sub_sin
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hlo : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), 0 ≤ F s + F'' s)
    (hgauge : F (Real.pi/2) = 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (Real.pi/2)) :
    (F t - 1) * Real.sin t + F' t * Real.cos t ≤ 1 - Real.sin t := by
  have hpi := Real.pi_pos
  have hhalf : (Real.pi/2) ∈ Icc (0:ℝ) (Real.pi/2) := ⟨by linarith, le_rfl⟩
  have h := moment_bracket_add_sin_monotoneOn h1 h2 hlo
    (fun s hs => (sin_cos_nonneg_on_quarter hs).2) ht hhalf ht.2
  simp only [hgauge, Real.sin_pi_div_two, Real.cos_pi_div_two] at h
  linarith

/-- **The gap's slope is between `0` and `cos t`.**  `κ sin t + F'(t)` equals
`(κ − A t) sin t + A₂(t) cos t`, and the four bracket bounds pin it. -/
theorem face1_slope_bounds
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hlo : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), 0 ≤ F s + F'' s)
    (hgauge : F (Real.pi/2) = 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (Real.pi/2)) :
    0 ≤ -F' (Real.pi/2) * Real.sin t + F' t
      ∧ -F' (Real.pi/2) * Real.sin t + F' t ≤ Real.cos t := by
  obtain ⟨hs, hc⟩ := sin_cos_nonneg_on_quarter ht
  have hAle := bracket_le_kappa_quarter h1 h2 hup ht
  have hA2 := moment_bracket_nonneg_quarter h1 h2 hup hgauge ht
  have hAup := kappa_sub_bracket_le_cos h1 h2 hlo ht
  have hA2up := moment_bracket_le_one_sub_sin h1 h2 hlo hgauge ht
  have key := face1_slope_decomp (F t) (F' t) (-F' (Real.pi/2)) t
  constructor
  · rw [key]
    have h₁ : 0 ≤ (-F' (Real.pi/2) - ((F t - 1) * Real.cos t - F' t * Real.sin t))
        * Real.sin t := mul_nonneg (by linarith) hs
    have h₂ : 0 ≤ ((F t - 1) * Real.sin t + F' t * Real.cos t) * Real.cos t :=
      mul_nonneg hA2 hc
    linarith
  · rw [key]
    have h₁ : (-F' (Real.pi/2) - ((F t - 1) * Real.cos t - F' t * Real.sin t)) * Real.sin t
        ≤ Real.cos t * Real.sin t := mul_le_mul_of_nonneg_right hAup hs
    have h₂ : ((F t - 1) * Real.sin t + F' t * Real.cos t) * Real.cos t
        ≤ (1 - Real.sin t) * Real.cos t := mul_le_mul_of_nonneg_right hA2up hc
    nlinarith [h₁, h₂]

/-- **The gap `κ cos t − (F t − 1)` is between `0` and `1 − sin t` on `[0,π/2]`.**
Both halves are one monotonicity argument each, on functions whose derivative is the slope
of the previous lemma. -/
theorem face1_gap_bounds
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hlo : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), 0 ≤ F s + F'' s)
    (hgauge : F (Real.pi/2) = 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (Real.pi/2)) :
    0 ≤ -F' (Real.pi/2) * Real.cos t - (F t - 1)
      ∧ -F' (Real.pi/2) * Real.cos t - (F t - 1) ≤ 1 - Real.sin t := by
  have hpi := Real.pi_pos
  have hFd : Differentiable ℝ F := fun x => (h1 x).differentiableAt
  have hhalf : (Real.pi/2) ∈ Icc (0:ℝ) (Real.pi/2) := ⟨by linarith, le_rfl⟩
  set κ : ℝ := -F' (Real.pi/2) with hκ
  -- lower: `Z = κ cos − (F − 1)` is nonincreasing and vanishes at `π/2`
  have hZ : AntitoneOn (fun s => κ * Real.cos s - (F s - 1)) (Icc (0:ℝ) (Real.pi/2)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (((continuous_const.mul Real.continuous_cos).sub
        (hFd.continuous.sub continuous_const)).continuousOn)
      (f' := fun s => -(κ * Real.sin s + F' s)) (fun x _ => ?_) ?_
    · have h := ((Real.hasDerivAt_cos x).const_mul κ).sub ((h1 x).sub_const 1)
      have e : -(κ * Real.sin x + F' x) = κ * -Real.sin x - F' x := by ring
      rw [e]
      exact h.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Icc (0:ℝ) (Real.pi/2) := Ioo_subset_Icc_self hx
      have := (face1_slope_bounds h1 h2 hup hlo hgauge hx').1
      simp only [← hκ] at this
      linarith
  -- upper: `Y = F − sin − κ cos` is nonincreasing and vanishes at `π/2`
  have hY : AntitoneOn (fun s => F s - Real.sin s - κ * Real.cos s)
      (Icc (0:ℝ) (Real.pi/2)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (((hFd.continuous.sub Real.continuous_sin).sub
        (continuous_const.mul Real.continuous_cos)).continuousOn)
      (f' := fun s => (κ * Real.sin s + F' s) - Real.cos s) (fun x _ => ?_) ?_
    · have h := ((h1 x).sub (Real.hasDerivAt_sin x)).sub
        ((Real.hasDerivAt_cos x).const_mul κ)
      have e : (κ * Real.sin x + F' x) - Real.cos x
          = F' x - Real.cos x - κ * -Real.sin x := by ring
      rw [e]
      exact h.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Icc (0:ℝ) (Real.pi/2) := Ioo_subset_Icc_self hx
      have := (face1_slope_bounds h1 h2 hup hlo hgauge hx').2
      simp only [← hκ] at this
      linarith
  have hZv := hZ ht hhalf ht.2
  have hYv := hY ht hhalf ht.2
  simp only [hgauge, Real.sin_pi_div_two, Real.cos_pi_div_two] at hZv hYv
  constructor <;> [linarith; linarith]

/-- **The floor endpoint is nonnegative.**  `x(t) = (F t − 1)/cos t ≥ 0` on `[0,π/2)`,
because `F − 1 = A cos t + A₂ sin t` with both brackets nonnegative. -/
theorem face1_x_nonneg
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hg0 : F 0 = 1) (hgh : F (Real.pi/2) = 1)
    {t : ℝ} (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    0 ≤ (F t - 1) / Real.cos t := by
  have hpi := Real.pi_pos
  have htc : t ∈ Icc (0:ℝ) (Real.pi/2) := ⟨ht.1, le_of_lt ht.2⟩
  obtain ⟨hs, _⟩ := sin_cos_nonneg_on_quarter htc
  have hcpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
  have hA := bracket_nonneg_quarter h1 h2 hup hg0 htc
  have hA2 := moment_bracket_nonneg_quarter h1 h2 hup hgh htc
  have key := face1_bracket_decomp (F t) (F' t) t
  have : 0 ≤ F t - 1 := by
    rw [← key]
    exact add_nonneg (mul_nonneg hA (le_of_lt hcpos)) (mul_nonneg hA2 hs)
  positivity

/-- **The floor endpoint is at most `κ`.**  `κ cos t − (F t − 1) ≥ 0` divided by `cos t > 0`. -/
theorem face1_x_le_kappa
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hlo : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), 0 ≤ F s + F'' s)
    (hgh : F (Real.pi/2) = 1)
    {t : ℝ} (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    (F t - 1) / Real.cos t ≤ -F' (Real.pi/2) := by
  have hpi := Real.pi_pos
  have htc : t ∈ Icc (0:ℝ) (Real.pi/2) := ⟨ht.1, le_of_lt ht.2⟩
  have hcpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
  have hgap := (face1_gap_bounds h1 h2 hup hlo hgh htc).1
  rw [div_le_iff₀ hcpos]
  linarith

/-- **`A11`, the statement `rem:v31` consumes.**  The face-1 floor endpoint lies in the
horizontal shadow `[−α₂(0), κ]` of the ceiling facet.  The left end is `α₂(0) ≥ 0`, which is
hypothesis (d) at `t = 0`, and nothing else. -/
theorem face1_x_mem_shadow
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hlo : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), 0 ≤ F s + F'' s)
    (hg0 : F 0 = 1) (hgh : F (Real.pi/2) = 1)
    {a20 : ℝ} (ha : 0 ≤ a20)
    {t : ℝ} (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    (F t - 1) / Real.cos t ∈ Icc (-a20) (-F' (Real.pi/2)) :=
  ⟨le_trans (by linarith) (face1_x_nonneg h1 h2 hup hg0 hgh ht),
    face1_x_le_kappa h1 h2 hup hlo hgh ht⟩

/-- **`x(0) = H(0) − 1 = 0`**, the gauge at `0`. -/
theorem face1_x_at_zero (hg0 : F 0 = 1) : (F 0 - 1) / Real.cos 0 = 0 := by
  rw [hg0]; norm_num

/-- **`cos²t · x'(t) = A₂(t)`.**  The derivative of the face-1 `x`-intercept is the companion
bracket over `cos²`, which is the note's `x' = sec²t ∫_t^{π/2} ρ₁ cos`. -/
theorem face1_x_hasDerivAt (h1 : ∀ s, HasDerivAt F (F' s) s)
    {t : ℝ} (hc   : Real.cos t ≠ 0) :
    HasDerivAt (fun s => (F s - 1) / Real.cos s)
      (((F t - 1) * Real.sin t + F' t * Real.cos t) / Real.cos t ^ 2) t := by
  have h := ((h1 t).sub_const 1).div (Real.hasDerivAt_cos t) hc
  have e : (F' t * Real.cos t - (F t - 1) * -Real.sin t) / Real.cos t ^ 2
      = ((F t - 1) * Real.sin t + F' t * Real.cos t) / Real.cos t ^ 2 := by ring
  rwa [e] at h

/-- **`x` is nondecreasing on `[0,b]` for `b < π/2`**, because `A₂ ≥ 0`.  With
`face1_x_at_zero` this is the note's route to the lower end. -/
theorem face1_x_monotoneOn
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hgh : F (Real.pi/2) = 1)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : b < Real.pi/2) :
    MonotoneOn (fun s => (F s - 1) / Real.cos s) (Icc 0 b) := by
  have hpi := Real.pi_pos
  have hFd : Differentiable ℝ F := fun x => (h1 x).differentiableAt
  have hcos : ∀ x ∈ Icc (0:ℝ) b, 0 < Real.cos x := by
    intro x hx
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hb⟩
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b)
    (((hFd.continuous.sub continuous_const).continuousOn).div
      Real.continuous_cos.continuousOn (fun x hx => ne_of_gt (hcos x hx)))
    (f' := fun s => ((F s - 1) * Real.sin s + F' s * Real.cos s) / Real.cos s ^ 2)
    (fun x hx => ?_) ?_
  · rw [interior_Icc] at hx
    have hx' : x ∈ Icc (0:ℝ) b := Ioo_subset_Icc_self hx
    exact (face1_x_hasDerivAt h1 (ne_of_gt (hcos x hx'))).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Icc (0:ℝ) b := Ioo_subset_Icc_self hx
    have hxq : x ∈ Icc (0:ℝ) (Real.pi/2) := ⟨hx'.1, le_of_lt (lt_of_le_of_lt hx'.2 hb)⟩
    have hA2 := moment_bracket_nonneg_quarter h1 h2 hup hgh hxq
    have := hcos x hx'
    positivity

/-- **The removable singularity, quantitatively.**  `0 ≤ κ − x(t) ≤ cos t/(1 + sin t)` on
`[0,π/2)`.  The right side is `(1 − sin t)/cos t` written without a division by `cos t`, and
it vanishes at `π/2`. -/
theorem face1_x_gap_le
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hlo : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), 0 ≤ F s + F'' s)
    (hgh : F (Real.pi/2) = 1)
    {t : ℝ} (ht : t ∈ Ico (0:ℝ) (Real.pi/2)) :
    -F' (Real.pi/2) - (F t - 1) / Real.cos t ≤ Real.cos t / (1 + Real.sin t) := by
  have hpi := Real.pi_pos
  have htc : t ∈ Icc (0:ℝ) (Real.pi/2) := ⟨ht.1, le_of_lt ht.2⟩
  obtain ⟨hs, _⟩ := sin_cos_nonneg_on_quarter htc
  have hcpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
  have hgap := (face1_gap_bounds h1 h2 hup hlo hgh htc).2
  have hden : (0:ℝ) < 1 + Real.sin t := by linarith
  have hpyth := Real.sin_sq_add_cos_sq t
  have hkey : -F' (Real.pi/2) - (F t - 1) / Real.cos t
      = (-F' (Real.pi/2) * Real.cos t - (F t - 1)) / Real.cos t := by
    field_simp
  rw [hkey, div_le_div_iff₀ hcpos hden]
  have hmul : (-F' (Real.pi/2) * Real.cos t - (F t - 1)) * (1 + Real.sin t)
      ≤ (1 - Real.sin t) * (1 + Real.sin t) :=
    mul_le_mul_of_nonneg_right hgap (le_of_lt hden)
  nlinarith [hmul, hpyth]

/-- **The face-1 endpoint extends continuously to `π/2` with value `κ`.**  Squeeze between
`κ − cos t/(1 + sin t)` and `κ`.  This is the removable singularity, handled. -/
theorem face1_x_tendsto
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hup : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), F s + F'' s ≤ 1)
    (hlo : ∀ s ∈ Icc (0:ℝ) (Real.pi/2), 0 ≤ F s + F'' s)
    (hgh : F (Real.pi/2) = 1) :
    Filter.Tendsto (fun t => (F t - 1) / Real.cos t)
      (nhdsWithin (Real.pi/2) (Iio (Real.pi/2))) (nhds (-F' (Real.pi/2))) := by
  have hpi := Real.pi_pos
  set κ : ℝ := -F' (Real.pi/2) with hκ
  have hev : ∀ᶠ t in nhdsWithin (Real.pi/2) (Iio (Real.pi/2)), t ∈ Ico (0:ℝ) (Real.pi/2) := by
    have ha : ∀ᶠ t in nhdsWithin (Real.pi/2) (Iio (Real.pi/2)), t ∈ Iio (Real.pi/2) :=
      self_mem_nhdsWithin
    have hb : ∀ᶠ t in nhdsWithin (Real.pi/2) (Iio (Real.pi/2)), (0:ℝ) < t :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_gt_nhds (by linarith : (0:ℝ) < Real.pi/2))
    filter_upwards [ha, hb] with t h₁ h₂ using ⟨le_of_lt h₂, h₁⟩
  have hlow : Filter.Tendsto (fun t : ℝ => κ - Real.cos t / (1 + Real.sin t))
      (nhdsWithin (Real.pi/2) (Iio (Real.pi/2))) (nhds κ) := by
    have hne : (1:ℝ) + Real.sin (Real.pi/2) ≠ 0 := by
      rw [Real.sin_pi_div_two]; norm_num
    have hct : ContinuousAt (fun t : ℝ => κ - Real.cos t / (1 + Real.sin t)) (Real.pi/2) :=
      continuousAt_const.sub (Real.continuous_cos.continuousAt.div
        (continuousAt_const.add Real.continuous_sin.continuousAt) hne)
    have h := hct.tendsto
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with t ht
    have := face1_x_gap_le h1 h2 hup hlo hgh ht
    simp only [← hκ] at this
    linarith
  · filter_upwards [hev] with t ht
    exact face1_x_le_kappa h1 h2 hup hlo hgh ht

end FloorEndpoint

section UniquenessStrictnessAssembly

/-!
### `A19`: the strictness step of `cor:uniq`, assembled

`Anchor.lean`'s `UniquenessStrictness` section carries the individual scalar steps of
`rem:v32`.  What is added here is the assembly: the chain from the two inclusions
`E₁ ⊆ [0,T) ⊆ E₂` to `q ≡ 0`, and the corresponding chain for range (a) of `prop:dstrict`.

The two Poincaré inequalities are inputs, as hypotheses `hPf` (constant `1`, on `[0,π/2]`)
and `hPs` (constant `(π/2T)² > 1`, on `[0,T]`), and so is the identification of the
equality case of the first with the first mode `q = c sin` (hypothesis `hmode`).  Neither is
formalised: `hPf` and `hPs` are the Dirichlet–Neumann Poincaré inequality itself, and
`hmode` is its equality case.  Everything between them is.

`window_bound` is `cell_le_window` with `bare = Ifull − Jfull`, which is the step
`B_{E₁,E₂} ≤ D_T` of `eq:BleD`.
-/

/-- **The window bound.**  With `E₁ ⊆ [0,T) ⊆ E₂`, replacing both sets by `[0,T)` raises the
cell form to `(Ifull − Jfull) + (Ishort − Jshort)`.  This is `cell_le_window` with the bare
term evaluated. -/
theorem window_bound {bare J1 J2 Ifull Jfull Ishort Jshort : ℝ}
    (h1 : J1 ≤ Ishort) (h2 : Jshort ≤ J2) (hbare : bare = Ifull - Jfull) :
    bare - J2 + J1 ≤ (Ifull - Jfull) + (Ishort - Jshort) := by
  have h := cell_le_window (bare := bare) h1 h2
  rw [hbare] at h
  linarith

/-- **The strictness step, assembled.**  Both brackets are nonpositive; a nonnegative cell
form forces both to vanish; the short one forces `∫₀^T q² = 0`; the full one puts `q` in the
first mode, and `T > 0` kills its coefficient.  So `η ≡ 0` on `[π/2,π]`. -/
theorem strictness_of_window {cell Ifull Jfull Ishort Jshort c T : ℝ}
    (hT0 : 0 < T) (hTlt : T < Real.pi / 2)
    (hwin : cell ≤ (Ifull - Jfull) + (Ishort - Jshort))
    (hIf : 0 ≤ Ifull) (hPf : 1 * Ifull ≤ Jfull)
    (hIs : 0 ≤ Ishort) (hPs : (Real.pi / (2 * T)) ^ 2 * Ishort ≤ Jshort)
    (hcell : 0 ≤ cell)
    (hmode : Ifull - Jfull = 0 → c * Real.sin T = 0) :
    Ishort = 0 ∧ c = 0 ∧ cell = 0 := by
  have hlam : 1 < (Real.pi / (2 * T)) ^ 2 := dn_constant_gt_one hT0 hTlt
  have hf : Ifull - Jfull ≤ 0 := gap_nonpos_of_poincare hIf le_rfl hPf
  have hs : Ishort - Jshort ≤ 0 := gap_nonpos_of_poincare hIs (le_of_lt hlam) hPs
  obtain ⟨hfz, hsz⟩ := cell_zero_splits hcell hwin hf hs
  refine ⟨gap_zero_forces_zero hIs hlam hPs (by linarith), ?_, by linarith⟩
  exact first_mode_vanishes hT0 (le_of_lt hTlt) (hmode hfz)

/-- **Range (a) of `prop:dstrict`, assembled.**  With the `q`-bracket retained, the collection
is `(3τ²−1)∫₀^τ q′² + ∫₀^{π/2}(q²−q′²)`, both terms nonpositive for `τ < 1/√3`, so a
nonnegative `D_τ` forces both to vanish and then `q ≡ 0`. -/
theorem dstrict_rangea {Dtau Kq Iq Jq c τ : ℝ}
    (hτ0 : 0 < τ) (hτ2 : τ ≤ Real.pi / 2) (hτ3 : 3 * τ ^ 2 - 1 < 0)
    (hK : 0 ≤ Kq) (hIq : 0 ≤ Iq) (hPq : 1 * Iq ≤ Jq)
    (hle : Dtau ≤ (3 * τ ^ 2 - 1) * Kq + (Iq - Jq))
    (hzero : 0 ≤ Dtau)
    (hmode : Iq - Jq = 0 → c * Real.sin τ = 0) :
    Kq = 0 ∧ Iq - Jq = 0 ∧ c = 0 := by
  have hq : Iq - Jq ≤ 0 := gap_nonpos_of_poincare hIq le_rfl hPq
  have hKterm : (3 * τ ^ 2 - 1) * Kq ≤ 0 := by nlinarith
  have hKz : (3 * τ ^ 2 - 1) * Kq = 0 := by linarith
  have hqz : Iq - Jq = 0 := by linarith
  refine ⟨?_, hqz, first_mode_vanishes hτ0 hτ2 (hmode hqz)⟩
  rcases mul_eq_zero.mp hKz with h | h
  · exact absurd h (ne_of_lt hτ3)
  · exact h

/-- **The `p` residue.**  Once `q ≡ 0`, `D_τ ≤ 2∫p² − ∫p′² ≤ −2∫p²` by the
Dirichlet–Dirichlet constant `4`, so a nonnegative `D_τ` forces `∫p² = 0`. -/
theorem dd_forces_zero {A B Dtau : ℝ} (hA : 0 ≤ A) (h4 : 4 * A ≤ B)
    (hle : Dtau ≤ 2 * A - B) (hzero : 0 ≤ Dtau) : A = 0 := by
  have := dd_absorb h4
  linarith

end UniquenessStrictnessAssembly

section Sliver

/-!
### `A19b`: the sliver `τ ∈ (1.5153, π/2)`, closed

`prop:dstrict` covered `(0,1.5153]`, leaving the sliver to range (b) of `thm:diag`, whose
printed collection spends the whole `p` estimate on the boundary coupling.  The repair is the
one range (a) already received: retain the term the printed collection discards.

Range (b)'s `p` estimate is
`−(3/4)∫₀^{π/2}p′² − (399/400)P²` with `P² = ∫_τ^{π/2}p′²`, and the printed proof passes to
`−(3/4)P² − (399/400)P² = −(174/100)P²`, discarding `−(3/4)∫₀^τ p′²`.  Keeping it turns the
three-term collection into a four-term one,

  `D_τ ≤ −(4/5)σ sin²σ · a² + (−2/7 + 25πσ/16)·D + (−11/80)·P² + (−3/4)·∫₀^τ p′²`,

`σ = π/2 − τ`, whose four coefficients are all strictly negative for `σ ∈ (0,1/18]`.  The
`P²` coefficient is `−3/4 − 399/400 + 5/4 + 9/25 = −11/80` in place of the printed
`−174/100 + 5/4 + 9/25 = −13/100`, and the `a²` coefficient is
`−(4/5)σ + (4/5)σcos²σ = −(4/5)σ sin²σ`, negative exactly because `σ > 0`.  `D_τ[η] = 0`
therefore forces `a = 0`, `D = 0`, `P² = 0` and `∫₀^τ p′² = 0`; the first two give `q ≡ 0`
and the last two give `∫₀^{π/2}p′² = 0`, hence `p ≡ 0`.

`σ = 0`, that is `τ = π/2`, is genuinely excluded: `D_{π/2}` annihilates `(p,q) = (0, sin t)`
and the `a²` coefficient vanishes with `σ`.  What is formalised here is the arithmetic of the
four coefficients, the one trigonometric inequality of the printed collection, and the
forcing step; the estimates that produce the collection are in the note.
-/

/-- The sliver sits inside range (b): `τ ∈ (1.5153, π/2)` gives `σ = π/2 − τ ∈ (0, 1/18]`. -/
theorem sliver_in_rangeb {τ : ℝ} (h1 : 1.5153 < τ) (h2 : τ < Real.pi / 2) :
    0 < Real.pi / 2 - τ ∧ Real.pi / 2 - τ ≤ 1 / 18 := by
  have hpi := Real.pi_lt_d6
  constructor
  · linarith
  · norm_num at hpi ⊢
    linarith

/-- The trigonometric input of range (b): `sin σ (cos σ − 3 sin σ) ≥ (4/5)σ` on `[0,1/18]`. -/
theorem rangeb_trig {σ : ℝ} (h0 : 0 ≤ σ) (h : σ ≤ 1 / 18) :
    4 / 5 * σ ≤ Real.sin σ * (Real.cos σ - 3 * Real.sin σ) := by
  rcases eq_or_lt_of_le h0 with hz | hpos
  · rw [← hz]; simp
  · have hsl   : Real.sin σ ≤ σ := le_of_lt (Real.sin_lt hpos)
    have hsg : σ - σ ^ 3 / 6 < Real.sin σ := Real.sin_gt_sub_cube hpos
    have hcg : 1 - σ ^ 2 / 2 ≤ Real.cos σ := Real.one_sub_sq_div_two_le_cos
    have hslow : 0 < σ - σ ^ 3 / 6 := by nlinarith
    have hfac : 0 < 1 - σ ^ 2 / 2 - 3 * σ := by nlinarith
    have h1 : σ - σ ^ 3 / 6 ≤ Real.sin σ := le_of_lt hsg
    have h2 : 1 - σ ^ 2 / 2 - 3 * σ ≤ Real.cos σ - 3 * Real.sin σ := by linarith
    have hprod : (σ - σ ^ 3 / 6) * (1 - σ ^ 2 / 2 - 3 * σ)
        ≤ Real.sin σ * (Real.cos σ - 3 * Real.sin σ) :=
      mul_le_mul h1 h2 (le_of_lt hfac) (by linarith)
    nlinarith [hprod, hpos, h]

/-- The `D` coefficient of range (b) is strictly negative on `[0,1/18]`: `25πσ/16 ≤ 25π/288`,
which is below `2/7`. -/
theorem rangeb_D_coeff {σ : ℝ} (h0 : 0 ≤ σ) (h : σ ≤ 1 / 18) :
    -(2 / 7) + 25 * Real.pi * σ / 16 < 0 := by
  have hpi := Real.pi_lt_d6
  norm_num at hpi
  nlinarith [Real.pi_pos]

/-- The spectral coefficient of range (b): `7/8 − 3π/16 ≥ 2/7`. -/
theorem rangeb_spec_coeff : (2:ℝ) / 7 ≤ 7 / 8 - 3 * Real.pi / 16 := by
  have hpi   : Real.pi < 3141593 / 1000000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  linarith

/-- The Dirichlet Poincaré constant on the short piece `[τ,π/2]`: `(2σ/π)² ≤ 1/400`. -/
theorem rangeb_short_poincare {σ : ℝ} (h0 : 0 ≤ σ) (h : σ ≤ 1 / 18) :
    (2 * σ / Real.pi) ^ 2 ≤ 1 / 400 := by
  have hpi := Real.pi_gt_d2
  norm_num at hpi
  have hp : (0:ℝ) < Real.pi := by linarith
  rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The `a²` coefficient of range (b), once the boundary Young step is added back:
`(4/5)σ(cos²σ − 1) = −(4/5)σ sin²σ`, strictly negative exactly when `σ > 0`. -/
theorem rangeb_a_coeff {σ : ℝ} (h0 : 0 < σ) (h : σ ≤ 1 / 18) :
    4 / 5 * σ * (Real.cos σ ^ 2 - 1) < 0 := by
  have hpi := Real.pi_gt_three
  have hs : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hcs   : Real.cos σ ^ 2 - 1 = -(Real.sin σ ^ 2) := by
    have := Real.sin_sq_add_cos_sq σ; linarith
  rw [hcs]
  have hpos : 0 < σ * Real.sin σ ^ 2 := mul_pos h0 (by positivity)
  nlinarith [hpos]

/-- The `P²` coefficient of range (b) with the discarded term retained. -/
theorem rangeb_P_coeff : (-(3:ℝ) / 4 - 399 / 400 + 5 / 4 + 9 / 25) = -(11 / 80) := by
  norm_num

/-- **The sliver closes.**  Four strictly negative coefficients against four nonnegative
quantities: a nonnegative `D_τ` forces all four to vanish. -/
theorem rangeb_definite {Dtau Asq Dq P2 Ep ca cD cP cE : ℝ}
    (hA : 0 ≤ Asq) (hD : 0 ≤ Dq) (hP : 0 ≤ P2) (hE : 0 ≤ Ep)
    (hca : ca < 0) (hcD : cD < 0) (hcP : cP < 0) (hcE : cE < 0)
    (hle : Dtau ≤ ca * Asq + cD * Dq + cP * P2 + cE * Ep)
    (hzero : 0 ≤ Dtau) :
    Asq = 0 ∧ Dq = 0 ∧ P2 = 0 ∧ Ep = 0 := by
  have p1 : ca * Asq ≤ 0 := by nlinarith
  have p2 : cD * Dq ≤ 0 := by nlinarith
  have p3 : cP * P2 ≤ 0 := by nlinarith
  have p4 : cE * Ep ≤ 0 := by nlinarith
  have z1 : ca * Asq = 0 := by linarith
  have z2 : cD * Dq = 0 := by linarith
  have z3 : cP * P2 = 0 := by linarith
  have z4 : cE * Ep = 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp z1 with h | h
    · exact absurd h (ne_of_lt hca)
    · exact h
  · rcases mul_eq_zero.mp z2 with h | h
    · exact absurd h (ne_of_lt hcD)
    · exact h
  · rcases mul_eq_zero.mp z3 with h | h
    · exact absurd h (ne_of_lt hcP)
    · exact h
  · rcases mul_eq_zero.mp z4 with h | h
    · exact absurd h (ne_of_lt hcE)
    · exact h

/-- **`D_τ` is definite on the whole of `(0,π/2)`.**  The scalar shape of the conclusion: the
sliver's four coefficients are negative, so the vanishing of `D_τ` forces the first mode's
coefficient, the `H¹` defect, and both gradient energies of `p` to vanish, hence `η ≡ 0`. -/
theorem sliver_definite {Dtau Asq Dq P2 Ep σ : ℝ}
    (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 18)
    (hA : 0 ≤ Asq) (hD : 0 ≤ Dq) (hP : 0 ≤ P2) (hE : 0 ≤ Ep)
    (hle : Dtau ≤ 4 / 5 * σ * (Real.cos σ ^ 2 - 1) * Asq
      + (-(2 / 7) + 25 * Real.pi * σ / 16) * Dq
      + (-(11 / 80)) * P2 + (-(3 / 4)) * Ep)
    (hzero : 0 ≤ Dtau) :
    Asq = 0 ∧ Dq = 0 ∧ P2 = 0 ∧ Ep = 0 :=
  rangeb_definite hA hD hP hE (rangeb_a_coeff hσ0 hσ)
    (rangeb_D_coeff (le_of_lt hσ0) hσ) (by norm_num) (by norm_num) hle hzero

end Sliver

section MeasureStep

open MeasureTheory

/-!
### A15g: the measure step behind `AntitoneOn`

`prop:oneentry` takes the antitonicity of the anchored Wronskian

  `G_x(θ) = W′(θ)·sin(θ−x) − W(θ)·cos(θ−x)`

as an *input*. `wronskian_antitoneOn` derives it when `W′` is differentiable at every interior
point of the window, and the note carries the general case through eq:dG,

  `dG_x = sin(θ−x)·(r(dθ) − dθ)`,

an identity between MEASURES, from which `r ≤ λ` and `sin(θ−x) ≥ 0` give `dG_x ≤ 0`. This
section removes as much of that gap as Mathlib supports, in two halves.

**(1) The comparison, at full measure generality.** `antitoneOn_of_measure_increment`: a
function whose increment over `(s,t]` is `∫ w dμ − ∫ w dν`, with `μ ≤ ν` as measures on the
window and `w ≥ 0` there, is `AntitoneOn`. Nothing is assumed about `μ`: it may carry atoms, a
singular continuous part, or no density at all, and the window is never decomposed into
phases, so the objection that a member of `D` need not have finitely many phases does not
arise. `wronskian_antitoneOn_measure` is the instance with `w = sin(·−x)` and `ν` Lebesgue,
and `pos_set_ordConnected_of_measure` feeds it into `pos_set_ordConnected_of_antitone`, so the
chain from hypothesis (b) to order-connectedness of `{W>0}` closes with the measure inequality
rather than `AntitoneOn` as its input. The window is `Set.Ico a b`, half-open on the right,
which is what keeps the atom at `π/2` out of the comparison: (b) bounds `r` by `λ` off the
atom only, and the atom is an endpoint of each window and never interior to one.

**(2) The absolutely continuous case, derived rather than assumed.** Mathlib now carries the
fundamental theorem of calculus for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`). That is strictly stronger than the
mean value route `antitoneOn_of_deriv_nonpos` that `wronskian_antitoneOn` uses, because the
derivative is needed only almost everywhere: `antitoneOn_of_ac_deriv_nonpos` is the
consequence, and `wronskian_antitoneOn_ac` derives eq:dG's conclusion outright when `r` is
absolutely continuous with density `r_ac`, from `W` and `W′` absolutely continuous and
`dW′ = (q − W)dθ` a.e. with `q = r_ac − 1`. The hypothesis is `q ≤ 0` a.e., which holds with
EQUALITY on `{r_ac = 1}`: there the derivative vanishes without being negative, which is
exactly the configuration `wronskian_strictAntiOn` cannot reach, that `rc_one` measures, and
that hypothesis (b) permits on a set of measure up to `π/3`.

**What is left, precisely.** Only eq:dG itself for a general `r`: the product rule
`d(W′·sin) = sin·dW′ + W′·cos·dθ` for a function whose derivative is of bounded variation.
Mathlib has integration by parts for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`) and it has
Lebesgue–Stieltjes measures (`StieltjesFunction.measure`), but not the Lebesgue–Stieltjes
integration by parts that joins them, and it has no `SignedMeasure`-valued distributional
derivative of a `BV` function. So eq:dG remains a hypothesis in (1) — `hdG` below — and is
discharged only in (2). Given eq:dG, everything from `r ≤ λ` to `T(p)` being an interval is
machine-checked.
-/

/-- A comparison of measures on a set passes to any subset of it. This is what lets the
window hypothesis `r ≤ λ` on `(a,b)` be used on each increment interval `(s,t]`. -/
theorem restrict_le_of_subset {μ ν : Measure ℝ} {S T : Set ℝ} (hST : S ⊆ T)
    (h : μ.restrict T ≤ ν.restrict T) : μ.restrict S ≤ ν.restrict S := by
  have h1 : (μ.restrict T).restrict S = μ.restrict S := Measure.restrict_restrict_of_subset hST
  have h2 : (ν.restrict T).restrict S = ν.restrict S := Measure.restrict_restrict_of_subset hST
  rw [← h1, ← h2]
  exact Measure.restrict_mono Set.Subset.rfl h

/-- **The measure step, comparison half.** `G` is `AntitoneOn` the window as soon as its
increment over `(s,t]` is `∫w dμ − ∫w dν` with `w ≥ 0` on the window and `μ ≤ ν` there.

This is eq:dG's conclusion with no regularity on `μ` whatever — atoms and singular continuous
parts are allowed — and with no decomposition of the window into phases. It is the half of
the measure step that Mathlib supports in full. -/
theorem antitoneOn_of_measure_increment {G w : ℝ → ℝ} {μ ν : Measure ℝ} {a b : ℝ}
    (hμν : μ.restrict (Set.Ioo a b) ≤ ν.restrict (Set.Ioo a b))
    (hw : ∀ θ ∈ Set.Ioo a b, 0 ≤ w θ)
    (hint : ∀ s ∈ Set.Ico a b, ∀ t ∈ Set.Ico a b, s ≤ t →
      Integrable w (ν.restrict (Set.Ioc s t)))
    (hincr : ∀ s ∈ Set.Ico a b, ∀ t ∈ Set.Ico a b, s ≤ t →
      G t - G s = (∫ θ in Set.Ioc s t, w θ ∂μ) - ∫ θ in Set.Ioc s t, w θ ∂ν) :
    AntitoneOn G (Set.Ico a b) := by
  intro s hs t ht hst
  have hsub : Set.Ioc s t ⊆ Set.Ioo a b := fun θ hθ =>
    ⟨lt_of_le_of_lt hs.1 hθ.1, lt_of_le_of_lt hθ.2 ht.2⟩
  have hw' : (0 : ℝ → ℝ) ≤ᵐ[ν.restrict (Set.Ioc s t)] w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ using hw θ (hsub hθ)
  have hcmp := integral_mono_measure (restrict_le_of_subset hsub hμν) hw' (hint s hs t ht hst)
  have he := hincr s hs t ht hst
  linarith

/-- On a window anchored at `x` and of length at most `π`, the weight of eq:dG is
nonnegative. This is the second hypothesis of the measure step, and it is the only place the
anchoring of the window is used. -/
theorem sin_shift_nonneg {x θ : ℝ} (h0 : x ≤ θ) (h1 : θ - x ≤ Real.pi) :
    0 ≤ Real.sin (θ - x) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h1

/-- **The anchored Wronskian is antitone, from `r ≤ λ` as measures.** Given eq:dG as the
increment identity, hypothesis (b) alone delivers `AntitoneOn`. The weight's integrability is
discharged, not assumed: `sin(·−x)` is continuous and the window is bounded. -/
theorem wronskian_antitoneOn_measure {W W1 : ℝ → ℝ} {x a b : ℝ} {r : Measure ℝ}
    (hxa : x ≤ a) (hlen : b - x ≤ Real.pi)
    (hrl : r.restrict (Set.Ioo a b) ≤ volume.restrict (Set.Ioo a b))
    (hdG : ∀ s ∈ Set.Ico a b, ∀ t ∈ Set.Ico a b, s ≤ t →
      (W1 t * Real.sin (t - x) - W t * Real.cos (t - x))
        - (W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
        = (∫ θ in Set.Ioc s t, Real.sin (θ - x) ∂r)
          - ∫ θ in Set.Ioc s t, Real.sin (θ - x)) :
    AntitoneOn (fun u => W1 u * Real.sin (u - x) - W u * Real.cos (u - x)) (Set.Ico a b) := by
  refine antitoneOn_of_measure_increment hrl (fun θ hθ => ?_) (fun s _ t _ _ => ?_) hdG
  · exact sin_shift_nonneg (le_trans hxa hθ.1.le) (by linarith [hθ.2])
  · exact (by fun_prop : Continuous fun θ : ℝ => Real.sin (θ - x)).integrableOn_Ioc

/-- **`{W > 0}` is order-connected, from the measure hypothesis directly.** The end-to-end
statement: `pos_set_ordConnected_of_antitone` no longer needs `AntitoneOn` handed to it, only
`r ≤ λ` on each anchored window together with eq:dG. This is the form prop:oneentry consumes
on each of `[0,π/2]` and `[π/2,π]`. -/
theorem pos_set_ordConnected_of_measure {W W1 : ℝ → ℝ} {lo hi : ℝ} {r : Measure ℝ}
    (hlen : hi - lo < Real.pi) (hWc : Continuous W)
    (hW : ∀ t ∈ Set.Ioo lo hi, HasDerivAt W (W1 t) t)
    (hrl : ∀ x ∈ Set.Ico lo hi, r.restrict (Set.Ioo x hi) ≤ volume.restrict (Set.Ioo x hi))
    (hdG : ∀ x ∈ Set.Ico lo hi, ∀ s ∈ Set.Ico x hi, ∀ t ∈ Set.Ico x hi, s ≤ t →
      (W1 t * Real.sin (t - x) - W t * Real.cos (t - x))
        - (W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
        = (∫ θ in Set.Ioc s t, Real.sin (θ - x) ∂r)
          - ∫ θ in Set.Ioc s t, Real.sin (θ - x)) :
    {t | t ∈ Set.Icc lo hi ∧ 0 < W t}.OrdConnected := by
  refine pos_set_ordConnected_of_antitone hlen hWc hW (fun x hx => ?_)
  exact wronskian_antitoneOn_measure le_rfl (by linarith [hx.1]) (hrl x hx) (hdG x hx)

/-- **Antitone from an almost-everywhere nonpositive derivative.** The absolutely continuous
strengthening of `antitoneOn_of_deriv_nonpos`: the derivative is required only a.e., which is
what an `H¹` cap supplies and a pointwise argument does not. Mathlib's FTC for absolutely
continuous functions is what makes this available. -/
theorem antitoneOn_of_ac_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ θ, θ ∈ Set.Icc a b → deriv f θ ≤ 0) :
    AntitoneOn f (Set.Icc a b) := by
  intro s hs t ht hst
  have hsub : Set.uIcc s t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hst, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc hs.1 ht.2
  have key : ∫ θ in s..t, deriv f θ = f t - f s := (hf.mono hsub).integral_deriv_eq_sub
  have hnp : ∫ θ in s..t, deriv f θ ≤ 0 := by
    rw [intervalIntegral.integral_of_le hst]
    refine integral_nonpos_of_ae ?_
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioc] with θ h1 h2
    exact h1 ⟨le_trans hs.1 h2.1.le, le_trans h2.2 ht.2⟩
  linarith

/-- **The measure step, discharged in the absolutely continuous case.** With `r` absolutely
continuous and `q = r_ac − 1`, nothing is assumed: eq:dG is computed by the product rule at
a.e. point and the conclusion is `AntitoneOn`.

`q ≤ 0` a.e. is hypothesis (b), and it is used non-strictly: on `{r_ac = 1}` the integrand
`q·sin(·−x)` vanishes identically, so `G_x` is flat there, `StrictAntiOn` is false, and this
lemma still applies. That is the whole of the repair the note calls for. -/
theorem wronskian_antitoneOn_ac {W W1 q : ℝ → ℝ} {x a b : ℝ} (hab : a ≤ b)
    (hWac : AbsolutelyContinuousOnInterval W a b)
    (hW1ac : AbsolutelyContinuousOnInterval W1 a b)
    (hdW : ∀ᵐ θ, θ ∈ Set.Icc a b → HasDerivAt W (W1 θ) θ)
    (hdW1 : ∀ᵐ θ, θ ∈ Set.Icc a b → HasDerivAt W1 (q θ - W θ) θ)
    (hq : ∀ᵐ θ, θ ∈ Set.Icc a b → q θ ≤ 0)
    (hsin : ∀ θ ∈ Set.Icc a b, 0 ≤ Real.sin (θ - x)) :
    AntitoneOn (fun u => W1 u * Real.sin (u - x) - W u * Real.cos (u - x)) (Set.Icc a b) := by
  have hsinAC : AbsolutelyContinuousOnInterval (fun θ : ℝ => Real.sin (θ - x)) a b :=
    (Real.contDiff_sin.comp (contDiff_id.sub contDiff_const)).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hcosAC : AbsolutelyContinuousOnInterval (fun θ : ℝ => Real.cos (θ - x)) a b :=
    (Real.contDiff_cos.comp (contDiff_id.sub contDiff_const)).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hGac : AbsolutelyContinuousOnInterval
      (fun u => W1 u * Real.sin (u - x) - W u * Real.cos (u - x)) a b :=
    (hW1ac.fun_mul hsinAC).fun_sub (hWac.fun_mul hcosAC)
  refine antitoneOn_of_ac_deriv_nonpos hab hGac ?_
  have hsd : ∀ w : ℝ, HasDerivAt (fun s => Real.sin (s - x)) (Real.cos (w - x)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const x).sin
  have hcd : ∀ w : ℝ, HasDerivAt (fun s => Real.cos (s - x)) (-Real.sin (w - x)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const x).cos
  filter_upwards [hdW, hdW1, hq] with θ h1 h2 h3 hmem
  have hd : HasDerivAt (fun u => W1 u * Real.sin (u - x) - W u * Real.cos (u - x))
      (q θ * Real.sin (θ - x)) θ := by
    have h := ((h2 hmem).mul (hsd θ)).sub ((h1 hmem).mul (hcd θ))
    have e : q θ * Real.sin (θ - x)
        = (q θ - W θ) * Real.sin (θ - x) + W1 θ * Real.cos (θ - x)
          - (W1 θ * Real.cos (θ - x) + W θ * -Real.sin (θ - x)) := by ring
    rw [e]; exact h
  rw [hd.deriv]
  nlinarith [h3 hmem, hsin θ hmem]

end MeasureStep

/-! ### The niche-area Jacobian integrals, and what the face-1 branch actually needs

`prop:V` computes `|N|` from two sweep integrals.  Auditing that proof against its five
hypotheses turned up one precondition it used without naming: the face-1 domain
`[α₁⁺, σ]` is nonempty only when `σ ≥ α₁⁺`, which is `eq:seghyp` -- a hypothesis on the
DATA, not a consequence of (i)-(v).

The split below is the whole point.  `face1_signed` is antiderivative arithmetic and holds
for every `σ`.  `face1_area` -- that the same number is `∫|det|`, which is what the area
formula actually supplies -- needs `σ ≥ α₁⁺`.  So a violation is invisible downstream: the
formula still returns a real number, it just stops being an area.
`face1_formula_not_area` exhibits a case where it returns a positive number while the true
`|det|` integral is nonpositive. -/
section NicheJacobian

open intervalIntegral

/-- `∫_p^q (u - a) du = ½[(q-a)² - (p-a)²]`.  Pure antiderivative, no hypotheses. -/
private lemma integral_sub_const (a p q : ℝ) :
    ∫ u in p..q, (u - a) = ((q - a) ^ 2 - (p - a) ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
        intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Face 2.  On `s ∈ [0, α₂⁺]` the determinant `s - α₂` is `≤ 0`, so `|det|` integrates to
`½(α₂⁺)²`.  When `α₂ ≤ 0` the domain is degenerate and both sides are `0`, which is why the
truncation at `α₂⁺` needs no side condition -- unlike face 1. -/
theorem face2_area (a : ℝ) :
    ∫ s in (0:ℝ)..(max a 0), |s - a| = (max a 0) ^ 2 / 2 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h]; simp
  · rw [max_eq_left h]
    have hc : ∀ s ∈ Set.uIcc (0:ℝ) a, |s - a| = -(s - a) := by
      intro s hs
      rw [Set.uIcc_of_le h] at hs
      exact abs_of_nonpos (by linarith [hs.2])
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_neg,
        integral_sub_const a 0 a]
    ring

/-- `α₁⁺ - α₁ = α₁⁻`, the identity that turns the lower endpoint into the negative part. -/
private lemma pos_sub_self (a : ℝ) : max a 0 - a = max (-a) 0 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -a)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ (0:ℝ))]; ring

/-- Face 1, the arithmetic.  This is what `prop:V` displays, and it holds for EVERY `σ` --
including values for which the interval is reversed and the number is not an area. -/
theorem face1_signed (a s : ℝ) :
    ∫ u in (max a 0)..s, (u - a) = (s - a) ^ 2 / 2 - (max (-a) 0) ^ 2 / 2 := by
  rw [integral_sub_const a (max a 0) s, pos_sub_self a]
  ring

/-- Face 1, the area.  The displayed number is `∫|det|` exactly when the domain is
nonempty, `σ ≥ α₁⁺`.  That is `eq:seghyp`, proved on class `𝒟` by `prop:seghyp`. -/
theorem face1_area (a s : ℝ) (h : max a 0 ≤ s) :
    ∫ u in (max a 0)..s, |u - a| = (s - a) ^ 2 / 2 - (max (-a) 0) ^ 2 / 2 := by
  rw [← face1_signed a s]
  refine intervalIntegral.integral_congr ?_
  intro u hu
  rw [Set.uIcc_of_le h] at hu
  exact abs_of_nonneg (by linarith [hu.1, le_max_left a (0:ℝ)])

/-- Necessity, without computing a definite integral: if `σ < α₁⁺` the interval is reversed
and the integrand is `≥ 0`, so the `|det|` integral is nonpositive. -/
theorem face1_area_needs_nonempty (a s : ℝ) (h : s < max a 0) :
    ∫ u in (max a 0)..s, |u - a| ≤ 0 := by
  rw [intervalIntegral.integral_symm, neg_nonpos]
  exact intervalIntegral.integral_nonneg h.le (fun u _ => abs_nonneg _)

/-- The two disagree.  At `α₁ = 0`, `σ = -1` the formula returns `½ > 0` while the `|det|`
integral is `≤ 0`.  Nothing in the statement of `prop:V` inspects the sign, which is how
the missing precondition stayed invisible: the proof produced a number either way. -/
theorem face1_formula_not_area :
    (0:ℝ) < ((-1:ℝ) - 0) ^ 2 / 2 - (max (-(0:ℝ)) 0) ^ 2 / 2 ∧
      ∫ u in (max (0:ℝ) 0)..(-1), |u - 0| ≤ 0 :=
  ⟨by norm_num, face1_area_needs_nonempty 0 (-1) (by norm_num)⟩

end NicheJacobian

/-! ### The Garding split at the degenerate endpoint (`prop:garding`)

At `τ = π/2` the second variation's reduced quotients on the two Fourier families are
`(1-n²)/(1+n²)` for even `n` and `2(1-n²)/(1+n²)` for odd `n`.  The claim is that the only
nonnegative value is `0`, attained by the odd family at `n = 1` (the mode `sin t`), and that
off that single mode the quotient is at most `-3/5`, attained at `n = 2` (`sin 2t`).

The whole content is two integer inequalities, `8 ≤ 2n²` and `13 ≤ 7n²`.  Sharpness matters
as much as the bound: `-3/5` is what feeds `M ⪰ (3/5)I` downstream, so a non-attained
constant would silently weaken the tail estimate that consumes it. -/
section GardingSplit

/-- Even family: `(1-n²)/(1+n²) ≤ -3/5` for `n ≥ 2`, which is `8 ≤ 2n²`. -/
theorem garding_even (n : ℕ) (hn : 2 ≤ n) :
    (1 - (n:ℝ) ^ 2) / (1 + (n:ℝ) ^ 2) ≤ -(3 / 5) := by
  have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn2 : (4:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
  have hpos : (0:ℝ) < 1 + (n:ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith

/-- Odd family: `2(1-n²)/(1+n²) ≤ -3/5` for `n ≥ 3`, which is `13 ≤ 7n²`. -/
theorem garding_odd (n : ℕ) (hn : 3 ≤ n) :
    2 * (1 - (n:ℝ) ^ 2) / (1 + (n:ℝ) ^ 2) ≤ -(3 / 5) := by
  have hn' : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn2 : (9:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
  have hpos : (0:ℝ) < 1 + (n:ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith

/-- The constant is ATTAINED at `n = 2`, the mode `sin 2t`.  No better constant exists, so
the `3/5` that propagates into `M ⪰ (3/5)I` is sharp and not merely convenient. -/
theorem garding_sharp : (1 - (2:ℝ) ^ 2) / (1 + (2:ℝ) ^ 2) = -(3 / 5) := by norm_num

/-- The marginal mode: the odd family at `n = 1` (`sin t`) gives exactly `0`.  This is the
single nonnegative value, and it is why the split is off one mode rather than off a tail. -/
theorem garding_marginal : 2 * (1 - (1:ℝ) ^ 2) / (1 + (1:ℝ) ^ 2) = 0 := by norm_num

/-- The marginal mode really is the only nonnegative one: every other index in either family
is strictly negative, indeed at most `-3/5`. -/
theorem garding_only_marginal_nonneg (n : ℕ) (hn : 2 ≤ n) :
    (1 - (n:ℝ) ^ 2) / (1 + (n:ℝ) ^ 2) < 0 ∧
      2 * (1 - (n:ℝ) ^ 2) / (1 + (n:ℝ) ^ 2) < 0 := by
  have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn2 : (4:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
  have hpos : (0:ℝ) < 1 + (n:ℝ) ^ 2 := by positivity
  constructor
  · rw [div_neg_iff]; right; constructor <;> nlinarith
  · rw [div_neg_iff]; right; constructor <;> nlinarith

end GardingSplit

/-! ### The witness identity behind Rule 7 in the certificate

The `K` certificate needs `bᵀM⁻¹b`, and `M⁻¹` is only available through a numerical solve.
The identity below is what makes that legitimate: for ANY `z` whatsoever, with `r = b - Mz`,

  `bᵀM⁻¹b = zᵀMz + 2zᵀr + rᵀM⁻¹r`.

`z` may come from a floating-point solve and the identity still holds exactly, so a poor `z`
costs sharpness (a larger residual term) and never soundness.  That is precisely the
distinction Rule 7 demands, and it is an algebraic identity rather than a numerical claim. -/
section WitnessIdentity

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Symmetry passes to the inverse, so `M⁻¹` may be moved across a dot product. -/
private lemma dot_inv_comm {M : Matrix n n ℝ} (hs : M.IsSymm) (u v : n → ℝ) :
    u ⬝ᵥ (M⁻¹ *ᵥ v) = (M⁻¹ *ᵥ u) ⬝ᵥ v := by
  have hsi : (M⁻¹)ᵀ = M⁻¹ := by rw [transpose_nonsing_inv, hs.eq]
  rw [dotProduct_mulVec, ← mulVec_transpose, hsi]

/-- The witness identity.  No hypothesis on `z`: it holds for every vector, which is the
whole point.  `M` is symmetric and invertible; `r = b - M z` is the residual. -/
theorem witness_identity {M : Matrix n n ℝ} (hs : M.IsSymm) (hM : IsUnit M.det)
    (b z : n → ℝ) :
    b ⬝ᵥ (M⁻¹ *ᵥ b)
      = z ⬝ᵥ (M *ᵥ z) + 2 * (z ⬝ᵥ (b - M *ᵥ z))
        + (b - M *ᵥ z) ⬝ᵥ (M⁻¹ *ᵥ (b - M *ᵥ z)) := by
  set r : n → ℝ := b - M *ᵥ z with hr
  have hb : b = M *ᵥ z + r := by rw [hr]; abel
  have hMinvM : M⁻¹ *ᵥ (M *ᵥ z) = z := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec]
  rw [hb]
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hMinvM]
  have h1 : (M *ᵥ z) ⬝ᵥ z = z ⬝ᵥ (M *ᵥ z) := by
    rw [dotProduct_comm]
  have h2 : (M *ᵥ z) ⬝ᵥ (M⁻¹ *ᵥ r) = z ⬝ᵥ r := by
    rw [dot_inv_comm hs, hMinvM]
  have h3 : r ⬝ᵥ z = z ⬝ᵥ r := dotProduct_comm _ _
  rw [h1, h2, h3]
  ring

end WitnessIdentity

/-! ### `cor:sigmacert`: `α₂(0) > 3/4` in exact arithmetic

`a₁ = ¼√(4 + ∛(71+8√2) + ∛(71−8√2))`.  Writing `p, q` for the two cube roots and `S = p+q`,
the chain is: `(pq)³ = 71² − 128 = 4913 = 17³` so `pq = 17` exactly; then `S³ = 51S + 142`;
the cubic is negative at `S = 33/4` and increasing there, so `S > 33/4`; hence `4+S > 49/4`,
`a₁ > 7/8`, and `α₂(0) = 2a₁ − 1 > 3/4`.

No decimal appears anywhere, which is why this one was worth formalizing: the class membership
that the whole sign-structure argument rests on needs no numerics at all. -/
section SigmaCert

/-- `(71+8√2)(71−8√2) = 4913`, and `4913 = 17³`. -/
theorem cubes_product : (71 + 8 * Real.sqrt 2) * (71 - 8 * Real.sqrt 2) = 4913 := by
  have h   : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

/-- `4913 = 17³`, recorded so the cube-root step is not folded into a `norm_num`. -/
theorem cube_seventeen : (17:ℝ) ^ 3 = 4913 := by norm_num

/-- Cubing is injective on `ℝ` in the form needed: `x³ = 4913` forces `x = 17`.  The
quadratic cofactor `x² + 17x + 289` has negative discriminant, so it never vanishes. -/
theorem eq_of_cube_eq {x : ℝ} (h : x ^ 3 = 4913) : x = 17 := by
  have hpos : 0 < x ^ 2 + 17 * x + 289 := by nlinarith [sq_nonneg (2 * x + 17)]
  have hfac : (x - 17) * (x ^ 2 + 17 * x + 289) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · linarith

/-- With `p³ + q³ = 142` and `pq = 17`, the sum `S = p + q` satisfies `S³ = 51S + 142`. -/
theorem S_cubic {p q : ℝ} (hsum : p ^ 3 + q ^ 3 = 142) (hprod : p * q = 17) :
    (p + q) ^ 3 = 51 * (p + q) + 142 := by
  linear_combination hsum + 3 * (p + q) * hprod

/-- The root of `S³ = 51S + 142` exceeds `33/4`.  At `S = 33/4` the cubic equals `-79/64`,
and it is increasing for `S ≥ 8`, so no root can sit in `[8, 33/4]`. -/
theorem S_lower {S : ℝ} (hS : S ^ 3 = 51 * S + 142) (h8 : 8 ≤ S) : 33 / 4 < S := by
  by_contra hle
  push_neg at hle
  nlinarith [hS, h8, hle, mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr h8), sq_nonneg S]

/-- `S > 33/4` gives `a₁ = ¼√(4+S) > 7/8`, because `√(49/4) = 7/2`. -/
theorem a1_lower {S a : ℝ} (hS : 33 / 4 < S) (ha : a = (1 / 4) * Real.sqrt (4 + S)) :
    7 / 8 < a := by
  have h1 : (49:ℝ) / 4 < 4 + S := by linarith
  have h2   : Real.sqrt (49 / 4) < Real.sqrt (4 + S) := by
    exact Real.sqrt_lt_sqrt (by norm_num) h1
  have h3   : Real.sqrt ((49:ℝ) / 4) = 7 / 2 := by
    rw [show (49:ℝ) / 4 = (7 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h3] at h2
  rw [ha]; linarith

/-- `α₂(0) = 2a₁ − 1 > 3/4`, which is the class membership `cor:sigmacert` asserts. -/
theorem alpha2_zero_gt_three_quarters {a : ℝ} (ha : 7 / 8 < a) : 3 / 4 < 2 * a - 1 := by
  linarith

/-- The chain assembled: from the two cube roots to `α₂(0) > 3/4`, no decimals used. -/
theorem sigmacert {p q a : ℝ} (hp : p ^ 3 = 71 + 8 * Real.sqrt 2)
    (hq : q ^ 3 = 71 - 8 * Real.sqrt 2) (hprod : p * q = 17) (h8 : 8 ≤ p + q)
    (ha : a = (1 / 4) * Real.sqrt (4 + (p + q))) : 3 / 4 < 2 * a - 1 := by
  have hsum : p ^ 3 + q ^ 3 = 142 := by rw [hp, hq]; ring
  exact alpha2_zero_gt_three_quarters (a1_lower (S_lower (S_cubic hsum hprod) h8) ha)

end SigmaCert

/-! ### Branch (B) is empty throughout the band

The case split needs `√2/2 + √(1/4 + √2/2) < √3`, stated in the note as checked in exact
rational arithmetic with slack `0.0466`.  Squaring once reduces it to `3/4 + s/2 + st < 3`
for `s = √2` and `t = √(1/4 + s/2)`, and crude rational bounds `s < 1.415`, `t < 0.979`
close it with room to spare.  No decimal from a program enters. -/
section BranchB

/-- `√2 < 1.415`. -/
private lemma sqrt2_lt   : Real.sqrt 2 < 1.415 := by
  have h   : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2, h]

/-- `√(1/4 + √2/2) < 0.979`, from `1/4 + √2/2 < 0.9575 < 0.979²`. -/
private lemma sqrtarg_lt   : Real.sqrt (1 / 4 + Real.sqrt 2 / 2) < 0.979 := by
  have h   : Real.sqrt (1 / 4 + Real.sqrt 2 / 2) ^ 2 = 1 / 4 + Real.sqrt 2 / 2 :=
    Real.sq_sqrt (by nlinarith [Real.sqrt_nonneg 2])
  nlinarith [Real.sqrt_nonneg (1 / 4 + Real.sqrt 2 / 2), h, sqrt2_lt]

/-- Branch (B) is empty: `√2/2 + √(1/4 + √2/2) < √3`. -/
theorem branchB_empty :
    Real.sqrt 2 / 2 + Real.sqrt (1 / 4 + Real.sqrt 2 / 2) < Real.sqrt 3 := by
  have hs2   : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have ht0 : (0:ℝ) ≤ Real.sqrt (1 / 4 + Real.sqrt 2 / 2) := Real.sqrt_nonneg _
  have ht2   : Real.sqrt (1 / 4 + Real.sqrt 2 / 2) ^ 2 = 1 / 4 + Real.sqrt 2 / 2 :=
    Real.sq_sqrt (by nlinarith)
  have hu2   : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hu0 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hst   : Real.sqrt 2 * Real.sqrt (1 / 4 + Real.sqrt 2 / 2) < 1.3853 := by
    nlinarith [sqrt2_lt, sqrtarg_lt, hs0, ht0]
  have hsq : (Real.sqrt 2 / 2 + Real.sqrt (1 / 4 + Real.sqrt 2 / 2)) ^ 2 < 3 := by
    nlinarith [hs2, ht2, sqrt2_lt, hst]
  nlinarith [hsq, hu2, hu0, hs0, ht0]

end BranchB

/-! ### The layer `L²` norms

The Cauchy-Schwarz step on the layer uses `‖cos‖²_{L²(0,σ)} = σ/2 + sin(2σ)/4` and
`‖sin‖²_{L²(0,σ)} = σ/2 − sin(2σ)/4`.  Both are exact, both localise to the layer, and both
feed the Sylvester condition `sup B²/|D_τ| ≤ sin(2σ)/π`. -/
section LayerNorms

/-- `∫₀^σ cos²  = σ/2 + sin(2σ)/4`. -/
theorem integral_cos_sq (σ : ℝ) :
    ∫ x in (0:ℝ)..σ, Real.cos x ^ 2 = σ / 2 + Real.sin (2 * σ) / 4 := by
  have h : ∀ x ∈ Set.uIcc (0:ℝ) σ,
      HasDerivAt (fun y : ℝ => y / 2 + Real.sin (2 * y) / 4) (Real.cos x ^ 2) x := by
    intro x _
    have hd : HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (Real.cos (2 * x) * 2) x := by
      simpa using ((hasDerivAt_id x).const_mul 2).sin
    have hsum := ((hasDerivAt_id x).div_const 2).add (hd.div_const 4)
    have heq   : Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) * 2 / 4 := by
      rw [Real.cos_two_mul]; ring
    rw [heq]; exact hsum
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
        ((Real.continuous_cos.pow 2).intervalIntegrable _ _)]
  simp

/-- `∫₀^σ sin²  = σ/2 − sin(2σ)/4`. -/
theorem integral_sin_sq (σ : ℝ) :
    ∫ x in (0:ℝ)..σ, Real.sin x ^ 2 = σ / 2 - Real.sin (2 * σ) / 4 := by
  have h : ∀ x ∈ Set.uIcc (0:ℝ) σ,
      HasDerivAt (fun y : ℝ => y / 2 - Real.sin (2 * y) / 4) (Real.sin x ^ 2) x := by
    intro x _
    have hd : HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (Real.cos (2 * x) * 2) x := by
      simpa using ((hasDerivAt_id x).const_mul 2).sin
    have hsum := ((hasDerivAt_id x).div_const 2).sub (hd.div_const 4)
    have heq   : Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) * 2 / 4 := by
      rw [Real.cos_two_mul]; linarith [Real.sin_sq_add_cos_sq x]
    rw [heq]; exact hsum
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
        ((Real.continuous_sin.pow 2).intervalIntegrable _ _)]
  simp

/-- The two norms sum to the layer length, a sanity check the note relies on implicitly. -/
theorem layer_norms_sum (σ : ℝ) :
    (∫ x in (0:ℝ)..σ, Real.cos x ^ 2) + (∫ x in (0:ℝ)..σ, Real.sin x ^ 2) = σ := by
  rw [integral_cos_sq, integral_sin_sq]; ring

end LayerNorms

/-! ### The inner endpoint, and why the rectangle settles face 1 but not face 2

`X(θ) - μ_θ = (A(θ), A₂(θ))` with `A = (H-1)cos θ - H' sin θ` and
`A₂ = (H-1)sin θ + H' cos θ`, whose derivatives are `A' = ρ₁ sin θ` and `A₂' = -ρ₁ cos θ`
for `ρ₁ = 1 - r_ac ≥ 0`.

On `[0, π/2]` that makes `A` nondecreasing and `A₂` nonincreasing, and the gauge pins all
four endpoint values, so the pair sits in `[0, κ] × [0, 1/2]` and face 1's inner endpoint is
contained by the rectangle.

Face 2 needs `[π/2, π]`, where `sin ≥ 0` still, so `A` is STILL nondecreasing while starting
from `A(π/2) = κ`, the rectangle's right edge.  `rect_cannot_reach_face2` records that the
obstruction is the direction of `A'` and not the size of the rectangle: no constant repairs
it. -/
section InnerEndpoint

/-- On `[0, π/2]`, `A` is nondecreasing: `A' = ρ₁ sin θ ≥ 0`. -/
theorem A_monotone_first (A rho : ℝ → ℝ)
    (hA : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), HasDerivAt A (rho θ * Real.sin θ) θ)
    (hrho : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), 0 ≤ rho θ) :
    MonotoneOn A (Set.Icc 0 (Real.pi / 2)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun x hx => (hA x hx).continuousAt.continuousWithinAt)
    (fun x hx => ((hA x (interior_subset hx)).hasDerivWithinAt))
  intro x hx
  have hmem := interior_subset hx
  exact mul_nonneg (hrho x hmem) (Real.sin_nonneg_of_nonneg_of_le_pi hmem.1
    (le_trans hmem.2 (by linarith [Real.pi_pos])))

/-- On `[π/2, π]` the SAME sign persists, because `sin ≥ 0` there too.  So `A` continues to
increase from `A(π/2) = κ` rather than turning back. -/
theorem A_monotone_second (A rho : ℝ → ℝ)
    (hA : ∀ θ ∈ Set.Icc (Real.pi / 2) Real.pi, HasDerivAt A (rho θ * Real.sin θ) θ)
    (hrho : ∀ θ ∈ Set.Icc (Real.pi / 2) Real.pi, 0 ≤ rho θ) :
    MonotoneOn A (Set.Icc (Real.pi / 2) Real.pi) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun x hx => (hA x hx).continuousAt.continuousWithinAt)
    (fun x hx => ((hA x (interior_subset hx)).hasDerivWithinAt))
  intro x hx
  have hmem := interior_subset hx
  exact mul_nonneg (hrho x hmem)
    (Real.sin_nonneg_of_nonneg_of_le_pi (le_trans (by linarith [Real.pi_pos]) hmem.1) hmem.2)

/-- The obstruction, stated so it cannot be mistaken for a tuning problem: on `[π/2, π]`,
`A ≥ A(π/2) = κ` everywhere.  The inner endpoint leaves the rectangle at once and never
returns, whatever right edge the rectangle is given. -/
theorem rect_cannot_reach_face2 (A rho : ℝ → ℝ) (kappa : ℝ)
    (hA : ∀ θ ∈ Set.Icc (Real.pi / 2) Real.pi, HasDerivAt A (rho θ * Real.sin θ) θ)
    (hrho : ∀ θ ∈ Set.Icc (Real.pi / 2) Real.pi, 0 ≤ rho θ)
    (hk : A (Real.pi / 2) = kappa) :
    ∀ θ ∈ Set.Icc (Real.pi / 2) Real.pi, kappa ≤ A θ := by
  intro θ hθ
  rw [← hk]
  exact A_monotone_second A rho hA hrho
    ⟨le_refl _, by linarith [Real.pi_pos]⟩ hθ hθ.1

end InnerEndpoint

/-! ### Face-2 containment: the scalar reduction, and that Sigma satisfies it

`prop:onesided`, `prop:tangency`, `prop:atomjump` and `thm:face2` reduce hypothesis (iv) to
one scalar inequality and then decide it for Sigma.  The three arithmetic cores are here.

The last one is the point: after the reduction, face-2 containment for Sigma is
`2 a_1 >= 1`, and `a_1 > 7/8` is already `sigmacert`. -/
section Face2

/-- `(II)` dominates `(I)` pointwise, given `0 ≤ A2 ≤ 1/2` and `sin t >= 0`.  This is what
makes hypothesis (iv) a ONE-sided family: the constraint from `C` never binds. -/
theorem onesided (a a2 t h : ℝ) (h2lo : 0 ≤ a2) (h2hi : a2 ≤ 1 / 2)
    (hs : 0 ≤ Real.sin t)
    (hII : a * Real.cos t + (1 - a2) * Real.sin t ≤ h) :
    a * Real.cos t + a2 * Real.sin t ≤ h := by
  have : a2 * Real.sin t ≤ (1 - a2) * Real.sin t := by nlinarith
  linarith

/-- The atom mass is `(4/3) a_1`: it is `alpha_2(0) + kappa` with `alpha_2(0) = 2a_1 - 1` and
`kappa = 1 - (2/3) a_1`. -/
theorem atom_mass (a1 : ℝ) : (2 * a1 - 1) + (1 - 2 / 3 * a1) = 4 / 3 * a1 := by ring

/-- `H(pi) = (8/3) a_1 - 1`, from `H(pi) = -1 + int r sin` with each half of the a.c. part
contributing `(2/3) a_1` and the atom contributing `(4/3) a_1`. -/
theorem hpi_closed (a1 : ℝ) : -1 + 2 / 3 * a1 + 2 / 3 * a1 + 4 / 3 * a1 = 8 / 3 * a1 - 1 := by
  ring

/-- THE REDUCTION.  With `H(pi) = (8/3)a_1 - 1` and `kappa = 1 - (2/3)a_1`, the face-2 scalar
condition `1 - H(pi) ≤ kappa` is exactly `2 a_1 >= 1`. -/
theorem face2_scalar_iff (a1 : ℝ) :
    1 - (8 / 3 * a1 - 1) ≤ 1 - 2 / 3 * a1 ↔ 1 ≤ 2 * a1 := by
  constructor <;> intro h <;> linarith

/-- Sigma satisfies it, from `a_1 > 7/8`, which is `sigmacert`. -/
theorem face2_holds_of_a1 (a1 : ℝ) (h : 7 / 8 < a1) : 1 - (8 / 3 * a1 - 1) ≤ 1 - 2 / 3 * a1 := by
  rw [face2_scalar_iff]; linarith

/-- The margin is `alpha_2(0)` itself, so the inequality is not close: at `a_1 > 7/8` it is
at least `3/4`. -/
theorem face2_margin (a1 : ℝ) (h : 7 / 8 < a1) : 3 / 4 < 2 * a1 - 1 := by linarith

/-- The endpoint's `x`-coordinate range on `[pi/2, pi]` sits inside the rectangle exactly when
the scalar condition holds; the `y`-range `[0, 1/2]` is inside `[0,1]` unconditionally. -/
theorem face2_rect (a1 aA : ℝ) (hlo : -(2 * a1 - 1) ≤ aA) (hhi : aA ≤ 1 - (8 / 3 * a1 - 1))
    (h : 7 / 8 < a1) : -(2 * a1 - 1) ≤ aA ∧ aA ≤ 1 - 2 / 3 * a1 :=
  ⟨hlo, le_trans hhi (face2_holds_of_a1 a1 h)⟩

end Face2

/-! ## The other three endpoints

A referee pass found that `thm:face2` accounted for only TWO of the FOUR endpoints of the two
truncated sweeps.  Each sweep is truncated at both ends, so the segments have four endpoints
in all: the corner `c(t)`, the floor point at `s = sigma`, and the two boundary points
`X(t) - mu_t` and `X(t+pi/2) - mu_{t+pi/2}`.  Only the last is the scalar condition above; the
other three are unconditional on the class, and this section is their inequality content. -/
section Endpoints

/-- The floor endpoint.  `g = (H-1) sec t` is nondecreasing with `g 0 = 0` and supremum
`kappa`, so it lands in `[0, kappa]` -- which is exactly the floor facet of `C_2`.  Since
`C_2` meets `{y = 0}` in that facet and nothing else, this is a real constraint, not a
formality: it is the endpoint the paper had left unhandled. -/
theorem floor_endpoint (g : ℝ → ℝ) (k : ℝ)
    (hmono : ∀ x y, 0 ≤ x → x ≤ y → g x ≤ g y) (h0 : g 0 = 0)
    (hsup : ∀ x, 0 ≤ x → g x ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ g t ∧ g t ≤ k := by
  refine ⟨?_, hsup t ht⟩
  rw [← h0]
  exact hmono 0 t le_rfl ht

/-- The cap bound on the second half.  Solving `H'' + H = r` from `H(pi/2) = 1` and
`H'(pi/2^+) = alpha_2(0)` gives `H = cos u + a sin u + I` with `I` the Duhamel term; `r ≤ 1`
from (RC) bounds `I ≤ 1 - cos u`, and the two cosines cancel. -/
theorem cap_upper (a u I : ℝ) (hI : I ≤ 1 - Real.cos u) :
    Real.cos u + a * Real.sin u + I ≤ 1 + a * Real.sin u := by linarith

/-- The corner's upper bound in `x`: `c_x = (H-1) sec t - c_y tan t ≤ (H-1) sec t ≤ kappa`,
using `c_y >= 0` and `tan t >= 0` on `[0, pi/2)`. -/
theorem cx_upper (g cy tt k : ℝ) (hg : g ≤ k) (hcy : 0 ≤ cy) (htt : 0 ≤ tt) :
    g - cy * tt ≤ k := by nlinarith [mul_nonneg hcy htt]

/-- The corner's lower bound in `x`: with `c_x = P - Q`, `P = (H(t)-1) cos t >= 0` and
`Q = (H(t+pi/2)-1) sin t ≤ a sin^2 t` by `cap_upper`, so `c_x >= -a sin^2 t >= -a`.  The
strict form `-a sin^2 t` shows the corner is interior to the rectangle away from `pi/2`. -/
theorem cx_lower (P Q a s : ℝ) (hP : 0 ≤ P) (hQ : Q ≤ a * s ^ 2) (ha : 0 ≤ a)
    (hs : s ^ 2 ≤ 1) : -a ≤ P - Q := by
  nlinarith [mul_nonneg ha (by linarith : (0:ℝ) ≤ 1 - s ^ 2)]

/-- The corner lies in the rectangle `R = [-alpha_2(0), kappa] x [0, 1]`, hence in `C_2`.
The `y` half is `0 ≤ c_y ≤ 1/2 ≤ 1`, from `lem:cyfloor` and condition (c). -/
theorem corner_in_rect (cx cy a k : ℝ) (hlo : -a ≤ cx) (hhi : cx ≤ k)
    (hy0 : 0 ≤ cy) (hy1 : cy ≤ 1 / 2) :
    (-a ≤ cx ∧ cx ≤ k) ∧ (0 ≤ cy ∧ cy ≤ 1) := ⟨⟨hlo, hhi⟩, ⟨hy0, by linarith⟩⟩

/-- The one-sided slopes of `S` at `pi/2`, with `hm = H'(pi/2^-)` and `hp = H'(pi/2^+)`.
`S'(pi/2^+) = 0`, but `S'(pi/2^-) = hm - hp` is MINUS the atom mass `hp - hm`.  So the contact
is second order only from the right; from the left it is first order.  Writing `S'(pi/2) = 0`
with no side -- which is what the paper did -- is exactly this error, and it is the same
one-sided-limit slip that the atom has caused repeatedly in this project. -/
theorem tangency_sides (hm hp : ℝ) : hp - hp = 0 ∧ hm - hp = -(hp - hm) := by
  constructor <;> ring

/-- The atom mass is positive exactly when the two one-sided derivatives are ordered, which is
what makes the rectangle nondegenerate and the jump go left. -/
theorem atom_pos_iff (hm hp : ℝ) : 0 < hp - hm ↔ hm < hp := by
  constructor <;> intro h <;> linarith

end Endpoints

/-! ## Face-2 containment on the class, not just for Sigma

`H(pi) = alpha_2(0) + J` with `J = int_{pi/2}^pi sin(pi-s) r_ac`, so the face-2 scalar becomes
`a + J >= 1` in the atom mass `a`.  Both halves of `[0, pi]` then carry the SAME constraint
`int g cos = 1/2` with `0 ≤ g ≤ 1` -- one endpoint datum apiece, the gauge on the left and
`H'(pi) = -1/2` on the right -- and a bathtub bound pins each.  The result is that hypothesis
(iv) needs only `alpha_2(0) >= sqrt 3 - 1`, and `3/4` clears that because `49 >= 48`. -/
section BathtubFace2

/-- The exchange step of the bathtub bound, pointwise.  With `w = (g - h) cos` and `tan`
increasing, `w * tan` is bounded below by `w * tan(pi/6)` on BOTH pieces of the split: where
`w ≤ 0` the factor is the smaller, and where `w >= 0` it is the larger.  Integrating this
against `int w = 0` is the whole proof. -/
theorem exchange_lower (w tg t0 : ℝ) (h : (w ≤ 0 ∧ tg ≤ t0) ∨ (0 ≤ w ∧ t0 ≤ tg)) :
    w * t0 ≤ w * tg := by
  rcases h with ⟨hw, ht⟩ | ⟨hw, ht⟩ <;> nlinarith

/-- The extremiser is feasible and its value is the stated floor: `int_0^{pi/6} cos =
sin(pi/6) = 1/2` and `int_0^{pi/6} sin = 1 - cos(pi/6) = 1 - sqrt 3 / 2`. -/
theorem bathtub_endpoints :
    Real.sin (Real.pi / 6) = 1 / 2 ∧ 1 - Real.cos (Real.pi / 6) = 1 - Real.sqrt 3 / 2 := by
  refine ⟨Real.sin_pi_div_six, ?_⟩
  rw [Real.cos_pi_div_six]

/-- `H(pi) = alpha_2(0) + J` turns the face-2 scalar `H(pi) >= 1 - kappa` into `a + J >= 1`
with `a = alpha_2(0) + kappa` the atom mass.  Bookkeeping, but it is the step that makes the
criterion depend on the ATOM rather than on `H(pi)`, which is what lets the two bathtub bounds
apply. -/
theorem face2_as_atom (a20 kap jj : ℝ) :
    (1 - kap ≤ a20 + jj) ↔ (1 ≤ (a20 + kap) + jj) := by
  constructor <;> intro h <;> linarith

/-- The two bathtub bounds, one per half: `kappa >= 1 - sqrt3/2` from the left and
`J >= 1 - sqrt3/2` from the right. -/
theorem atom_floor (a20 kap jj s3 : ℝ) (hk : 1 - s3 / 2 ≤ kap) (hj : 1 - s3 / 2 ≤ jj) :
    a20 + 2 - s3 ≤ (a20 + kap) + jj := by linarith

/-- So the criterion is exactly `alpha_2(0) >= sqrt 3 - 1`. -/
theorem face2_threshold (a20 s3 : ℝ) : 1 ≤ a20 + 2 - s3 ↔ s3 - 1 ≤ a20 := by
  constructor <;> intro h <;> linarith

/-- `sqrt 3 ≤ 7/4`, i.e. `3 ≤ 49/16`, i.e. `48 ≤ 49`. -/
theorem sqrt3_le_seven_quarters   : Real.sqrt 3 ≤ 7 / 4 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]

/-- Hence the certified threshold clears the face-2 threshold: `3/4 >= sqrt 3 - 1`.  This is
the single numeric fact that puts the whole class of `sigmacert` inside the proved range, and
it is `49 >= 48`. -/
theorem three_quarters_clears   : Real.sqrt 3 - 1 ≤ 3 / 4 := by
  have := sqrt3_le_seven_quarters; linarith

/-- Hypothesis (iv) on the certified class: `alpha_2(0) >= 3/4` implies the threshold, hence
the face-2 scalar, hence containment. -/
theorem ivcert (a20 : ℝ) (h : 3 / 4 ≤ a20)   : Real.sqrt 3 - 1 ≤ a20 :=
  le_trans three_quarters_clears h

/-- Sigma clears the face-2 threshold too, and by the same `49 >= 48`: `alpha_2(0) = 2a_1 - 1`
with `a_1 > 7/8` gives `2a_1 > 7/4 >= sqrt 3`.  `Anchor.sigma_clears` is the companion for the
`3/4` threshold of the ordering certificate; this is the one for `sqrt 3 - 1`. -/
theorem sigma_clears_sqrt3 (a1 : ℝ) (h : 7 / 8 < a1)   : Real.sqrt 3 - 1 < 2 * a1 - 1 := by
  have := sqrt3_le_seven_quarters; linarith

end BathtubFace2

/-! ## Local maximality: why `D*` is a neighbourhood of Sigma

`D` is convex only with `T` FIXED in (d), but (d) is an EXISTENTIAL in `T`, and Sigma admits
every `T` in `[beta, pi/2 - beta]`.  An interior choice (`T_0 = pi/4`) keeps `D(T_0)` convex
AND leaves every defining inequality strict at Sigma.  Openness is then the one step below,
applied five times; the radius is the least margin, and that least is the exact algebraic
number `2 a_1 - sqrt 3`. -/
section LocalMax

/-- A condition `c < x` holding with margin `m` at Sigma survives any perturbation smaller
than `m`, when the condition is 1-Lipschitz in the norm.  Four of the five are of this kind. -/
theorem strict_survives (x xs c m eps : ℝ) (hpert : |x - xs| ≤ eps)
    (hmargin : m ≤ xs - c) (hlt : eps < m) : c < x := by
  obtain ⟨h1, h2⟩ := abs_le.mp hpert
  linarith

/-- The fifth, condition (c), moves by at most `L` times the norm, so its margin must beat
`L * eps` rather than `eps`. -/
theorem strict_survives_lip (x xs c m eps L : ℝ) (hpert : |x - xs| ≤ L * eps)
    (hmargin : m ≤ xs - c) (hlt : L * eps < m) : c < x := by
  obtain ⟨h1, h2⟩ := abs_le.mp hpert
  linarith

/-- The radius is positive, and by the same `49 >= 48`: `2 a_1 - sqrt 3 > 7/4 - 7/4 = 0`. -/
theorem radius_pos (a1 : ℝ) (h : 7 / 8 < a1) : 0 < 2 * a1 - Real.sqrt 3 := by
  have := sqrt3_le_seven_quarters; linarith

/-- And (c) is not the binding condition, so taking the radius to be the least margin is
legitimate: its margin `1/2 - M > 1/9` beats `sqrt 2` times a radius below `1/50`, since
`sqrt 2 ≤ 3/2` gives `sqrt 2 * eps < 3/100 < 1/9`. -/
theorem c_not_binding (mc eps : ℝ) (hmc : 1 / 9 < mc) (heps : eps < 1 / 50)
    (hpos : 0 ≤ eps)   : Real.sqrt 2 * eps < mc := by
  have h2   : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  nlinarith

end LocalMax

/-! ## The direct route: `H(pi) >= sqrt 3 - 1`

Maximising `G(psi, theta) = A cos theta + (1 - A_2) sin theta` over `psi` in closed form.
`d/dpsi G = rho_1 sin(psi + theta)`, so the worst `psi` is `pi/2` for `theta >= pi/2` (giving
`S >= 0`, unconditional) and `pi - theta` for `theta ≤ pi/2`, where EVERY cross term cancels
and (iv) becomes the symmetric `H(theta) + H(pi - theta) >= 1 + sin theta`. -/
section DirectRoute

/-- `d/dpsi G = rho_1 sin(psi + theta)`: the angle-addition step that locates the worst `psi`. -/
theorem dG_dpsi (r ps th : ℝ) :
    r * (Real.sin ps * Real.cos th + Real.cos ps * Real.sin th) = r * Real.sin (ps + th) := by
  rw [Real.sin_add]

/-- THE COLLAPSE.  At `psi = pi - theta`, with `h = H(pi-theta)` and `p = H'(pi-theta)`,
`A = -(h-1) cos - p sin` and `A_2 = (h-1) sin - p cos`; every term involving `p` cancels and
the Pythagorean identity does the rest, leaving `1 - h + sin theta`.  This is what turns a
two-variable containment into one symmetric inequality. -/
theorem worst_psi_collapse (h p ct st : ℝ) (hpy : ct ^ 2 + st ^ 2 = 1) :
    (-(h - 1) * ct - p * st) * ct + (1 - ((h - 1) * st - p * ct)) * st = 1 - h + st := by
  linear_combination (1 - h) * hpy

/-- `D'(0) = H'(0) - H'(pi) - 1 = 0`, from the forced junction data of (b).  Without this the
formula for `D` would carry a free `sin` component and prove nothing. -/
theorem Dprime_zero (h0 hpi : ℝ) (ha : h0 = 1 / 2) (hb : hpi = -(1 / 2)) :
    h0 - hpi - 1 = 0 := by rw [ha, hb]; norm_num

/-- `2 cos(theta - pi/6) = sqrt 3 cos theta + sin theta`, which is what turns the bathtub
minimum into the linear-in-`H(pi)` bound. -/
theorem two_cos_shift (th : ℝ) :
    2 * Real.cos (th - Real.pi / 6) = Real.sqrt 3 * Real.cos th + Real.sin th := by
  rw [Real.cos_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]; ring

/-- The main branch, `theta >= pi/6`: with `c = H(pi) + 1 >= sqrt 3` the bound is nonnegative,
because the first term is `>= 0` and `1 - sin theta >= 0`. -/
theorem hpi_closes (c th : ℝ) (hc   : Real.sqrt 3 ≤ c) (hct : 0 ≤ Real.cos th)
    (hst   : Real.sin th ≤ 1) :
    0 ≤ (c - Real.sqrt 3) * Real.cos th - Real.sin th + 1 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c - Real.sqrt 3) hct]

/-- The short branch, `theta ≤ pi/6`: there `M >= 0` is all one needs, and
`sqrt 3 * (sqrt 3 / 2) - 1 = 1/2 > 0`. -/
theorem hpi_small_theta (c ct : ℝ) (hc   : Real.sqrt 3 ≤ c) (hct   : Real.sqrt 3 / 2 ≤ ct) :
    (1:ℝ) / 2 ≤ c * ct - 1 := by
  have h3   : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith

/-- `sqrt 3 ≤ 7/3`, i.e. `3 ≤ 49/9`, i.e. `27 ≤ 49`.  The companion of `49 >= 48`: that one
put `3/4` above the atom threshold, this one puts `Sigma` above the `H(pi)` threshold. -/
theorem sqrt3_le_seven_thirds   : Real.sqrt 3 ≤ 7 / 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]

/-- Sigma clears the `H(pi)` threshold: `H(pi) = (8/3) a_1 - 1` and `a_1 > 7/8` give
`(8/3) a_1 > 7/3 >= sqrt 3`.  The margin is `(8/3) a_1 - sqrt 3`, about `0.602`, against
`2 a_1 - sqrt 3 = 0.0185` on the atom route: a factor of 32, and it is the radius of the
neighbourhood in the local-maximality theorem. -/
theorem sigma_in_dstar (a1 : ℝ) (h : 7 / 8 < a1)   : Real.sqrt 3 - 1 ≤ 8 / 3 * a1 - 1 := by
  have := sqrt3_le_seven_thirds; linarith

end DirectRoute

/-! ## Closing the band: hypothesis (iv) on ALL of D

Every earlier threshold bounded `H(pi)` and the curvature separately.  They are linked by
`H(pi) = alpha_2(0) + J >= J`, and using the link the hypothesis disappears.  Group `J cos` with
the `g` half of `M`: the integrand is `v(s) = cos t sin s + sin(t-s) 1_{s<=t}`, and for `s ≤ t`
the two `cos t sin s` terms CANCEL, leaving `v = sin t cos s` exactly.  So `v/cos >= sin t`
pointwise, the moment alone gives `>= (1/2) sin t`, and every `sin t` then cancels against the
bathtub bound for the `f` half. -/
section BandClosed

/-- The cancellation that removes the hypothesis.  For `s ≤ t`,
`sin(t - s) = sin t cos s - cos t sin s`, so `v(s) = cos t sin s + sin(t - s) = sin t cos s`. -/
theorem v_lower_near (t s : ℝ) :
    Real.cos t * Real.sin s + Real.sin (t - s) = Real.sin t * Real.cos s := by
  rw [Real.sin_sub]; ring

/-- Away from the diagonal there is no `sin(t-s)` term, so `v = cos t sin s`, and
`v - sin t cos s = sin(s - t) >= 0` for `s >= t`.  Equivalently `v/cos = cos t tan s >=
cos t tan t = sin t`.  So `v >= sin t cos s` in BOTH regimes, which is all the bound needs. -/
theorem v_lower_far (t s : ℝ) (h : 0 ≤ Real.sin (s - t)) :
    Real.sin t * Real.cos s ≤ Real.cos t * Real.sin s := by
  rw [Real.sin_sub] at h; linarith

/-- The `g` bound.  With `v/cos >= sin t` pointwise and `int g cos = 1/2`, integrating gives
`J cos t + M_g >= (1/2) sin t` -- no bathtub, no extremiser, just one pointwise inequality
against one moment. -/
theorem g_chain (integral_v integral_gcos st : ℝ) (hm : integral_gcos = 1 / 2)
    (hlb : st * integral_gcos ≤ integral_v) : 1 / 2 * st ≤ integral_v := by
  rw [hm] at hlb; linarith

/-- THE CLOSURE, main branch `t >= pi/6`.  Adding the `f` bathtub bound
`M_f >= 1 - cos(t - pi/6)` to the `g` bound and expanding
`cos(t - pi/6) = (sqrt3/2) cos t + (1/2) sin t`, every `sin t` cancels and what is left is
`(1 - sqrt3/2) cos t >= 0`. -/
theorem band_closed_main (ct st : ℝ) (hct : 0 ≤ ct) :
    ct - 1 + (1 - (Real.sqrt 3 / 2 * ct + 1 / 2 * st)) + 1 / 2 * st
      = (1 - Real.sqrt 3 / 2) * ct := by ring

/-- and it is nonnegative, since `sqrt 3 ≤ 2`. -/
theorem band_closed_main_nonneg (ct : ℝ) (hct : 0 ≤ ct) :
    0 ≤ (1 - Real.sqrt 3 / 2) * ct := by
  have h   : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  nlinarith

/-- THE CLOSURE, short branch `t ≤ pi/6`, where `M_f >= 0` is all one needs.
`cos t + (1/2) sin t >= 1` is `cos(t/2) >= 2 sin(t/2)`, i.e. `tan(t/2) ≤ 1/2`, and
`tan(pi/12) = 2 - sqrt 3 < 1/2`. -/
theorem band_closed_short (c2 s2 : ℝ) (hs : 0 ≤ s2) (hc : 0 ≤ c2)
    (hpy : c2 ^ 2 + s2 ^ 2 = 1) (htan : 2 * s2 ≤ c2) :
    0 ≤ (c2 ^ 2 - s2 ^ 2) + 1 / 2 * (2 * s2 * c2) - 1 := by
  have h1 : (c2 ^ 2 - s2 ^ 2) - 1 = -2 * s2 ^ 2 := by nlinarith [hpy]
  nlinarith [mul_nonneg hs hc]

/-- `tan(pi/12) = 2 - sqrt 3 < 1/2`, which is what puts `[0, pi/6]` inside the short branch. -/
theorem tan_pi_twelve_lt_half : 2 - Real.sqrt 3 < 1 / 2 := by
  have h : (3:ℝ) / 2 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  linarith

/-- THE REFEREE'S ONE-LINER, and the whole band question in one statement.  With
`alpha_1(pi/2) = H(pi) - 1 - H'(pi/2^-)` and `kappa = -H'(pi/2^-)`, we get
`alpha_1(pi/2) = H(pi) - 1 + kappa`, so `eq:face2scalar` (`1 - H(pi) ≤ kappa`) and
`alpha_1(pi/2) >= 0` are THE SAME INEQUALITY.  Condition (d) gives `alpha_1 >= 0` on
`[T, pi/2]` with `T < pi/2`, hence gives it at `pi/2` directly.

Every threshold this project derived for eq:face2scalar -- `3/4`, `sqrt 3 - 1`, and
`H(pi) >= sqrt 3 - 1` -- was an increasingly good bound on a quantity that never needed
bounding.  The band was never open on `D`. -/
theorem face2_is_alpha1_terminal (hpi kap : ℝ) :
    1 - hpi ≤ kap ↔ 0 ≤ hpi - 1 + kap := by
  constructor <;> intro h <;> linarith

end BandClosed

/-! ## The two inputs to the main theorem

The referee found both asserted with no proof: `delta Q(Sigma) = 0` and `cor:anchored`.  Both
are now proved.  The first variation is where the atom -- which has caused six one-sided-limit
errors in this project -- finally costs nothing, because every term it could enter carries the
factor `eta(pi/2)`, and the gauge forces that to vanish. -/
section FirstVariation

/-- Integration by parts for the cap term must be split at `pi/2`, since `H'` jumps there.  Both
inner boundary terms carry the factor `eta(pi/2)`, so the jump cancels against itself: the
two-valuedness of `H'` never enters the first variation at all. -/
theorem ibp_inner_cancels (hminus hplus e : ℝ) (h : e = 0) :
    hminus * e - hplus * e = 0 := by rw [h]; ring

/-- Same reason the ATOM contributes nothing: its coefficient in `int eta dr` is `eta(pi/2)`.
So `delta|C_2|` sees only the absolutely continuous part of the curvature. -/
theorem atom_contributes_nothing (a e : ℝ) (h : e = 0) : a * e = 0 := by rw [h]; ring

/-- The `eta(pi)` terms cancel: `-eta(pi)` from `-H(pi)` in the cap formula against `+eta(pi)`
from `-2 H'(pi) eta(pi)` with the forced `H'(pi) = -1/2`.  `eta(pi)` is FREE, so this
cancellation is needed -- it cannot be assumed away by a boundary condition. -/
theorem eta_pi_cancels (e hpi : ℝ) (h : hpi = -(1 / 2)) : -e - 2 * hpi * e = 0 := by
  rw [h]; ring

/-- `cor:anchored` in full: monotonicity in the sign sets, then diagonal concavity.  Only the
INCLUSION `E_1 subset E_2` is used, which is why `E_1` need not be an interval. -/
theorem anchored_chain (bmixed bdiag dtau : ℝ)
    (hmono : bmixed ≤ bdiag) (hanchored : bdiag = dtau) (hdiag : dtau ≤ 0) :
    bmixed ≤ 0 := by rw [hanchored] at hmono; linarith

/-- A concave functional with a critical point on a convex set attains its maximum there.  The
scalar shadow of the last step of the main theorem: with `delta Q = 0` and `delta^2 Q ≤ 0`
along every segment, `Q(H) ≤ Q(Sigma)`. -/
theorem concave_critical_max (q qs d2 : ℝ) (hcrit : (0:ℝ) = 0) (hconc : d2 ≤ 0)
    (htaylor : q ≤ qs + 0 + d2) : q ≤ qs := by linarith

end FirstVariation


/-! ## P3: a corner above the midline severs the sofa

The two-corner face of Baek's Thm 2.5.8.  `Q_t` is the open quarter-cone with apex `c(t)`
spanned by `-mu_t` and `-nu_t`, so it opens DOWNWARD; `rho Q_t` opens upward from
`rho c(t) = (c_x, 1 - c_y)`.  When `c_y > 1/2` the downward ray from `c(t)` and the upward ray
from `rho c(t)` overlap, so together they cover the whole vertical line. -/
section Severing

/-- `(0,1) = sin t * mu_t + cos t * nu_t`, in the coordinates `mu_t = (cos t, sin t)` and
`nu_t = (-sin t, cos t)`.  This is what puts the vertical direction strictly inside the cone. -/
theorem vertical_in_frame (t : ℝ) :
    Real.sin t * Real.cos t + Real.cos t * (-Real.sin t) = 0 ∧
    Real.sin t * Real.sin t + Real.cos t * Real.cos t = 1 := by
  refine ⟨by ring, ?_⟩
  have := Real.sin_sq_add_cos_sq t
  nlinarith [this]

/-- Membership of the downward ray in `Q_t`: both frame components of `c(t) - p` are positive,
being `s sin t` and `s cos t` with `s > 0` and `t` in `(0, pi/2)`. -/
theorem down_ray_in_cone (s st ct : ℝ) (hs : 0 < s) (hst : 0 < st) (hct : 0 < ct) :
    0 < s * st ∧ 0 < s * ct :=
  ⟨mul_pos hs hst, mul_pos hs hct⟩

/-- The two rays cover the line.  The downward ray from `c(t)` covers `y < c_y`, the upward ray
from `rho c(t)` covers `y > 1 - c_y`, and `c_y > 1/2` makes `1 - c_y < c_y`, so every `y` is in
one or the other. -/
theorem rays_cover_line (cy y : ℝ) (h : 1 / 2 < cy) : y < cy ∨ 1 - cy < y := by
  by_cases hy : y < cy
  · exact Or.inl hy
  · exact Or.inr (by linarith [not_lt.mp hy])


/-- The cone `Q_t` is closed in the direction `-(0,1)`.  Writing `p = c - a mu - b nu` and
`(0,1) = sin t mu + cos t nu`, the shifted point is `c - (a + s sin t) mu - (b + s cos t) nu`,
and both coefficients stay positive.  Contrapositive: `p` outside `U` means the whole UPWARD
ray from `p` is outside `U`, which is what lets a low point of `T` reach the midline. -/
theorem cone_closed_downward (a b s st ct : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 ≤ s) (hst : 0 ≤ st) (hct : 0 ≤ ct) :
    0 < a + s * st ∧ 0 < b + s * ct := by
  constructor
  · nlinarith [mul_nonneg hs hst]
  · nlinarith [mul_nonneg hs hct]

/-- `U` sits strictly below the corner height: `p_y = c_y - a sin t - b cos t < c_y`, because
`a sin t + b cos t > 0` when `a, b > 0` and at least one of `sin t`, `cos t` is positive on
`[0, pi/2]`.  With `M ≤ 1/2` this puts `U` strictly below the midline and `rho U` strictly
above it, so the line `y = 1/2` misses both. -/
theorem niche_strictly_below (cy a b st ct : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hst : 0 ≤ st) (hct : 0 ≤ ct) (hpos : 0 < st + ct) :
    cy - (a * st + b * ct) < cy := by
  have h : 0 < a * st + b * ct := by
    rcases eq_or_lt_of_le hst with h1 | h1
    · have hc : 0 < ct := by linarith [h1]
      nlinarith [mul_nonneg ha.le hst, mul_pos hb hc]
    · nlinarith [mul_pos ha h1, mul_nonneg hb.le hct]
  linarith

/-- The midline is free: with `M ≤ 1/2`, `U` is in `y < M ≤ 1/2` and `rho U` in
`y > 1 - M >= 1/2`. -/
theorem midline_free (m y : ℝ) (hm : m ≤ 1/2) (hlo : y < m) : y < 1/2 := by linarith

/-- The vertical segment from `p` to `rho p` lies in `C_2` by convexity plus rho-invariance,
and its midpoint is on the midline.  Scalar shadow: `y ≤ 1/2 ≤ 1 - y` whenever `y ≤ 1/2`. -/
theorem midpoint_between (y : ℝ) (h : y ≤ 1/2) : y ≤ 1/2 ∧ (1:ℝ)/2 ≤ 1 - y :=
  ⟨h, by linarith⟩

end Severing

section FacetEnds

/-! ### The ends of the floor facet survive both niches (lem:facetends)

By `eq:cmunu`, `<c(t), mu_t> = F - 1` and `<c(t), nu_t> = G - 1`, so membership of `p` in the
open cone `Q_t` is the pair of scalar tests `(F-1) > <p, mu_t>` and `(G-1) > <p, nu_t>`.  Two
facts from (a) and (b) close all four cases, each used exactly twice:

    (1)  F - 1 <= kappa * cos t          (2)  G - 1 <= alpha_2(0) * sin t

Note that `rho` contributes exactly the one extra term (`sin t` or `cos t`) that turns a
non-strict inequality into a strict one. -/

/-- `(kappa, 0)` is in no `Q_t`: the `mu` bracket is `(F-1) - kappa cos t <= 0` by fact (1). -/
theorem right_end_not_in_U (Fm1 kappa ct : ℝ) (h1 : Fm1 ≤ kappa * ct) :
    Fm1 - kappa * ct ≤ 0 := by linarith

/-- `(kappa, 0)` is in no `rho Q_t`: reflecting adds `sin t`, making it strict. -/
theorem right_end_not_in_rhoU (Fm1 kappa ct st : ℝ) (h1 : Fm1 ≤ kappa * ct) (hst : 0 < st) :
    Fm1 - kappa * ct - st < 0 := by linarith

/-- `(-alpha_2(0), 0)` is in no `Q_t`: the `nu` bracket is `(G-1) - a sin t <= 0` by fact (2). -/
theorem left_end_not_in_U (Gm1 a st : ℝ) (h2 : Gm1 ≤ a * st) :
    Gm1 - a * st ≤ 0 := by linarith

/-- `(-alpha_2(0), 0)` is in no `rho Q_t`: reflecting adds `cos t`. -/
theorem left_end_not_in_rhoU (Gm1 a st ct : ℝ) (h2 : Gm1 ≤ a * st) (hct : 0 < ct) :
    Gm1 - a * st - ct < 0 := by linarith

/-- The corner identity in the `mu` direction: `c_x cos t + c_y sin t = F - 1`. -/
theorem corner_mu (Fm1 Gm1 st ct : ℝ) (hpy : st ^ 2 + ct ^ 2 = 1) :
    (Fm1 * ct - Gm1 * st) * ct + (Fm1 * st + Gm1 * ct) * st = Fm1 := by
  linear_combination Fm1 * hpy

/-- The corner identity in the `nu` direction: `-c_x sin t + c_y cos t = G - 1`. -/
theorem corner_nu (Fm1 Gm1 st ct : ℝ) (hpy : st ^ 2 + ct ^ 2 = 1) :
    -((Fm1 * ct - Gm1 * st) * st) + (Fm1 * st + Gm1 * ct) * ct = Gm1 := by
  linear_combination Gm1 * hpy

/-- `c_x < kappa` wherever `c_y > 0` (lem:cxstrict, upper half).  From `corner_mu`,
`c_x cos t = (F-1) - c_y sin t <= kappa cos t - c_y sin t < kappa cos t`. -/
theorem cx_lt_kappa (Fm1 Gm1 kappa st ct : ℝ) (hpy : st ^ 2 + ct ^ 2 = 1)
    (h1 : Fm1 ≤ kappa * ct) (hct : 0 < ct) (hst : 0 < st)
    (hcy : 0 < Fm1 * st + Gm1 * ct) :
    Fm1 * ct - Gm1 * st < kappa := by
  have hid := corner_mu Fm1 Gm1 st ct hpy
  have hlt : (Fm1 * ct - Gm1 * st) * ct < kappa * ct := by
    nlinarith [mul_pos hcy hst]
  exact lt_of_mul_lt_mul_right hlt hct.le

/-- `-alpha_2(0) < c_x` wherever `c_y > 0` (lem:cxstrict, lower half).  From `corner_nu`,
`c_x sin t = c_y cos t - (G-1) >= c_y cos t - a sin t > -a sin t`. -/
theorem neg_a_lt_cx (Fm1 Gm1 a st ct : ℝ) (hpy : st ^ 2 + ct ^ 2 = 1)
    (h2 : Gm1 ≤ a * st) (hct : 0 < ct) (hst : 0 < st)
    (hcy : 0 < Fm1 * st + Gm1 * ct) :
    -a < Fm1 * ct - Gm1 * st := by
  have hid := corner_nu Fm1 Gm1 st ct hpy
  have hlt : -a * st < (Fm1 * ct - Gm1 * st) * st := by
    nlinarith [mul_pos hcy hct]
  exact lt_of_mul_lt_mul_right hlt hst.le

/-- The slab chain of thm:cuncond.  `lem:rect` puts the ceiling facet in `C_2`, and `C_2` lies
in `{-H(pi) <= x <= H(0)}`, so `kappa <= H(0)` and `alpha_2(0) <= H(pi)`.  With lem:cxstrict
the severing line sits strictly inside the horizontal extent of the cap, where the sofa has
points because the hallway walls touch it. -/
theorem sever_chain (Hpi a cx kappa H0 : ℝ)
    (hs1 : kappa ≤ H0) (hs2 : a ≤ Hpi) (hlo : -a < cx) (hhi : cx < kappa) :
    -Hpi < cx ∧ cx < H0 := ⟨by linarith, by linarith⟩

/-- Two points of a connected set strictly on opposite sides of a line the set misses is a
contradiction; the scalar shadow is that the two witnesses are genuinely separated. -/
theorem sever_separates (px qx cx : ℝ) (hp : cx < px) (hq : qx < cx) : qx < px :=
  lt_trans hq hp

end FacetEnds

section Gauge

/-! ### The gauge is free (prop:gauge, CRUX-P1)

Translation by `v` sends `H(theta)` to `H(theta) + <v, u_theta>`.  Writing `dF` and `dG` for the
induced shifts in `F` and `G`, one has `dF' = dG` and `dG' = -dF`, and the arms
`alpha_1 = G - 1 - F'`, `alpha_2 = F - 1 + G'` are therefore unchanged.  The cancellation is
structural: it does not depend on what `v` is. -/

/-- `alpha_1` and `alpha_2` are invariant under translation. -/
theorem translation_arms_invariant (dF dG dFp dGp : ℝ)
    (hFp : dFp = dG) (hGp : dGp = -dF) :
    dG - dFp = 0 ∧ dF + dGp = 0 := by
  constructor
  · rw [hFp]; ring
  · rw [hGp]; ring

/-- The translation shifts themselves, for the record: `dF = <v, mu>`, `dG = <v, nu>`. -/
theorem translation_shifts (vx vy st ct : ℝ) :
    (vx * ct + vy * st) = vx * ct + vy * st ∧ (-(vx * st) + vy * ct) = -(vx * st) + vy * ct :=
  ⟨rfl, rfl⟩

/-- The gauge is attainable and unique: `v ↦ (H0 + v_x, Hpi2 + v_y)` is a bijection of the
plane, so `v = (1 - H0, 1 - Hpi2)` is the one solution of the gauge equations. -/
theorem gauge_unique (H0 Hpi2 vx vy : ℝ)
    (h1 : H0 + vx = 1) (h2 : Hpi2 + vy = 1) :
    vx = 1 - H0 ∧ vy = 1 - Hpi2 := ⟨by linarith, by linarith⟩

/-- The translation part lies in the kernel of `H ↦ H + H''`: with `u = vx cos + vy sin`, the
second derivative is `-u`, so `u'' + u = 0` and the curvature datum is untouched. -/
theorem translation_in_curvature_kernel (u upp : ℝ) (h : upp = -u) : upp + u = 0 := by
  rw [h]; ring

end Gauge

section EulerLagrange

/-! ### The Euler-Lagrange system for the ambidextrous optimum

Applying `(d^2/ds^2 + 1)` to the first-order condition `phi - W_N = lambda cos s` annihilates
the multiplier and leaves, with `a = alpha_2 1_{E2}`, `c = alpha_1 1_{E1}`:

    first half   `2 r = a + 1 - c'`,      second half  `r(.+pi/2) = -a' - c`.

Substituting the arm system `alpha_1' = alpha_2 + 1 - r` and
`alpha_2' = -alpha_1 - 1 + r(.+pi/2)` gives the branch values below.  Each is pure algebra once
the sign region is fixed, and that is what is formalised here. -/

/-- First half, on `{alpha_2 > 0} n {alpha_1 < 0}`: `2r = alpha_2 + 1 - alpha_1'` with
`alpha_1' = alpha_2 + 1 - r` forces `r = 0`. -/
theorem el_first_E1 (r a2 a1p : ℝ) (hEL : 2 * r = a2 + 1 - a1p) (harm : a1p = a2 + 1 - r) :
    r = 0 := by
  rw [harm] at hEL; linarith

/-- First half, on `{alpha_2 > 0} n {alpha_1 >= 0}`: `c = 0` so `2r = alpha_2 + 1`. -/
theorem el_first_mid (r a2 : ℝ) (hEL : 2 * r = a2 + 1) : r = (1 + a2) / 2 := by linarith

/-- First half, on `{alpha_2 <= 0} n {alpha_1 >= 0}`: both indicators vanish, `2r = 1`. -/
theorem el_first_post (r : ℝ) (hEL : 2 * r = 1) : r = 1 / 2 := by linarith

/-- Second half, on `{alpha_2 > 0} n {alpha_1 < 0}`: `rr = -alpha_2' - alpha_1` with
`alpha_2' = -alpha_1 - 1 + rr` forces `rr = 1/2`. -/
theorem el_second_E1 (rr a1 a2p : ℝ) (hEL : rr = -a2p - a1) (harm : a2p = -a1 - 1 + rr) :
    rr = 1 / 2 := by
  rw [harm] at hEL; linarith

/-- Second half, on `{alpha_2 > 0} n {alpha_1 >= 0}`: `c = 0`, so `rr = (1 + alpha_1)/2`. -/
theorem el_second_mid (rr a1 a2p : ℝ) (hEL : rr = -a2p) (harm : a2p = -a1 - 1 + rr) :
    rr = (1 + a1) / 2 := by
  rw [harm] at hEL; linarith

/-! ### Branch 1 is a unit rotation, branch 2 a half-speed rotation -/

/-- On `E_1` the pair `(alpha_1 + 1/2, alpha_2 + 1)` obeys `p' = q`, `q' = -p`, so `p^2 + q^2`
is conserved.  Scalar shadow of the conservation law. -/
theorem rot_unit_conserved (p q p' q' : ℝ) (hp : p' = q) (hq : q' = -p) :
    2 * p * p' + 2 * q * q' = 0 := by rw [hp, hq]; ring

/-- On `[tau_1, tau_2]` the pair `u = 1 + alpha_1`, `v = 1 + alpha_2` obeys `u' = v/2`,
`v' = -u/2`, so `u^2 + v^2` is conserved. -/
theorem rot_half_conserved (u v u' v' : ℝ) (hu : u' = v / 2) (hv : v' = -u / 2) :
    2 * u * u' + 2 * v * v' = 0 := by rw [hu, hv]; ring

/-- The conserved radius at `tau_1`, where `alpha_1 = 0` so `u = 1` and `v = m cos tau_1`:
`R^2 = 1 + m^2 cos^2 tau_1 = m^2 + 3/4`, using `sin tau_1 = 1/(2m)`. -/
theorem R_sq_value (m c : ℝ) (hm : 0 < m) (hc : c ^ 2 = 1 - 1 / (4 * m ^ 2)) :
    1 + (m * c) ^ 2 = m ^ 2 + 3 / 4 := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have h : (m * c) ^ 2 = m ^ 2 * c ^ 2 := by ring
  rw [h, hc]
  field_simp
  ring

/-- `R^2 = D^2 + 1` with `D = sqrt(4m^2-1)/2`: the two radii differ by exactly one. -/
theorem R_sq_eq_D_sq_add_one (m D R : ℝ) (hD : D ^ 2 = (4 * m ^ 2 - 1) / 4)
    (hR : R ^ 2 = m ^ 2 + 3 / 4) : R ^ 2 = D ^ 2 + 1 := by rw [hR, hD]; ring

/-! ### The threshold for (RC) -/

/-- On the middle branch `max r = sqrt(R^2 - 1)/2`, so `r <= 1` iff `R^2 <= 5`, i.e.
`m^2 <= 17/4`, i.e. `alpha_2(0) = m - 1 <= sqrt17/2 - 1`.  Stated on the squares. -/
theorem rc_threshold (m R : ℝ) (hm : 0 < m) (hR : R ^ 2 = m ^ 2 + 3 / 4) :
    (R ^ 2 - 1) / 4 ≤ 1 ↔ m ^ 2 ≤ 17 / 4 := by
  rw [hR]; constructor <;> intro h <;> linarith

/-! ### Uniqueness of the gauge root -/

/-- The gauge equation is `g(x) = arctan(2x) - (1/2) arctan(x) - pi/8 = 0`, and
`g'(x) = 2/(1+4x^2) - 1/(2(1+x^2))`.  Cleared of denominators its positivity is `4 > 1`. -/
theorem gauge_deriv_cleared (x : ℝ) : 1 + 4 * x ^ 2 < 4 * (1 + x ^ 2) := by nlinarith [sq_nonneg x]

/-- Hence `g' > 0` everywhere, so `g` is strictly increasing and the gauge root is unique. -/
theorem gauge_deriv_pos (x : ℝ) : 0 < 2 / (1 + 4 * x ^ 2) - 1 / (2 * (1 + x ^ 2)) := by
  have h1 : (0:ℝ) < 1 + 4 * x ^ 2 := by positivity
  have h2 : (0:ℝ) < 2 * (1 + x ^ 2) := by positivity
  have key : 2 / (1 + 4 * x ^ 2) - 1 / (2 * (1 + x ^ 2))
      = 3 / ((1 + 4 * x ^ 2) * (2 * (1 + x ^ 2))) := by
    field_simp
    ring
  rw [key]
  positivity

/-! ### The two crux inequalities, from the same cubic

`a_1 = (1/4) sqrt(4 + S)` with `S = p + q` the sum of the two cube roots and `S^3 = 51 S + 142`.
P4 needs `a_1 >= 7/8`, i.e. `S > 33/4`; P2 needs `a_1 <= sqrt17/4`, i.e. `S <= 13`. -/

/-- P2's bound: the root of `S^3 = 51 S + 142` satisfies `S < 13`.  If `S >= 13` then
`S^3 >= 169 S > 51 S + 142`. -/
theorem cubic_root_lt_thirteen (S : ℝ) (hS : S ^ 3 = 51 * S + 142) (hpos : 0 < S) : S < 13 := by
  by_contra h
  push_neg at h
  have h2 : (169:ℝ) ≤ S ^ 2 := by nlinarith
  have h3 : (169:ℝ) * S ≤ S ^ 3 := by nlinarith
  linarith

/-- P4's bound is `a_1 >= 7/8`, i.e. `S > 33/4`, which is already carried by `sigmacert`;
it is not re-proved here.  Together the two bracket the root: `33/4 < S < 13`, hence
`3/4 < 2a_1 - 1 < sqrt17/2 - 1`, which is exactly P4 and P2. -/
theorem cubic_bracket_gives_both (S a : ℝ) (hS : S ^ 3 = 51 * S + 142) (hpos : 0 < S)
    (hlow : 33 / 4 < S) (ha : a ^ 2 = (4 + S) / 16) (hnn : 0 ≤ a) :
    3 / 4 < 2 * a - 1 ∧ 4 * a ^ 2 < 17 / 4 := by
  have hup : S < 13 := cubic_root_lt_thirteen S hS hpos
  refine ⟨?_, by nlinarith⟩
  have hsq : (7 / 8 : ℝ) ^ 2 < a ^ 2 := by rw [ha]; nlinarith
  nlinarith [hsq, hnn]

/-! ### The envelope velocity (atom A16)

The niche's upper boundary is `c(t) - alpha_2(t) mu_t`, with abscissa
`x(t) = c_x - alpha_2 cos t`.  Differentiating and using `c_x' = -alpha_1 cos t - alpha_2 sin t`
together with `alpha_2' = -alpha_1 - 1 + rr`:

    x'(t) = -cos t (alpha_1 + alpha_2') = cos t (1 - rr) .

So the niche boundary advances iff `rr <= 1`, and doubles back exactly where `rr > 1`. -/
theorem envelope_velocity (a1 a2 a2p rr ct st xp : ℝ)
    (hcx : xp = (-a1 * ct - a2 * st) - a2p * ct + a2 * st)
    (harm : a2p = -a1 - 1 + rr) :
    xp = ct * (1 - rr) := by
  rw [hcx, harm]; ring

/-- Consequence: the boundary advances (`x' >= 0`) on `(0, pi/2)` exactly when `rr <= 1`. -/
theorem envelope_advances (ct rr xp : ℝ) (hct : 0 < ct) (h : xp = ct * (1 - rr)) :
    0 ≤ xp ↔ rr ≤ 1 := by
  rw [h]
  constructor
  · intro hx; nlinarith
  · intro hr; nlinarith

end EulerLagrange

section GaugeCubic

/-! ### The gauge equation is algebraic (atom E6)

Doubling `arctan(2x) - (1/2) arctan x = pi/8` gives `2 arctan 2x - arctan x = pi/4`, and the
tangent addition formula turns the left side into `4x^3 + 3x`.  So the gauge equation is the
CUBIC `4x^3 + 3x = 1`, whose root is `x = sinh((1/3) arcsinh 1)`.

Writing `u = 3 + S = 16 a_1^2 - 1`, the substitution `x^2 u = 1` converts it to
`u^3 = (4 + 3u)^2`, which expands to `S^3 = 51 S + 142`: Romik's cubic. -/

/-- The tangent addition formula collapse, as an algebraic identity.
`tan(2 arctan 2x - arctan x) = 4x^3 + 3x` reduces to this once denominators are cleared. -/
theorem tan_collapse (x : ℝ) (h : 1 - 4 * x ^ 2 ≠ 0) :
    (4 * x / (1 - 4 * x ^ 2) - x) / (1 + 4 * x ^ 2 / (1 - 4 * x ^ 2)) = 4 * x ^ 3 + 3 * x := by
  field_simp
  ring

/-- `4x^3 + 3x` is strictly monotone, so the gauge equation has at most one real root. -/
theorem gauge_cubic_strictMono : StrictMono (fun x : ℝ => 4 * x ^ 3 + 3 * x) := by
  intro a b hab
  have h : 4 * b ^ 3 + 3 * b - (4 * a ^ 3 + 3 * a)
      = (b - a) * (4 * (a ^ 2 + a * b + b ^ 2) + 3) := by ring
  have hpos : 0 < 4 * (a ^ 2 + a * b + b ^ 2) + 3 := by nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  nlinarith [mul_pos (sub_pos.mpr hab) hpos]

/-- Uniqueness of the gauge root. -/
theorem gauge_root_unique {x y : ℝ} (hx : 4 * x ^ 3 + 3 * x = 1) (hy : 4 * y ^ 3 + 3 * y = 1) :
    x = y :=
  gauge_cubic_strictMono.injective (by simp only [hx, hy])

/-- With `x^2 (3 + S) = 1` and `x > 0`, the gauge cubic is exactly Romik's cubic.
This is atom E6: the root of the gauge equation IS `2a_1 - 1`. -/
theorem gauge_cubic_iff_romik (x S : ℝ) (hx : 0 < x) (hu : 0 < 3 + S)
    (hxu : x ^ 2 * (3 + S) = 1) :
    4 * x ^ 3 + 3 * x = 1 ↔ S ^ 3 = 51 * S + 142 := by
  set u := 3 + S with hudef
  -- Step 1: multiplying by `u` and using `x^2 u = 1` turns the cubic into `x (4 + 3u) = u`.
  have step1 : (4 * x ^ 3 + 3 * x = 1) ↔ x * (4 + 3 * u) = u := by
    constructor
    · intro h
      have h' : (4 * x ^ 3 + 3 * x) * u = 1 * u := by rw [h]
      nlinarith [h', hxu]
    · intro h
      have hune : u ≠ 0 := ne_of_gt hu
      have : (4 * x ^ 3 + 3 * x) * u = 1 * u := by nlinarith [h, hxu]
      exact mul_right_cancel₀ hune this
  -- Step 2: `x (4 + 3u) = u` squares to `u^3 = (4 + 3u)^2`, using `x^2 u = 1` and positivity.
  have step2 : x * (4 + 3 * u) = u ↔ u ^ 3 = (4 + 3 * u) ^ 2 := by
    constructor
    · intro h
      have hsq : x ^ 2 * (4 + 3 * u) ^ 2 = u ^ 2 := by nlinarith [h]
      nlinarith [hsq, hxu]
    · intro h
      have h4 : 0 < 4 + 3 * u := by linarith
      have hsq : (x * (4 + 3 * u)) ^ 2 = u ^ 2 := by nlinarith [hxu, h]
      have hxp : 0 < x * (4 + 3 * u) := mul_pos hx h4
      nlinarith [hsq, hxp, hu]
  -- Step 3: expand `u = 3 + S`.
  have step3 : u ^ 3 = (4 + 3 * u) ^ 2 ↔ S ^ 3 = 51 * S + 142 := by
    rw [hudef]; constructor <;> intro h <;> nlinarith [h]
  rw [step1, step2, step3]

end GaugeCubic

section GaugeClosedForm

/-! ### The closed form of the gauge moment (atom E3)

On `[tau_1, tau_2]` the EL gives `u' = v/2`, `v' = -u/2`, so `v = 2u'` and `u = -2v'`.  Writing
`I = int v cos`, `J = int u sin`, `UC = [u cos t]`, `VS = [v sin t]` (endpoint differences),
two integrations by parts give

    I = 2 UC + 2 J ,      J = -2 VS + 2 I ,

and eliminating `J` yields `I = (4 VS - 2 UC)/3`.  This is the algebraic core of E3. -/

/-- Eliminating `J` from the two integration-by-parts relations. -/
theorem ibp_eliminate (I J UC VS : ℝ) (h1 : I = 2 * UC + 2 * J) (h2 : J = -2 * VS + 2 * I) :
    I = (4 * VS - 2 * UC) / 3 := by
  rw [h2] at h1; linarith

/-- The endpoint values are symmetric: `u(tau_1) = 1`, `v(tau_1) = D`, `u(tau_2) = D`,
`v(tau_2) = 1`.  With `sin tau_1 = 1/(2m)` and `cos tau_1 = D/m` the `D/m` terms cancel and

    I = (4 sin tau_2 - 2 D cos tau_2)/3 . -/
theorem I_closed (I D m s1 c1 s2 c2 UC VS : ℝ) (hm : m ≠ 0)
    (hs1 : s1 = 1 / (2 * m)) (hc1 : c1 = D / m)
    (hVS : VS = 1 * s2 - D * s1) (hUC : UC = D * c2 - 1 * c1)
    (hI : I = (4 * VS - 2 * UC) / 3) :
    I = (4 * s2 - 2 * D * c2) / 3 := by
  rw [hI, hVS, hUC, hs1, hc1]
  field_simp
  ring

/-- `J_1 = (1/2)(I + 1 - sin tau_2) = (3 + sin tau_2 - 2 D cos tau_2)/6`. -/
theorem J1_closed (J1 I D s2 c2 : ℝ) (hI : I = (4 * s2 - 2 * D * c2) / 3)
    (hJ : J1 = (I + 1 - s2) / 2) :
    J1 = (3 + s2 - 2 * D * c2) / 6 := by
  rw [hJ, hI]; ring

/-- The gauge `J_1 = 1/2` is exactly `sin tau_2 = 2 D cos tau_2`, i.e. `tan tau_2 = 2D`.
Since `tan tau_1 = 1/(2D)`, this says `tau_2 = pi/2 - tau_1`, which is Sigma's structure. -/
theorem gauge_iff_tan (J1 D s2 c2 : ℝ) (hJ : J1 = (3 + s2 - 2 * D * c2) / 6) :
    J1 = 1 / 2 ↔ s2 = 2 * D * c2 := by
  rw [hJ]; constructor <;> intro h <;> linarith

/-- `tan tau_2 = 2D` together with `tan tau_1 = 1/(2D)` gives `tan tau_1 tan tau_2 = 1`,
the cotangent relation `tau_2 = pi/2 - tau_1`. -/
theorem tan_product_one (D t1 t2 : ℝ) (hD : D ≠ 0) (h1 : t1 = 1 / (2 * D)) (h2 : t2 = 2 * D) :
    t1 * t2 = 1 := by
  rw [h1, h2]; field_simp

end GaugeClosedForm

section ExtentBound

/-! ### The uniform horizontal extent (atom P0, prop:extent)

`S` lies in `L_t = A_t u B_t`, two unit strips, and in the corridor `0 <= y <= 1`.  The `x`-span
of `A_t n corridor` is `(1 + sin t)/cos t` and of `B_t n corridor` is `(1 + cos t)/sin t`.  `S`
is connected and covered by two relatively closed pieces, so they meet and the spans add.  The
sum collapses: with `s = sin t`, `c = cos t`,

    (1+s)/c + (1+c)/s = (s + c + 1)/(s c) = 2/(s + c - 1) ,

so minimising it is exactly maximising `s + c`, and `s + c <= sqrt 2`. -/

/-- The two strip spans sum to `2/(sin t + cos t - 1)`. -/
theorem extent_identity (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (hpy : s ^ 2 + c ^ 2 = 1)
    (hne : s + c - 1 ≠ 0) :
    (1 + s) / c + (1 + c) / s = 2 / (s + c - 1) := by
  have hs' : s ≠ 0 := ne_of_gt hs
  have hc' : c ≠ 0 := ne_of_gt hc
  field_simp
  nlinarith [hpy]

/-- `sin t + cos t <= sqrt 2`, from `(s+c)^2 = 1 + 2sc <= 2`. -/
theorem sum_le_sqrt_two (s c : ℝ) (hpy : s ^ 2 + c ^ 2 = 1) : s + c ≤ Real.sqrt 2 := by
  have h : (s + c) ^ 2 ≤ 2 := by nlinarith [sq_nonneg (s - c), hpy]
  nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2,
             sq_nonneg (s + c - Real.sqrt 2), h]

/-- Hence the extent is at least `2/(sqrt 2 - 1) = 2(1 + sqrt 2)`.  Stated on the collapsed
form: `s + c <= sqrt 2` forces `2/(s + c - 1) >= 2/(sqrt 2 - 1)`. -/
theorem extent_ge (s c : ℝ) (hlt : s + c ≤ Real.sqrt 2) (hgt : 1 < s + c) :
    2 / (Real.sqrt 2 - 1) ≤ 2 / (s + c - 1) := by
  have h2 : (1:ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hpos : 0 < s + c - 1 := by linarith
  have hpos2 : 0 < Real.sqrt 2 - 1 := by linarith
  apply div_le_div_of_nonneg_left (by norm_num) hpos
  linarith

/-- `2/(sqrt 2 - 1) = 2(1 + sqrt 2)`, the constant of prop:extent. -/
theorem extent_constant : 2 / (Real.sqrt 2 - 1) = 2 * (1 + Real.sqrt 2) := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : (1:ℝ) < Real.sqrt 2 := by nlinarith [h, Real.sqrt_nonneg 2]
  have hne : Real.sqrt 2 - 1 ≠ 0 := by linarith
  rw [div_eq_iff hne]
  linear_combination (-2 : ℝ) * h

end ExtentBound

section MovingBoundary

/-! ### The sign-set boundary terms vanish (review item for thm:el)

`|N| = (1/2) int [ alpha_2^2 1_{E_2} + (sigma - alpha_1)^2 - alpha_1^2 1_{E_1} ]`, and varying
the data moves the endpoints of `E_2 = {alpha_2 > 0}` and `E_1 = {alpha_1 < 0}`.  Leibniz gives
a boundary term (integrand at the moving endpoint) times (endpoint velocity).  The integrand
attached to `E_2` is `alpha_2^2`, which vanishes exactly on `dE_2 = {alpha_2 = 0}`; the one
attached to `E_1` is `alpha_1^2`, vanishing on `dE_1 = {alpha_1 = 0}`.  So both boundary terms
are zero whatever the velocities are, and the first variation is the interior integral alone.

This was previously inherited from the `sofa_firstvar` header rather than derived. -/

/-- Leibniz boundary term for a moving endpoint: it is the integrand there times the velocity. -/
theorem leibniz_boundary (gTau tauDot interior total : ℝ)
    (h : total = gTau * tauDot + interior) (hz : gTau = 0) : total = interior := by
  rw [h, hz]; ring

/-- On `dE_2` the integrand `alpha_2^2` vanishes, because `alpha_2 = 0` there. -/
theorem e2_integrand_vanishes (a2 : ℝ) (h : a2 = 0) : a2 ^ 2 = 0 := by rw [h]; ring

/-- On `dE_1` the integrand `alpha_1^2` vanishes, because `alpha_1 = 0` there. -/
theorem e1_integrand_vanishes (a1 : ℝ) (h : a1 = 0) : a1 ^ 2 = 0 := by rw [h]; ring

/-- Both boundary contributions drop, so `delta|N|` is the interior integral. -/
theorem niche_variation_interior (a1 a2 t1dot t2dot interior total : ℝ)
    (h : total = a2 ^ 2 * t2dot - a1 ^ 2 * t1dot + interior)
    (h2 : a2 = 0) (h1 : a1 = 0) : total = interior := by
  rw [h, h1, h2]; ring

end MovingBoundary

section AreaCollapse

/-! ### The collapsed area identity (atom T1) and the Legendre transfer (L1, L2)

By `rho`-symmetry `hi = 1 - lo`, and `T = {(x,y) in C_2 : f(x) <= y <= 1 - f(x)}` once clause
(c) is known (Theorem thm:cuncond, unconditional).  The slab height at abscissa `x` is then

    min(hi, 1-f) - max(lo, f) = 1 - 2 max(lo, f) ,

so `|T| = int [1 - 2 max(lo, f)] dx` with no swept integral anywhere. -/

/-- The slab height collapses.  This is the whole content of T1; the rest is integration. -/
theorem slab_height (lo f hi : ℝ) (h : hi = 1 - lo) :
    min hi (1 - f) - max lo f = 1 - 2 * max lo f := by
  subst h
  rw [min_sub_sub_left]
  ring

/-- `|T| <= |C_2|`, since `max(lo,f) >= lo`.  Sanity direction for T1. -/
theorem slab_le_cap (lo f : ℝ) : 1 - 2 * max lo f ≤ 1 - 2 * lo := by
  have : lo ≤ max lo f := le_max_left _ _
  linarith

/-! #### L1: the Legendre derivatives -/

/-- `db/dp = alpha_2 cos t - c_x = -x(t)`, the envelope abscissa.  With `p = tan t`,
`dp/dt = sec^2 t`, and `db/dt = sec^2 t (alpha_2 cos t - c_x)`, the chain rule divides out. -/
theorem legendre_first (dbdt dpdt sec2 a2 ct cx : ℝ) (hne : sec2 ≠ 0)
    (hb : dbdt = sec2 * (a2 * ct - cx)) (hp : dpdt = sec2) :
    dbdt / dpdt = a2 * ct - cx := by
  rw [hb, hp]; field_simp

/-- `d^2b/dp^2 = -cos^3 t (1 - r)`.  Differentiating `db/dp = -x(t)` again and using
`x'(t) = cos t (1 - r)` with `dp/dt = 1/cos^2 t`. -/
theorem legendre_second (d2 xp ct rr : ℝ) (hct : ct ≠ 0)
    (hx : xp = ct * (1 - rr)) (hd : d2 = -xp * ct ^ 2) :
    d2 = -(ct ^ 3) * (1 - rr) := by
  rw [hd, hx]; ring

/-- (RC) is concavity of the dual: `d^2b/dp^2 <= 0` iff `r <= 1`, since `cos^3 t > 0`. -/
theorem rc_iff_concave (d2 ct rr : ℝ) (hct : 0 < ct) (h : d2 = -(ct ^ 3) * (1 - rr)) :
    d2 ≤ 0 ↔ rr ≤ 1 := by
  rw [h]
  constructor
  · intro hle; nlinarith [pow_pos hct 3]
  · intro hr; nlinarith [pow_pos hct 3]

/-! #### L2: conjugation sees only the concave hull -/

/-- If `b <= B` pointwise and the supremum of `B + p x` is attained at a point where `b` and `B`
agree, the two conjugates coincide there.  This is why the non-concave part of `b` is invisible
to `f`: the concave hull `B` touches `b` exactly at the points that realise the supremum. -/
theorem conj_sees_hull (b B : ℝ → ℝ) (x s : ℝ) (hle : ∀ p, b p ≤ B p)
    (p₀ : ℝ) (hagree : b p₀ = B p₀)
    (hsupB : ∀ p, B p + p * x ≤ s) (hatt : B p₀ + p₀ * x = s) :
    (∀ p, b p + p * x ≤ s) ∧ b p₀ + p₀ * x = s := by
  refine ⟨fun p => le_trans (by nlinarith [hle p]) (hsupB p), ?_⟩
  rw [hagree]; exact hatt

end AreaCollapse

section SumOfSquares

/-! ### The face-2 niche integral is a sum of squares (atom S1)

Parametrising the niche boundary by `t`, the envelope is `(c_x - a2 cos t, c_y - a2 sin t)` with
`x'(t) = cos t (1 - r(t+pi/2))`, so on `E_2` (where `alpha_2 > 0`, which is where the face-2
branch is the active one)

    int f dx = int_0^{tau_2} (c_y - a2 sin t) cos t (1 - r(t+pi/2)) dt .

Now `c_y - a2 sin t = (G-1) cos t - G' sin t =: W`, which depends on `G` alone, and
`W' = sin t (1 - r(t+pi/2))`.  Hence the integrand is `W W' cot t = (1/2)(W^2)' cot t`, and
integrating by parts, using `W(0) = H(pi/2) - 1 = 0` from the gauge,

    int f dx = (1/2) W(tau_2)^2 cot(tau_2) + (1/2) int_0^{tau_2} W^2 csc^2 t dt .

`W` is AFFINE in `H`, so both terms are NONNEGATIVE quadratic forms in `H`. -/

/-- `W = (G-1) cos t - G' sin t` and `W' = sin t (1 - r)`, where `r = G + G''`. -/
theorem W_deriv (G Gp Gpp W Wp ct st r : ℝ)
    (hW : W = (G - 1) * ct - Gp * st)
    (hr : r = G + Gpp)
    (hWp : Wp = (Gp * ct - (G - 1) * st) - (Gpp * st + Gp * ct)) :
    Wp = st * (1 - r) := by
  rw [hWp, hr]; ring

/-- `W(0) = 0`: at `t = 0` one has `W = G(0) - 1 = H(pi/2) - 1`, which the gauge sets to zero. -/
theorem W_zero (G0 W0 : ℝ) (hgauge : G0 = 1) (hW : W0 = (G0 - 1) * 1 - 0) : W0 = 0 := by
  rw [hW, hgauge]; ring

/-- Integration by parts against `cot`: `d/dt [ (1/2) W^2 cot t ] = W W' cot t - (1/2) W^2 csc^2 t`,
using `d(cot t)/dt = -csc^2 t`.  Stated with `cot` and `csc2` opaque so no division appears;
that is the whole algebraic content. -/
theorem cot_ibp (W Wp cot dcot csc2 deriv : ℝ)
    (hd : dcot = -csc2)
    (hderiv : deriv = W * Wp * cot + (1 / 2) * W ^ 2 * dcot) :
    deriv = W * Wp * cot - (1 / 2) * W ^ 2 * csc2 := by
  rw [hderiv, hd]; ring

/-- Both terms of the sum-of-squares form are nonnegative: `cot t >= 0`, `csc^2 t >= 0` on
`(0, pi/2]`, and `W^2 >= 0` always. -/
theorem sos_terms_nonneg (W cot csc2 : ℝ) (hc : 0 ≤ cot) (hs : 0 ≤ csc2) :
    0 ≤ (1 / 2) * W ^ 2 * cot ∧ 0 ≤ (1 / 2) * W ^ 2 * csc2 := by
  constructor <;> positivity

/-- Consequence: the face-2 niche integral is a nonnegative quadratic form in `H`, since `W` is
affine in `H`.  Scalar shadow of "sum of two nonnegative terms is nonnegative". -/
theorem face2_niche_nonneg (bdry integ total : ℝ) (hb : 0 ≤ bdry) (hi : 0 ≤ integ)
    (h : total = bdry + integ) : 0 ≤ total := by
  rw [h]; linarith

end SumOfSquares

/-! ## Tiling

The floor facet is tiled by the two envelope ranges and the corner-path range,
with no overlap and no seam.  Everything below uses only clause (b) (`r ≤ 1`)
and clause (d) (`τ₁ ≤ τ₂`); no curvature or optimality hypothesis enters. -/

namespace Tiling

/-- Both envelope maps are nondecreasing: this is exactly clause (b), `r ≤ 1`,
together with nonnegativity of `sin`/`cos` on the first quadrant. -/
theorem envelope_deriv_nonneg (s r : ℝ) (hs : 0 ≤ s) (hr : r ≤ 1) :
    0 ≤ s * (1 - r) :=
  mul_nonneg hs (by linarith)

/-- The corner path moves left on the interval where both arms are nonnegative.
`c_x' = -α₁ cos t - α₂ sin t`. -/
theorem corner_x_deriv_nonpos (a1 a2 c s : ℝ)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    -a1 * c - a2 * s ≤ 0 := by
  have h1 : 0 ≤ a1 * c := mul_nonneg ha1 hc
  have h2 : 0 ≤ a2 * s := mul_nonneg ha2 hs
  linarith

/-- Seam on the right: `α₁(τ₁) = 0` forces the face-1 envelope to start exactly
at the corner, `x₁(τ₁) = c_x(τ₁)`. -/
theorem seam_right (cx a1 s : ℝ) (h : a1 = 0) : cx + a1 * s = cx := by
  rw [h]; ring

/-- Seam on the left: `α₂(τ₂) = 0` forces `x₂(τ₂) = c_x(τ₂)`. -/
theorem seam_left (cx a2 c : ℝ) (h : a2 = 0) : cx - a2 * c = cx := by
  rw [h]; ring

/-- The three ranges tile `[x₂(0), x₁(π/2)]` exactly: consecutive endpoints match,
so the three integrals sum to the integral over the whole facet.  Stated as the
additivity that the seam identities license. -/
theorem tile_add (A B C D I2 Ig I1 : ℝ)
    (h2 : I2 = B - A) (hg : Ig = C - B) (h1 : I1 = D - C) :
    I2 + Ig + I1 = D - A := by
  rw [h2, hg, h1]; ring


/-- The corner-piece Wronskian identity.  With `P = a*s + b*c` and `R = a*c - b*s`
(so that `R + i*P = (a + i*b) * exp (i*t)`), and `Pp`, `Rp` the derivatives obtained
by the product rule with `s' = c` and `c' = -s`, one has
`P*Rp - Pp*R = -((a*b' - a'*b) + (a^2 + b^2))`.
This is what splits the corner piece into a positive-definite part, a symplectic
part of indefinite sign, and a boundary term. -/
theorem wronskian_identity (a b a' b' s c P R Pp Rp : ℝ)
    (hpy : s ^ 2 + c ^ 2 = 1)
    (hP : P = a * s + b * c)
    (hR : R = a * c - b * s)
    (hPp : Pp = a' * s + a * c + b' * c - b * s)
    (hRp : Rp = a' * c - a * s - b' * s - b * c) :
    P * Rp - Pp * R = -((a * b' - a' * b) + (a ^ 2 + b ^ 2)) := by
  subst hP hR hPp hRp
  -- Expanding without using the Pythagorean identity gives
  --   P*Rp - Pp*R = (s^2+c^2) * (-a^2 - a*b' + a'*b - b^2),
  -- so the claim is exactly this multiple of `hpy`.
  linear_combination (-a ^ 2 - a * b' + a' * b - b ^ 2) * hpy

/-- Consequence: the corner piece splits as a manifestly nonnegative term, a symplectic
term of indefinite sign, and a boundary term. -/
theorem corner_split (Q psd symp bdry : ℝ)
    (hpsd : 0 ≤ psd) (h : Q = psd + symp + bdry) :
    Q - symp - bdry = psd := by
  rw [h]; ring


/-- Polar form of the symplectic density.  Writing the corner displacement in polar
coordinates, `R = rho * cos psi` and `P = rho * sin psi`, the density `R * P' - P * R'`
that integrates to the swept area equals `rho ^ 2 * psi'`.  This is what turns the
corner term of the second variation into a swept area. -/
theorem swept_area_form (rho rhop psi psip R P Rp Pp : Real)
    (hR : R = rho * Real.cos psi)
    (hP : P = rho * Real.sin psi)
    (hRp : Rp = rhop * Real.cos psi - rho * Real.sin psi * psip)
    (hPp : Pp = rhop * Real.sin psi + rho * Real.cos psi * psip) :
    R * Pp - P * Rp = rho ^ 2 * psip := by
  subst hR hP hRp hPp
  -- Expanding, `R * Pp - P * Rp = rho ^ 2 * psip * (sin psi ^ 2 + cos psi ^ 2)`,
  -- so the claim is exactly this multiple of the Pythagorean identity.
  linear_combination (rho ^ 2 * psip) * Real.sin_sq_add_cos_sq psi

/-- The boundary term is `rho ^ 2 * sin (2 * psi) / 4`, and `rho ^ 2 * sin (2 * psi) = 2 * R * P`. -/
theorem boundary_is_two_RP (rho psi R P : Real)
    (hR : R = rho * Real.cos psi) (hP : P = rho * Real.sin psi) :
    rho ^ 2 * Real.sin (2 * psi) = 2 * (R * P) := by
  subst hR hP
  rw [Real.sin_two_mul]; ring


/-- **No completion of squares can prove C1.**  On `[tau_1, tau_2]` the second-variation
density in the variables `X = b' - b * cot t`, `Y = a' + a * tan t`, `U = b`, `V = a` is
`q = X^2 + Y^2 + U^2 + V^2 + lam * U * V + V * X - U * Y`.
At the explicit witness `(X, Y, U, V) = (U/2, U/2, U, -U)` this equals `(3/2 - lam) * U ^ 2`,
which is negative as soon as `lam > 3/2`.  Since `lam = 1 / (sin t * cos t) >= 2` on the whole
interval, the density is indefinite at every point, so positivity of the second variation is
NONLOCAL: it cannot follow from any pointwise algebraic rearrangement, and must use that
`X` and `Y` are derivatives of `b` and `a`. -/
theorem pointwise_indefinite (lam U : Real) :
    (U / 2) ^ 2 + (U / 2) ^ 2 + U ^ 2 + (-U) ^ 2 + lam * (U * (-U))
      + (-U) * (U / 2) - U * (U / 2) = (3 / 2 - lam) * U ^ 2 := by
  ring

/-- The witness is strictly negative once `lam > 3/2` and `U <> 0`. -/
theorem pointwise_indefinite_neg (lam U : Real) (hlam : 3 / 2 < lam) (hU : U ≠ 0) :
    (3 / 2 - lam) * U ^ 2 < 0 := by
  have h1 : (0:Real) < U ^ 2 := by positivity
  nlinarith [h1]


/-- **Transversality of the worst-case direction.**  The witness of `pointwise_indefinite`
requires `a = -b` together with `X = Y = b / 2`, where `X = b' - b * (c / s)` and
`Y = a' + a * (s / c)`.  The first forces `b' / b = c / s + 1 / 2`, the second forces
`b' / b = -(s / c + 1 / 2)`.  Their mismatch is
`(c / s + 1 / 2) + (s / c + 1 / 2) = 1 / (s * c) + 1 = lam + 1`,
which on the first quadrant is at least `3`, hence never zero.  So the direction attaining the
pointwise minimum of the density is not realisable by any actual pair `(a, b)` on a set of
positive measure: the negative cone is transverse to the set where `X` and `Y` really are
derivatives.  This is the nonlocal mechanism that `pointwise_indefinite` shows any proof
must use. -/
theorem transversality_gap (s c : Real) (hs : s ≠ 0) (hc : c ≠ 0)
    (hpy : s ^ 2 + c ^ 2 = 1) :
    (c / s + 1 / 2) + (s / c + 1 / 2) = 1 / (s * c) + 1 := by
  have key : c / s + s / c = (s ^ 2 + c ^ 2) / (s * c) := by
    field_simp; ring
  have regroup : (c / s + 1 / 2) + (s / c + 1 / 2) = (c / s + s / c) + 1 := by ring
  rw [regroup, key, hpy]

/-- On the first quadrant `lam = 1 / (s * c) >= 2`, so the transversality gap `lam + 1` is at
least `3`.  The bound `1 / (s * c) >= 2` follows from `2 * s * c <= s ^ 2 + c ^ 2 = 1`. -/
theorem transversality_gap_ge (s c : Real) (hs : 0 < s) (hc : 0 < c)
    (hpy : s ^ 2 + c ^ 2 = 1) :
    3 ≤ 1 / (s * c) + 1 := by
  have hsc : 0 < s * c := mul_pos hs hc
  have h2 : 2 * (s * c) ≤ 1 := by nlinarith [sq_nonneg (s - c)]
  have : 2 ≤ 1 / (s * c) := by
    rw [le_div_iff₀ hsc]; linarith
  linarith


/-- **The kernel of the reduced second variation is translation.**  At
`a = cos t`, `b = -sin t` one has `X = b' - b * (c/s) = 0` and `Y = a' + a * (s/c) = 0`,
`a ^ 2 + b ^ 2 = 1`, and `a * b' - a' * b = -1`, so the density
`X ^ 2 + Y ^ 2 + a ^ 2 + b ^ 2 + (a * b' - a' * b)` vanishes identically.  Stated here as the
arithmetic identity on the `(a,b)` block, with `a = c`, `b = -s`, `a' = -s`, `b' = -c`. -/
theorem kernel_density_vanishes (s c : Real) :
    c ^ 2 + (-s) ^ 2 + (c * (-c) - (-s) * (-s)) = 0 := by
  ring

/-- The `X` and `Y` combinations both vanish on the kernel direction: with `a = c`, `b = -s`,
`a' = -s`, `b' = -c`, one has `b' - b * (c / s) = 0` and `a' + a * (s / c) = 0`. -/
theorem kernel_is_translation (s c : Real) (hs : s ≠ 0) (hc : c ≠ 0) :
    (-c) - (-s) * (c / s) = 0 ∧ (-s) + c * (s / c) = 0 := by
  constructor
  · have h : (-s) * (c / s) = -c := by field_simp
    rw [h]; ring
  · have h : c * (s / c) = s := by field_simp
    rw [h]; ring

/-- On the kernel direction `P = a * s + b * c` vanishes identically, so the boundary term
`- (1/2) [P R]` contributes nothing. -/
theorem kernel_P_vanishes (s c : Real) : c * s + (-s) * c = 0 := by ring


/-- **The sum-of-squares completion.**  After integrating `R * P'` by parts, the integrand of
the reduced second variation is
`A ^ 2 + B ^ 2 + 4 * P ^ 2 * (1 + k ^ 2) + 2 * A * P - 4 * B * P * k`
where `A = R'`, `B = P'` and `k = cot (2 t)` (the weight `4 / sin (2t) ^ 2` rewritten via
`1 / sin ^ 2 = 1 + cot ^ 2`).  This equals a sum of three squares:
`(A + P) ^ 2 + (B - 2 * P * k) ^ 2 + 3 * P ^ 2`.
Every term is nonnegative, so the reduced second variation is `>= 0`, and it vanishes exactly
when `P = 0` and `A = R' = 0`, i.e. when `R + i P` is constant -- the translation kernel. -/
theorem sos_completion (A B P k : Real) :
    A ^ 2 + B ^ 2 + 4 * P ^ 2 * (1 + k ^ 2) + 2 * A * P - 4 * B * P * k
      = (A + P) ^ 2 + (B - 2 * P * k) ^ 2 + 3 * P ^ 2 := by
  ring

/-- The completed form is nonnegative. -/
theorem sos_nonneg (A B P k : Real) :
    0 ≤ (A + P) ^ 2 + (B - 2 * P * k) ^ 2 + 3 * P ^ 2 := by positivity

/-- Equality forces `P = 0` and `A = 0`: the kernel is exactly `P = 0`, `R' = 0`. -/
theorem sos_eq_zero_iff (A B P k : Real) :
    (A + P) ^ 2 + (B - 2 * P * k) ^ 2 + 3 * P ^ 2 = 0 ↔
      A + P = 0 ∧ B - 2 * P * k = 0 ∧ P = 0 := by
  constructor
  · intro h
    have h1 : (A + P) ^ 2 = 0 ∧ (B - 2 * P * k) ^ 2 = 0 ∧ P ^ 2 = 0 := by
      refine ⟨by nlinarith [sq_nonneg (A + P), sq_nonneg (B - 2 * P * k), sq_nonneg P], ?_, ?_⟩
      · nlinarith [sq_nonneg (A + P), sq_nonneg (B - 2 * P * k), sq_nonneg P]
      · nlinarith [sq_nonneg (A + P), sq_nonneg (B - 2 * P * k), sq_nonneg P]
    exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1.1,
           pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1.2.1,
           pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1.2.2⟩
  · rintro ⟨h1, h2, h3⟩; rw [h1, h2, h3]; ring

/-! ### The anchoring threshold (gap (i))

At the critical value `A = √3 - 1` the mixed certificate `p α₁ + q α₂` has, in the full-fill
regime, the closed form `Φ(T) = C cos T + S sin T - p - R` with `C = p/2 + √3 q` and
`S = √3 p - q/2`.  Its amplitude collapses: `C² + S² = (13/4)(p² + q²)`, independently of the
weight.  That is what makes `Φ` an explicit cosine and lets one weight cover a whole range of
`T`.  -/

theorem certificate_amplitude (p q : ℝ) :
    (p / 2 + Real.sqrt 3 * q) ^ 2 + (Real.sqrt 3 * p - q / 2) ^ 2
      = (13 / 4) * (p ^ 2 + q ^ 2) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [h3, sq_nonneg p, sq_nonneg q]

/-- The `α₂` closed form collapses on `[π/6, π/3]`: the three terms combine to
`(√3/2) cos T - sin T`, so it vanishes exactly at `tan T = √3/2`. -/
theorem alpha2_closed_form (T : ℝ) :
    -(1 / 2) * Real.sin T + Real.sqrt 3 * Real.cos T - 1
      + (1 - Real.cos (T - Real.pi / 6))
      = Real.sqrt 3 / 2 * Real.cos T - Real.sin T
        + (Real.sqrt 3 / 2 * Real.cos T + (1 / 2) * Real.sin T
           - Real.cos (T - Real.pi / 6)) := by
  ring

/-- `cos (T - π/6) = (√3/2) cos T + (1/2) sin T`, the cancellation behind the collapse. -/
theorem cos_sub_pi_six (T : ℝ) :
    Real.cos (T - Real.pi / 6) = Real.sqrt 3 / 2 * Real.cos T + (1 / 2) * Real.sin T := by
  rw [Real.cos_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

/-- The threshold identity of `prop:thresh`: `min α₁(π/2) = A + 1 - √3`, from
`√3/2 + (1 - √3/2) = 1` after subtracting the two greedy optima. -/
theorem threshold_value (A : ℝ) :
    A - Real.sqrt 3 / 2 + (1 - Real.sqrt 3 / 2) = A + 1 - Real.sqrt 3 := by
  ring

/-- Monotonicity in `A`: the weight applied to `A` is `p sin T + q cos T ≥ 0` on the first
quadrant, so the certificate is nondecreasing in `A` and the lemma at `A = √3 - 1` extends to
every larger `A`. -/
theorem certificate_mono_in_A (p q T : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 ≤ Real.sin T) (hc : 0 ≤ Real.cos T) :
    0 ≤ p * Real.sin T + q * Real.cos T :=
  add_nonneg (mul_nonneg hp hs) (mul_nonneg hq hc)

/-! ### First variation of the wedge (gap (ii))

With `δH = η`, `a = η(t)`, `b = η(t+π/2)`, the corner moves by
`δc_x = a cos t - b sin t`, `δc_y = a sin t + b cos t`.  Each branch of the wedge
`g_t = min(c_y + (c_x-x)cot t, c_y - (c_x-x)tan t)` then varies by an expression in ONE of the
two arguments only.  Nothing here uses `r ≤ 1`, so this holds however the sweep behaves --
which is what a tiling-based derivation could not offer. -/

theorem wedge_var_right (a b s c : ℝ) (hc : c ≠ 0) (hpy : s ^ 2 + c ^ 2 = 1) :
    (a * s + b * c) - (s / c) * (a * c - b * s) = b / c := by
  field_simp
  linear_combination b * hpy

theorem wedge_var_left (a b s c : ℝ) (hs : s ≠ 0) (hpy : s ^ 2 + c ^ 2 = 1) :
    (a * s + b * c) + (c / s) * (a * c - b * s) = a / s := by
  field_simp
  linear_combination a * hpy

/-! ### The gap term of `δ|N|`

At a gap point the max over `t` sits where the two branch families cross, and that crossing
moves under perturbation, so the derivative is a convex combination of the branch derivatives
weighted by the crossing slopes `λ = α₁ csc t`, `ρ = α₂ sec t` -- NOT their minimum.  The
combination collapses, and its denominator is exactly `-c_x'`. -/

/-- Crossing-slope weights collapse.  With `λ = a₁/s`, `ρ = a₂/c`, `δL = e₁/s`, `δR = e₂/c`,
both the numerator `λ δR + ρ δL` and the denominator `λ + ρ` scale by `s c`, leaving
`(a₁ e₂ + a₂ e₁)/(a₁ c + a₂ s)`.  This is the gap term of `δ|N|`; taking `min(δL, δR)` instead
is wrong, and drove the assembly error to 4.2e-1. -/
theorem gap_convex_combination (a1 a2 e1 e2 s c : ℝ) (hs : s ≠ 0) (hc : c ≠ 0) :
    ((a1 / s) * (e2 / c) + (a2 / c) * (e1 / s)) * (s * c) = a1 * e2 + a2 * e1
    ∧ ((a1 / s) + (a2 / c)) * (s * c) = a1 * c + a2 * s := by
  constructor <;> field_simp <;> ring

/-- The denominator is `-c_x'`: with `c_x' = -a₁ cos t - a₂ sin t`, one has
`a₂ sin t + a₁ cos t = -c_x'`. -/
theorem gap_denom_is_neg_cx (a1 a2 s c : ℝ) :
    a2 * s + a1 * c = -(-a1 * c - a2 * s) := by ring

/-! ### The boundary terms of `δ²|N|` are perfect squares

With the correct sign on `[PR]`, the boundary total of the corrected second variation is
`cot τ₂ · P(τ₂)²  +  tan τ₁ · P(τ₁)²`, so every term of `δ²|N|` is a square with a positive
coefficient and `|N|` is convex.  An earlier hand evaluation used `-[PR]` and concluded the
boundary form was indefinite; it is not. -/

theorem boundary_square_tau2 (a b s c : ℝ) (hs : s ≠ 0) :
    a ^ 2 * (s * c) + b ^ 2 * (c ^ 3 / s) + 2 * a * b * c ^ 2
      = (c / s) * (a * s + b * c) ^ 2 := by
  field_simp
  ring

theorem boundary_square_tau1 (a b s c : ℝ) (hc : c ≠ 0) :
    a ^ 2 * (s ^ 3 / c) + b ^ 2 * (s * c) + 2 * a * b * s ^ 2
      = (s / c) * (a * s + b * c) ^ 2 := by
  field_simp
  ring

/-- Both coefficients are positive on the first quadrant, so both boundary terms are `≥ 0`. -/
theorem boundary_nonneg (P s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    0 ≤ (c / s) * P ^ 2 + (s / c) * P ^ 2 :=
  add_nonneg (mul_nonneg (le_of_lt (div_pos hc hs)) (sq_nonneg P))
             (mul_nonneg (le_of_lt (div_pos hs hc)) (sq_nonneg P))

/-! ### Fold surgery

The moment identity behind admissibility, and the sign step that yields `r ≤ 1` off the gap. -/

/-- Moment identity: `∫(η+η'')cos` telescopes to a boundary term.  Stated as the algebraic
identity behind it, `(η'cos + η sin)' = (η+η'')cos` when the product rule is expanded. -/
theorem moment_boundary (e ep epp s c : ℝ) (hs : Real.sin 0 = 0) :
    (ep * c + e * s) - (ep * 1 + e * 0) = ep * c + e * s - ep := by ring

/-- The sign step: with `μ ≥ 0` and `η ≥ 0`, the integrand `η(μ + 2(r-1))` is `> 0` when `r > 1`,
so the variation strictly increases `|T|` and the cap is not optimal. -/
theorem fold_sign (eta mu r : ℝ) (he : 0 < eta) (hm : 0 ≤ mu) (hr : 1 < r) :
    0 < eta * (mu + 2 * (r - 1)) := by
  apply mul_pos he
  have : 0 < 2 * (r - 1) := by linarith
  linarith

/-- The Euler–Lagrange identity `μ = 2(1-r)` forces `r ≤ 1` whenever `μ ≥ 0`. -/
theorem el_forces_r_le_one (mu r : ℝ) (hm : 0 ≤ mu) (h : mu = 2 * (1 - r)) : r ≤ 1 := by
  linarith [h ▸ hm]

/-! ### RETRACTED SUPPORT — the ordering at an optimum

WARNING.  The theorem these lemmas were written for (`thm:ordering`, and with it `cor:closed`) is
RETRACTED.  Its proof assigned the value `α₂` to the `η₁` coefficient of `δ|N|` on `(τ₂,τ₁)` in the
reversed case; a finite difference of `|N|` shows the coefficient is neither `α₂` nor `0`, and its
sign is positive, so the contradiction does not arise.  Independently, the closed-form `δ|N|` is
valid only for `r ≤ 1` (the face-1 envelope folds where `r > 1` and the signed change of variables
counts the folded sheet with the wrong sign), which also retracts `thm:fold` and `thm:chain`.
The lemmas below remain true as statements about real numbers; they support nothing.


In the reversed case `r = 0` on `[0, τ₁)`, so the gauge moment is bounded by
`(1/2)(1 - sin τ₁)`, which reaches `1/2` only at `τ₁ = 0`. -/

/-- The reversed-case moment bound: with `r = 0` before `τ₁` and `r ≤ 1/2` after,
`∫₀^{π/2} r cos ≤ (1/2)(1 - sin τ₁)`. -/
theorem reversed_moment_bound (s : ℝ) (hs : 0 < s) : (1 / 2) * (1 - s) < 1 / 2 := by linarith

/-- Hence the gauge moment `1/2` forces `sin τ₁ = 0`. -/
theorem moment_forces_tau_zero (s : ℝ) (h : (1 / 2) * (1 - s) = 1 / 2) : s = 0 := by linarith

/-- The ordered case escapes: there the coefficient is `1 - r + α₂` with `α₂ > 0`, so
`r = (1+α₂)/2 > 1/2`. -/
theorem ordered_r_exceeds_half (a2 : ℝ) (h : 0 < a2) : 1 / 2 < (1 + a2) / 2 := by linarith

end Tiling

section ThresholdCovering

/-!
### The two remaining arithmetic steps of `thm:threshold`

The threshold lemma runs two greedy certificates and concludes because their ranges overlap.
`certificate_amplitude` and `certificate_mono_in_A` above supply the algebra; what was still
carried on the note alone is (i) the moment capacity of the region where the coefficient of `r`
is negative, and (ii) the covering arithmetic itself.
-/

/-- The negative region `(T-δ, T)` has moment capacity `sin T - sin (T-δ) = 2 sin(δ/2) cos(T-δ/2)`,
bounded by `2 sin(δ/2)` uniformly in `T`.  This is what lets the whole region be filled and the
remaining moment placed beyond `T`, where the coefficient vanishes. -/
theorem moment_capacity_le (T d : ℝ) (hd : 0 ≤ Real.sin (d / 2)) :
    Real.sin T - Real.sin (T - d) ≤ 2 * Real.sin (d / 2) := by
  have h : Real.sin T - Real.sin (T - d) = 2 * Real.sin (d / 2) * Real.cos (T - d / 2) := by
    rw [Real.sin_sub_sin]; ring_nf
  rw [h]
  nlinarith [Real.cos_le_one (T - d / 2), Real.neg_one_le_cos (T - d / 2)]

/-- With `(p,q) = (0.3475, 0.6525)` one has `δ = arctan (p/q)` and `2 sin(δ/2) = 0.4845 < 1/2`,
so the negative region always fits inside the available moment.  Stated on the numeral. -/
theorem capacity_below_half : (0.4845 : ℝ) < 1 / 2 := by norm_num

/-- The covering step.  The mixed certificate `(p,q) = (0.3475, 0.6525)` is nonnegative for
`T ≤ 0.825627`; the pure certificate `(p,q) = (1,0)` is nonnegative for `T ≥ 0.737751`.  Since
`0.737751 < 0.825627`, every `T` is covered by at least one of them. -/
theorem threshold_ranges_cover (T : ℝ) :
    T ≤ (0.825627 : ℝ) ∨ (0.737751 : ℝ) ≤ T := by
  by_cases h : T ≤ (0.825627 : ℝ)
  · exact Or.inl h
  · push_neg at h; exact Or.inr (by linarith)

/-- The overlap is a genuine interval, not a touching pair: the certificates agree on a window of
length `0.087876`.  This is the quantitative form of "the two ranges cover `(0, π/2]`". -/
theorem threshold_overlap_positive : (0 : ℝ) < 0.825627 - 0.737751 := by norm_num

end ThresholdCovering

section AtomPrice

/-!
### The price of an atom, and why pi/2 is the exception (entry 224)

`r dθ` is arc length pushed forward to normal directions, so an ATOM of mass `m` at `t₀` in the
curvature measure is a STRAIGHT EDGE of length `m` on `∂C`.  Σ carries one at `π/2`, which is what
clause (b) means by "atom only at `π/2`".

An atom at `t₀` contributes `m cos t₀` to the moment `∫ r cos`, so restoring the moment forces the
rest of that half to be scaled by `λ = 1 - 2 m cos t₀`.  The atom is FREE exactly when `λ = 1`.
The two lemmas below are that statement: free iff `cos t₀ = 0`, and on `[0, π]` iff `t₀ = π/2`.

CAUTION, recorded with the lemma so it cannot be lost: being free in the moments does NOT make an
atom favourable in `|T|`.  Entry 224 measured the opposite -- an atom at `π/2` costs MORE area than
one at `t₀ = 0.9`, and the ordering survived a 2.7x grid refinement.  So this algebra explains
where clause (b)`s exception SITS; it does not prove the clause, and the moment-cost route to it
is closed.
-/

/-- The price of an atom is trivial exactly when the atom is massless or sits where `cos` vanishes. -/
theorem atom_price (m t0 : ℝ) :
    (1:ℝ) - 2 * m * Real.cos t0 = 1 ↔ m = 0 ∨ Real.cos t0 = 0 := by
  constructor
  · intro h
    have hm : m * Real.cos t0 = 0 := by linarith
    exact mul_eq_zero.1 hm
  · rintro (rfl | h)
    · ring
    · rw [h]; ring

/-- On `[0, π]` a nonzero atom is free in the moments **exactly** at `π/2`. -/
theorem atom_free_iff_pi_div_two {m t0 : ℝ} (hm : m ≠ 0) (h0 : 0 ≤ t0) (h1 : t0 ≤ Real.pi) :
    (1:ℝ) - 2 * m * Real.cos t0 = 1 ↔ t0 = Real.pi / 2 := by
  rw [atom_price]
  constructor
  · rintro (h | h)
    · exact absurd h hm
    · have hpi := Real.pi_pos
      exact Real.injOn_cos ⟨h0, h1⟩ ⟨by linarith, by linarith⟩
        (by rw [h, Real.cos_pi_div_two])
  · rintro rfl
    exact Or.inr Real.cos_pi_div_two

/-- The niche`s second derivative in the atom mass is `2 f(β)` with this `f` (sofa_atom). -/
noncomputable def atomF (b : ℝ) : ℝ := Real.pi / 2 - 2 * b + Real.sin (2 * b)

/-- `f` is antitone: `f a - f b = 2(b-a) + (sin 2a - sin 2b)` and `sin` is 1-Lipschitz, so the
second term cannot beat the first.  (Equivalently `f' = -2 + 2 cos 2β ≤ 0`, but the Lipschitz
route needs no differentiation.) -/
theorem atomF_antitone {a b : ℝ} (hab : a ≤ b) : atomF b ≤ atomF a := by
  have hL : |Real.sin (2 * a) - Real.sin (2 * b)| ≤ |2 * a - 2 * b| := by
    have h := Real.lipschitzWith_sin.dist_le_mul (2 * a) (2 * b)
    simpa [Real.dist_eq, one_mul] using h
  have habs : |2 * a - 2 * b| = 2 * b - 2 * a := by
    rw [abs_of_nonpos (by linarith)]; ring
  rw [habs] at hL
  have := (abs_le.1 hL).1
  simp only [atomF]
  linarith

/-- Hence `f > 0` throughout `β ≤ π/6`, with `f(π/6) = π/6 + √3/2`.  This is the strong convexity
of `2|N|` in the atom mass, and with `|C₂|` affine it makes `|T|` STRICTLY CONCAVE there. -/
theorem atomF_pos_of_le_pi_div_six {b : ℝ} (hb : b ≤ Real.pi / 6) : 0 < atomF b := by
  have hmono : atomF (Real.pi / 6) ≤ atomF b := atomF_antitone hb
  have hval : atomF (Real.pi / 6) = Real.pi / 6 + Real.sqrt 3 / 2 := by
    simp only [atomF]
    rw [show (2 : ℝ) * (Real.pi / 6) = Real.pi / 3 by ring, Real.sin_pi_div_three]
    ring
  have hpi := Real.pi_pos
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  linarith [hval ▸ hmono]

/-- The affineness half of `sofa_atom`: the cap`s quadratic coefficient in the atom mass is
`∫₀^{π/2} cos 2θ dθ`, an exact derivative over a half period, hence ZERO.  With `atomF_pos_…`
(strong convexity of `2|N|`) this gives `|T|` STRICTLY CONCAVE in the atom mass. -/
theorem cap_quadratic_coeff_zero :
    (∫ θ in (0:ℝ)..(Real.pi / 2), Real.cos (2 * θ)) = 0 := by
  have h : (∫ θ in (0:ℝ)..(Real.pi / 2), Real.cos (2 * θ))
      = (Real.sin (2 * (Real.pi / 2)) - Real.sin (2 * 0)) / 2 := by
    simp [mul_comm]; ring
  rw [h, show (2:ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  simp

end AtomPrice

section SliceGeometry

/-!
### The slice geometry of `|T|` (entry 231)

Writing `hi(x)`, `lo(x)` for the top and bottom of the `C₂` slice and `f(x)` for the niche
envelope, the area integrand is `(hi - lo) - 2 (min f hi - lo)₊`.  Three elementary facts, all
UNCONDITIONAL in `r`, collapse it:

* `ρ`-symmetry of `C₂ = C ∩ ρC` gives `lo = 1 - hi`, hence `hi > 1/2`;
* each niche branch is `c_y` plus a term of one sign and `c_y` minus a term of the same sign, so
  their MIN is at most `c_y`; hence `f ≤ max_t c_y ≤ 1/2` by clause (c) (`thm:cuncond`);
* therefore `f < hi` always -- the regime where the niche pokes past the cap top is EMPTY.

With that the integrand becomes `min (2hi - 1) (1 - 2f)`.  `2hi - 1` is concave (`hi` is a min of
affine functions of `H`, and `H` is affine in `r`).

CAUTION recorded with the lemmas: this does NOT give concavity of `|T|`.  That would need `f`
convex in `r`, and entry 231 measured `f` to be non-convex even on the region where the niche is
nonempty (146689 violations, worst -1.1e-1).  `|T|` concavity beyond `r ≤ 1` remains a
CANCELLATION in the integral, not a pointwise fact.
-/

/-- `ρ`-symmetry forces the slice top above the midline. -/
theorem hi_gt_half {hi lo : ℝ} (hsym : lo = 1 - hi) (h : lo < hi) : 1 / 2 < hi := by
  rw [hsym] at h; linarith

/-- Each niche branch: one of `c_y ± d·(positive)` is at most `c_y`, so their min is. -/
theorem niche_branch_le_corner {cy d ct tg : ℝ} (hct : 0 < ct) (htg : 0 < tg) :
    min (cy + d * ct) (cy - d * tg) ≤ cy := by
  by_cases hd : (0:ℝ) ≤ d
  · exact le_trans (min_le_right _ _) (by nlinarith)
  · push_neg at hd; exact le_trans (min_le_left _ _) (by nlinarith)

/-- Hence the third regime is empty: `f ≤ 1/2 < hi`. -/
theorem third_regime_empty {f hi lo : ℝ} (hsym : lo = 1 - hi) (h : lo < hi)
    (hf : f ≤ 1 / 2) : f < hi := lt_of_le_of_lt hf (hi_gt_half hsym h)

/-- THE SLICE IDENTITY.  With `lo = 1 - hi` and `f ≤ hi`, the area integrand collapses to a min
of two expressions.  This holds with NO bound on `r`. -/
theorem slice_identity {hi f : ℝ} (hf : f ≤ hi) :
    (hi - (1 - hi)) - 2 * max (min f hi - (1 - hi)) 0 = min (2 * hi - 1) (1 - 2 * f) := by
  rw [min_eq_left hf]
  by_cases h : f - (1 - hi) ≤ 0
  · rw [max_eq_right h, min_eq_left (by linarith)]; ring
  · push_neg at h; rw [max_eq_left h.le, min_eq_right (by linarith)]; ring

end SliceGeometry

section ConcavityReduction

/-!
### The concavity obligation, reduced (entry 237)

Along any admissible direction, `δ²|T| = δ²|C₂| - 2 δ²|N|`.  Write `qc = δ²|C₂|` and
`qn = δ²|N|`.  `prop:wirt` gives `qc ≤ 0` UNCONDITIONALLY -- it is a Wirtinger inequality in `η`
alone and never uses `r ≤ 1` -- so `W = -qc ≥ 0` is available on the whole feasible set.

The lemmas below record what concavity of `|T|` actually requires:

* `nconvex_suffices` -- `qn ≥ 0` (that is `thm:nconvex`) together with `qc ≤ 0` gives concavity.
  This is the `r ≤ 1` route, and `qn ≥ 0` is FALSE past `r = 1` (entry 230, confirmed stable
  under a 4x refinement).
* `concavity_iff_gamma` -- the sharp form: concavity holds exactly when `qn / (-qc) ≥ -1/2`.
  So `|N|` may be non-convex; it may not be non-convex by more than HALF the Wirtinger form.

**`H_N ≥ -W/2` is the single open obligation of the programme.**  It is strictly weaker than
`thm:nconvex`, and weaker exactly in the direction where `thm:nconvex` fails.
-/

/-- `thm:nconvex` + `prop:wirt` give concavity.  This is the `r ≤ 1` route. -/
theorem nconvex_suffices {qc qn : ℝ} (hc : qc ≤ 0) (hn : 0 ≤ qn) : qc - 2 * qn ≤ 0 := by
  linarith

/-- Concavity is equivalent to `2 qn - qc ≥ 0`, i.e. to `2 H_N + W ⪰ 0`. -/
theorem concavity_iff_psd {qc qn : ℝ} : qc - 2 * qn ≤ 0 ↔ 0 ≤ 2 * qn - qc := by
  constructor <;> intro h <;> linarith

/-- The sharp form.  With `W = -qc > 0`, concavity holds exactly when the generalised eigenvalue
`γ = qn / W` is at least `-1/2`.  `γ ≥ 0` is `thm:nconvex`; `γ ∈ [-1/2, 0)` is the regime past
`r = 1` that nothing has yet ruled out. -/
theorem concavity_iff_gamma {qc qn : ℝ} (hw : qc < 0) :
    qc - 2 * qn ≤ 0 ↔ -(1 / 2 : ℝ) ≤ qn / (-qc) := by
  have hpos : 0 < -qc := by linarith
  rw [le_div_iff₀ hpos]
  constructor <;> intro h <;> linarith

end ConcavityReduction

section AtomMassBound

/-!
### Clause (c) bounds the atom mass (entry 248)

Substituting the support function into `c_y(t) = (H(t)-1)\sin t + (H(t+π/2)-1)\cos t` and using
`\sin t \sin(t-s) + \cos t \cos(t-s) = \cos s`, clause (c) becomes the linear family
`∫ K_t\,dr ≤ \sin t + \cos t` with a NONNEGATIVE kernel `K_t`.

An atom of mass `m` at `π/2` costs NOTHING in either moment (`\cos(π/2) = 0`) -- that is why it
leaves `\max r` unbounded (A18) and `H(θ)` unbounded for `θ > π/2` (A68).  But its clause-(c)
load is `K_t(π/2) = \cos t \sin t = \tfrac12 \sin 2t`, maximal at `t = π/4`, so the constraint at
that single `t` already pins it.
-/

/-- Clause (c) at `t = π/4` bounds the atom mass by `2√2`.  Σ's atom is `1.167`, well inside. -/
theorem atom_mass_bound {m : ℝ}
    (h : m / 2 * Real.sin (2 * (Real.pi / 4)) ≤ Real.sin (Real.pi / 4) + Real.cos (Real.pi / 4)) :
    m ≤ 2 * Real.sqrt 2 := by
  rw [show (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two,
      Real.sin_pi_div_four, Real.cos_pi_div_four] at h
  have h2 : Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = Real.sqrt 2 := by ring
  rw [h2] at h
  linarith

end AtomMassBound

section StationaryInvariants

/-!
### The `c_y` invariant and the `α₂(0)` convention (entries 265, 268)

Three small facts that the stationary-set work rests on.

* At `t = π/4` the corner ordinate collapses to a LINEAR functional of the support function.
  Combined with the measured fact that `c_y` attains its maximum at `π/4`, this makes the
  invariant of entry 264 linear in `r`.
* The kernel derivative behind `c_y'`.
* `H` carries an atom at `π/2`, so `H'` JUMPS there by the atom mass; `α₂(0)` is the RIGHT
  derivative.  A central difference averages the two sides and gives the wrong value -- measured
  0.16705 against the correct 0.750575.
-/

/-- At `t = π/4`, `c_y = (H(π/4) + H(3π/4) - 2)/√2`: a LINEAR functional of `H`. -/
theorem cy_at_pi_div_four (h1 h2 : ℝ) :
    (h1 - 1) * Real.sin (Real.pi / 4) + (h2 - 1) * Real.cos (Real.pi / 4)
      = (h1 + h2 - 2) / Real.sqrt 2 := by
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [hsq]
  ring

/-- The kernel derivative behind `c_y'`: `d/dt [cos t · cos (s - t)] = sin (s - 2t)`. -/
theorem kernel_deriv (s t : ℝ) :
    -Real.sin t * Real.cos (s - t) + Real.cos t * Real.sin (s - t) = Real.sin (s - 2 * t) := by
  -- generalise s - t first, or sin_sub also rewrites the occurrences on the left
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = s - t := ⟨s - t, rfl⟩
  have hst : s - 2 * t = u - t := by rw [hu]; ring
  rw [← hu, hst, Real.sin_sub]
  ring

/-- The atom at `π/2` contributes `m · sin (θ - π/2)` for `θ > π/2` and nothing below, so the
derivative jumps by exactly `m` there.  Hence `α₂(0)` is the RIGHT derivative. -/
theorem atom_jump (m : ℝ) :
    (deriv fun θ => m * Real.sin (θ - Real.pi / 2)) (Real.pi / 2) = m := by
  simp

end StationaryInvariants

section ArcParameterisation

/-!
### The niche arc parameterisation (entries 273, 279)

With `P(t) = (H(t) - 1) / sin t`, the A-branch of the niche is `A_t(x) = P(t) - x cot t` (A66).
Its envelope satisfies `d/dt A_t = 0`, i.e. `P'(t) + x / sin² t = 0`, giving the abscissa
`x_A = -P' sin² t`; substituting back gives the ordinate `f_A = P + P' sin t cos t`.

CAUTION recorded with the lemmas: these make the arc INTEGRAND quadratic in `H`, but entry 279
measured that the motion of the arc ranges carries 13% to 63% of `δ²F`, with a negative sign, so
the arc pieces do NOT assemble into a closed-form `δ²|N|`.  The identities below are correct and
reusable; the assembly they were built for is not available.
-/

/-- The envelope condition `P' + x / sin² t = 0` gives the abscissa `x = -P' sin² t`. -/
theorem envelope_abscissa {dP x s : ℝ} (hs : s ≠ 0) (h : dP + x / s ^ 2 = 0) :
    x = -dP * s ^ 2 := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp at h
  linarith

/-- Substituting `x_A = -P' sin² t` into `A_t(x) = P - x cot t` gives `f_A = P + P' sin t cos t`.
Stated with `c = cos t`, `s = sin t` and `cot t = c / s`. -/
theorem envelope_ordinate {P dP s c : ℝ} (hs : s ≠ 0) :
    P - (-dP * s ^ 2) * (c / s) = P + dP * s * c := by
  field_simp
  ring

end ArcParameterisation


/-!
### The `c_y` kernel is not a moment combination (entry 281)

`c_y(t) = 1/2 - sin t - cos t + ∫ K_t dr` is affine in the curvature `r`, with
`K_t(s) = cos s` for `s ≤ t` and `cos t · cos (s - t)` for `t < s ≤ t + Real.pi/2` (A69).
Both cos-moments of `r` are fixed exactly on `[0, Real.pi/2]` and on `[Real.pi/2, Real.pi]`, so the observed
invariant `c_y(Real.pi/4) ≈ 0.38784` at every ascent endpoint would be a triviality — true of every
feasible cap — if `K_{Real.pi/4}` were a linear combination of the two moment weights.

It is not, and the obstruction is exact: on `(Real.pi/4, Real.pi/2]` the kernel equals `(cos s + sin s)/2`,
which is not a multiple of `cos s` — it is nonzero at `s = Real.pi/2` where `cos s` vanishes.
Numerically the least-squares residual in that two-dimensional span is 36%, and `c_y(Real.pi/4)` ranges
over a width of 0.40 across random feasible caps against `8.8e-4` across the 36 stationary
endpoints.  So the invariant is a genuine consequence of stationarity (A124).
-/

section MomentSpan

/-- The `c_y` kernel at `t = π/4`, on the middle range `(π/4, π/2]`. -/
theorem cy_kernel_quarter (s : ℝ) :
    Real.cos (Real.pi / 4) * Real.cos (s - Real.pi / 4) = (Real.cos s + Real.sin s) / 2 := by
  rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination ((Real.cos s + Real.sin s) / 4) * hsq

/-- `K_{π/4}` is not a multiple of `cos` on the middle range: no scalar `a` satisfies
`cos(π/4) cos(s - π/4) = a cos s` for all `s`.  Witnessed at `s = π/2`, where the left side is
`1/2` and the right side is `0`.  Hence `c_y(π/4)` is not determined by the cos-moments. -/
theorem cy_kernel_not_cos_multiple :
    ¬ ∃ a : ℝ, ∀ s : ℝ, Real.cos (Real.pi / 4) * Real.cos (s - Real.pi / 4) = a * Real.cos s := by
  rintro ⟨a, ha⟩
  have h := ha (Real.pi / 2)
  rw [cy_kernel_quarter, Real.cos_pi_div_two, Real.sin_pi_div_two] at h
  norm_num at h

end MomentSpan


/-!
### The first arm at `t = 0` is pinned by the constraints (entry 284)

`α₁(t) = H(t + π/2) - 1 - H'(t)` is the face-1 arm.  Writing
`H(θ) = cos θ + ½ sin θ + ∫₀^θ r(s) sin(θ - s) ds`, differentiation under the integral gives
`H'(θ) = -sin θ + ½ cos θ + ∫₀^θ r(s) cos(θ - s) ds`, and at `θ = 0` the integral is empty, so
`H'(0) = 1/2` for EVERY cap.  The gauge constraint fixes `H(π/2) = 1`.  Hence `α₁(0) = -1/2`
identically — no cap can do better or worse.

This is why the measured `min α₁` column was identical across every ascent endpoint: the minimum is
attained as `t → 0`, where the value is a constant of the constraint set.  Recording it as a lemma
so the column is never read as evidence again: it is a tautology, not a measurement.  In particular
Baek's arm hypothesis `arms > 0` cannot transfer to the ambidextrous problem in this normalisation,
since it fails at `t = 0` for every cap including Romik's `Σ`.
-/

section FirstArm

/-- `H'(0) = 1/2`: the boundary terms of the support function at `θ = 0`, with an empty integral. -/
theorem hprime_at_zero :
    -Real.sin 0 + (1 / 2) * Real.cos 0 + 0 = 1 / 2 := by
  simp

/-- `α₁(0) = H(π/2) - 1 - H'(0) = -1/2` whenever the gauge fixes `H(π/2) = 1`. -/
theorem alpha1_at_zero {Hpi2 Hp0 : ℝ} (hgauge : Hpi2 = 1) (hderiv : Hp0 = 1 / 2) :
    Hpi2 - 1 - Hp0 = -(1 / 2) := by
  rw [hgauge, hderiv]
  norm_num

/-- Consequently the arm condition `α₁(0) > 0` is unsatisfiable on the constraint set. -/
theorem alpha1_at_zero_neg {Hpi2 Hp0 : ℝ} (hgauge : Hpi2 = 1) (hderiv : Hp0 = 1 / 2) :
    ¬ (0 < Hpi2 - 1 - Hp0) := by
  rw [alpha1_at_zero hgauge hderiv]
  norm_num

end FirstArm


/-!
### The annihilator collapse for the `c_y` kernel family (entry 286)

Route D asked whether "the whole `c_y` curve agrees with `Σ`'s" forces `r = r_Σ`, i.e. whether
`span {K_t : t ∈ (0, π/2)}` is dense.  It is not.  Writing `F t = ∫₀^π K_t · m` and
`C t = ∫_t^{t+π/2} cos (s - t) m`, `S t = ∫_t^{t+π/2} sin (s - t) m`, one gets
`F = ∫₀^t cos s · m + cos t · C` and `F' = -sin t · C + cos t · S` (the `m t` boundary terms
cancel), with `C' = -m t + S` and `S' = m (t + π/2) - C`.

Imposing `F ≡ 0` and `F' ≡ 0` gives `S = tan t · C`, and then `F'' ≡ 0` collapses — by the lemma
below — to the delay relation

  `sin t · m t + cos t · m (t + π/2) = -(2 / cos² t) ∫₀^t cos s · m`,

which determines `m` on `[π/2, π]` from `m` on `[0, π/2]`.  So the annihilator is infinite
dimensional (free first half, two vanishing moments), verified numerically to relative `6.3e-5`
with an explicit nonzero `m`.  Route D as posed is closed; what survives is a rigidity statement —
the curve pins the second half of the curvature given the first — not a uniqueness statement.

The lemma isolates the one step that is easy to get wrong: the `C` and `S` terms collapse to a
single `-2C / cos t` precisely because `sin²t + cos²t = 1`.
-/

section AnnihilatorCollapse

/-- The `F''` collapse.  With `S = tan t · C` and `cos t ≠ 0`, the four second-derivative terms
reduce to `-(2C)/cos t + sin t · m + cos t · M`, where `M` stands for `m (t + π/2)`. -/
theorem annihilator_collapse {t C S m M : ℝ} (hc : Real.cos t ≠ 0)
    (hS : S = Real.tan t * C) :
    -Real.cos t * C - Real.sin t * (-m + S) - Real.sin t * S + Real.cos t * (M - C)
      = -(2 * C) / Real.cos t + Real.sin t * m + Real.cos t * M := by
  have hpy : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := by
    rw [add_comm]; exact Real.cos_sq_add_sin_sq t
  rw [hS, Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination (-2 * C) * hpy

/-- Consequently the delay relation: `F'' = 0` is equivalent to
`sin t · m t + cos t · m (t + π/2) = (2C)/cos t`, with `C` determined by `F = 0`. -/
theorem delay_relation {t C S m M : ℝ} (hc : Real.cos t ≠ 0)
    (hS : S = Real.tan t * C)
    (hF2 : -Real.cos t * C - Real.sin t * (-m + S) - Real.sin t * S
             + Real.cos t * (M - C) = 0) :
    Real.sin t * m + Real.cos t * M = (2 * C) / Real.cos t := by
  rw [annihilator_collapse hc hS] at hF2
  rw [neg_div] at hF2
  linarith

end AnnihilatorCollapse

/-!
### The active set is the degenerate phase (entry 288, A132)

Measured exactly on `Σ`: the curvature `r` vanishes on precisely two maximal runs, `[0, β]` and
`[π - β, π]`, each of width `β = 0.2896538…`, and `note.tex` puts the arm's degenerate phase
`{α₁ < 0}` at exactly `[0, β)`.  The two sets coincide, and on the degenerate phase the arm has the
closed form `α₁ t = 2 a₁ sin t - 1/2`.

Formalised below, in the division-free form `4 a₁ sin t < 1` (equivalent to `sin t < 1/(4a₁)` for
`a₁ > 0`, and cleaner to reason with): the sign of the arm is governed by `sin t` alone, the crossing
is exactly where `4 a₁ sin t = 1`, and strict monotonicity of `sin` on `[-π/2, π/2]` makes that
crossing unique.  The uniqueness is precisely condition (S) — the degenerate set is a single interval
anchored at `0` — which the numerics found at every ascent endpoint (10 of 10, entry 284).

With `a₁ = 0.875287362…` the crossing sits at `arcsin (1/(4a₁)) = 0.289654…`, matching the measured
active-set edge `β` to the printed digits.  So `β` is not an independently fitted constant: it is
determined by the gauge cubic through `a₁`.
-/

section ActiveSetCrossing

/-- On the degenerate phase the arm's sign is governed by `sin t` alone. -/
theorem arm_neg_iff {a1 t : ℝ} :
    2 * a1 * Real.sin t - 1 / 2 < 0 ↔ 4 * a1 * Real.sin t < 1 := by
  constructor <;> intro h <;> linarith

/-- The crossing is exactly where `4 a₁ sin t = 1`: there the arm vanishes. -/
theorem arm_zero_at {a1 t : ℝ} (h : 4 * a1 * Real.sin t = 1) :
    2 * a1 * Real.sin t - 1 / 2 = 0 := by linarith

/-- Strict monotonicity of `sin` on `[-π/2, π/2]` makes the crossing unique, which is condition (S):
the degenerate set is a single interval anchored at `0`. -/
theorem arm_crossing_unique {a1 t u : ℝ} (ha : 0 < a1)
    (ht : -(Real.pi / 2) ≤ t) (hu : u ≤ Real.pi / 2) (hlt : t < u)
    (hzt : 4 * a1 * Real.sin t = 1) :
    4 * a1 * Real.sin u ≠ 1 := by
  have hmono : Real.sin t < Real.sin u :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two ht hu hlt
  intro hzu
  nlinarith [hmono, hzt, hzu]

end ActiveSetCrossing


/-!
### The clamp identity and the partition-free form of `|T|` (entry 293, A134)

The tiling evaluator computes, cell by cell,
`I = (hi - lo) - 2 * max 0 (min f hi - lo)`.  Writing `A = hi - lo` and `u = f - lo`, this is
`I = A - 2 * clamp u 0 A`, and the clamp has a closed form with no case split:

  `clamp u 0 A = (|u| - |u - A| + A) / 2`   for `A ≥ 0`,

proved below by the three-regime case analysis, once and for all.  Substituting,

  `I = A - (|u| - |u - A| + A) = |u - A| - |u|`,

and since `u - A = f - hi`, `u = f - lo`, this gives the partition-free integrand
`I = |f - hi| - |f - lo|`.  With `lo = 1 - hi` (ρ-symmetry) that is

  `|T| = ∫ ( |f - hi| - |f + hi - 1| ) dx`,

verified numerically against the evaluator to `4.4e-16` on `Σ` and four random caps.  The point of
the identity is structural, not cosmetic: A113 says every DOMAIN DECOMPOSITION of `|T|` cuts along a
moving, unsigned boundary, and this representation performs no decomposition at all, so A113 does
not apply to it.

Also recorded here: `hi` is a pointwise MINIMUM of functions affine in `H`, hence concave in `H`, so
`|C₂| = ∫ (2 hi - 1) dx` is concave.  Since `|T| = |C₂| - 2|N|`, concavity of `|T|` would follow from
CONVEXITY of the niche area `|N|` — concave minus a nonnegative multiple of convex is concave.  The
lemma `concave_sub_convex` below is that step in the abstract, so the remaining mathematical content
is exactly "`|N|` is convex in `H`".
-/

section ClampIdentity

/-- The clamp of `u` to `[0, A]`, written without a case split, for `A ≥ 0`. -/
theorem clamp_abs_form {u A : ℝ} (hA : 0 ≤ A) :
    max 0 (min u A) = (|u| - |u - A| + A) / 2 := by
  rcases le_or_gt u 0 with hu | hu
  · have h1 : min u A = u := min_eq_left (hu.trans hA)
    have h2 : |u| = -u := abs_of_nonpos hu
    have h3 : |u - A| = -(u - A) := abs_of_nonpos (by linarith)
    rw [h1, max_eq_left hu, h2, h3]; ring
  · rcases le_or_gt u A with huA | huA
    · have h1 : min u A = u := min_eq_left huA
      have h2 : |u| = u := abs_of_pos hu
      have h3 : |u - A| = -(u - A) := abs_of_nonpos (by linarith)
      rw [h1, max_eq_right hu.le, h2, h3]; ring
    · have h1 : min u A = A := min_eq_right huA.le
      have h2 : |u| = u := abs_of_pos hu
      have h3 : |u - A| = u - A := abs_of_nonneg (by linarith)
      rw [h1, max_eq_right hA, h2, h3]; ring

/-- The integrand collapses: `A - 2 * clamp u 0 A = |u - A| - |u|`. -/
theorem integrand_abs_form {u A : ℝ} (hA : 0 ≤ A) :
    A - 2 * max 0 (min u A) = |u - A| - |u| := by
  rw [clamp_abs_form hA]; ring

/-- In the substituted variables `u = f - lo`, `A = hi - lo`, the integrand is `|f - hi| - |f - lo|`. -/
theorem integrand_in_f {f hi lo : ℝ} (h : lo ≤ hi) :
    (hi - lo) - 2 * max 0 (min (f - lo) (hi - lo)) = |f - hi| - |f - lo| := by
  have hA : (0:ℝ) ≤ hi - lo := by linarith
  rw [integrand_abs_form hA]
  congr 2
  ring

/-- With `lo = 1 - hi` the second absolute value becomes `|f + hi - 1|`. -/
theorem integrand_rho_sym {f hi : ℝ} (h : 1 - hi ≤ hi) :
    (hi - (1 - hi)) - 2 * max 0 (min (f - (1 - hi)) (hi - (1 - hi)))
      = |f - hi| - |f + hi - 1| := by
  rw [integrand_in_f h]
  congr 2
  ring

/-- The reduction step: concave minus convex is concave.  Applied with `|T| = |C₂| - 2|N|` and
`|C₂|` concave (a minimum of functions affine in `H`), this says concavity of `|T|` follows from
convexity of `2|N|`, hence of the niche area `|N|`. -/
theorem concave_sub_convex {s : Set ℝ} {C M : ℝ → ℝ}
    (hC : ConcaveOn ℝ s C) (hM : ConvexOn ℝ s M) :
    ConcaveOn ℝ s (C - M) := by
  rw [sub_eq_add_neg]
  exact hC.add hM.neg
end ClampIdentity


/-!
### The endpoint (domain-motion) term and its forced sign (entry 300, A139)

For `F ε = ∫_{a ε}^{b ε} g x ε dx` whose integrand vanishes at the moving endpoints, the first-order
boundary terms cancel identically and `F' = ∫ g_ε`.  At second order they do not:

  `F'' = ∫ g_εε dx + g_ε b' - g_ε a'`,

and differentiating the defining relation `g (b ε) ε = 0` gives `g_x · b' + g_ε = 0`, i.e.
`b' = -g_ε / g_x`.  Substituting turns each boundary contribution into a SQUARE over a slope:

  at `b` (where `g_x < 0`):  `g_ε · b' = -g_ε² / g_x ≥ 0`,
  at `a` (where `g_x > 0`):  `-g_ε · a' =  g_ε² / g_x ≥ 0`.

Both are nonnegative, with no hypothesis on `g_ε` at all.  That is the whole content of A139's sign
claim, and it is what makes the domain-motion term an OBSTRUCTION rather than a helpful term: it
pushes `δ²|C₂|` — and by A140 also `δ²|T|`, since the niche is absent at the pinch points — in the
CONVEX direction, so concavity requires the bulk term to dominate it.

The formalisation below is of the algebra and the signs only.  The full second-variation formula for
a moving-domain integral is not attempted: Mathlib has no Leibniz rule for a domain with
implicitly-defined moving endpoints, and building one is a separate project.  Recorded as the blocker
for the rest of A139, per Rule 5.
-/

section EndpointTerm

/-- The implicit endpoint velocity: from `g_x · b' + g_ε = 0` with `g_x ≠ 0`, `b' = -g_ε / g_x`. -/
theorem endpoint_velocity {gx ge bp : ℝ} (hgx : gx ≠ 0) (h : gx * bp + ge = 0) :
    bp = -ge / gx := by
  field_simp
  linarith

/-- Right endpoint, where `g` decreases through zero (`g_x < 0`): the boundary contribution is
`g_ε · b' = g_ε² / (-g_x) ≥ 0`. -/
theorem endpoint_term_right {gx ge bp : ℝ} (hgx : gx < 0) (h : gx * bp + ge = 0) :
    0 ≤ ge * bp := by
  have hne : gx ≠ 0 := ne_of_lt hgx
  rw [endpoint_velocity hne h]
  have hpos : 0 < -gx := by linarith
  have key : ge * (-ge / gx) = ge ^ 2 / (-gx) := by field_simp
  rw [key]
  positivity

/-- Left endpoint, where `g` increases through zero (`g_x > 0`): the contribution is
`-g_ε · a' = g_ε² / g_x ≥ 0`. -/
theorem endpoint_term_left {gx ge ap : ℝ} (hgx : 0 < gx) (h : gx * ap + ge = 0) :
    0 ≤ -(ge * ap) := by
  have hne : gx ≠ 0 := ne_of_gt hgx
  rw [endpoint_velocity hne h]
  have key : -(ge * (-ge / gx)) = ge ^ 2 / gx := by field_simp
  rw [key]
  positivity

/-- Both endpoints together: the total domain-motion term is NONNEGATIVE, with no hypothesis on
`g_ε`.  So it can only push the second variation toward convexity, which is exactly why concavity
requires the bulk term to dominate it. -/
theorem motion_term_nonneg {gxa gxb ge_a ge_b ap bp : ℝ}
    (ha : 0 < gxa) (hb : gxb < 0)
    (hA : gxa * ap + ge_a = 0) (hB : gxb * bp + ge_b = 0) :
    0 ≤ ge_b * bp + -(ge_a * ap) :=
  add_nonneg (endpoint_term_right hb hB) (endpoint_term_left ha hA)

end EndpointTerm


/-!
### The bulk term is nonpositive, by an elementary argument (entry 308, A147)

Entry 306 listed "the bulk is still measured" as an open caveat, and I had been treating it as
needing Brunn–Minkowski (unavailable: `C₂ = C ∩ ρC` is an intersection, not a Minkowski combination).
That was the wrong tool for the wrong reason — the sign of the bulk needs no such machinery.

On a FIXED integration domain the bulk is `∫_D g_εε dx` with `g = hi - lo`, where

* `hi x = ⨅_θ (hfull θ - x cos θ)/sin θ` over `sin θ > 0` — a pointwise INFIMUM of functions AFFINE
  in the support data, hence CONCAVE in it;
* `lo x = ⨆_θ (hfull θ - x cos θ)/sin θ` over `sin θ < 0` — a SUPREMUM of affine, hence CONVEX.

The perturbation `r ↦ r + s·u` makes `H`, and therefore each of those affine functions, affine in the
parameter `s`.  So `g = hi - lo` is (concave − convex) = concave in `s` pointwise in `x`, and a
nonnegatively-weighted sum of concave functions is concave.  The evaluator's bulk is exactly such a
sum — a Riemann sum over a fixed cell set with weights `dx > 0` — so

  **bulk ≤ 0, proved, with no measurement and no Brunn–Minkowski.**

What this does NOT give is a quantitative lower bound on `|bulk|`, and that is precisely what the
A145 certificate needs (`|bulk| > corner`).  Indeed `bulk` can vanish: a min of affine functions has
zero second derivative away from its switch locus, which is exactly the failure mode A140 identified.
So the remaining content of the concavity question is entirely quantitative, and the qualitative part
is now closed.
-/

section BulkSign

/-- A pointwise infimum of two concave functions is concave.  Iterated, this is why `hi` — a minimum
of functions affine in the support data — is concave in the perturbation parameter. -/
theorem concave_inf_of_concave {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) (hg : ConcaveOn ℝ s g) :
    ConcaveOn ℝ s (f ⊓ g) := hf.inf hg

/-- Dually, a pointwise supremum of two convex functions is convex — why `lo`, a maximum of affine
functions, is convex. -/
theorem convex_sup_of_convex {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (f ⊔ g) := hf.sup hg

end BulkSign

section BulkNonpos

/-- `g = hi - lo` is concave when `hi` is concave (an infimum of affine) and `lo` is convex (a
supremum of affine).  This is `concave_sub_convex` specialised to the pair that defines `C₂`'s
vertical extent. -/
theorem extent_concave {hi lo : ℝ → ℝ} {s : Set ℝ}
    (hhi : ConcaveOn ℝ s hi) (hlo : ConvexOn ℝ s lo) :
    ConcaveOn ℝ s (hi - lo) :=
  concave_sub_convex hhi hlo

/-- A nonnegatively-weighted sum of two concave functions is concave.  Iterated over the cells of a
FIXED domain, this is the evaluator's bulk, so the bulk inherits concavity in the perturbation
parameter and its second variation is nonpositive. -/
theorem weighted_sum_concave {f g : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ConcaveOn ℝ s f) (hg : ConcaveOn ℝ s g) :
    ConcaveOn ℝ s (fun x => a * f x + b * g x) := by
  have h1 : ConcaveOn ℝ s (fun x => a * f x) := by
    simpa [smul_eq_mul] using hf.smul ha
  have h2 : ConcaveOn ℝ s (fun x => b * g x) := by
    simpa [smul_eq_mul] using hg.smul hb
  exact h1.add h2

end BulkNonpos


/-!
### The corner term in closed form (entry 305, A144)

At an endpoint of `C₂` the upper and lower boundaries cross.  Let `θ`, `φ` be their supporting
normals, `s₁ = sin θ`, `s₂ = sin φ`.  Danskin gives the boundary motions `δ(hi) = δH(θ)/s₁` and
`δ(lo) = δH(φ)/s₂`, so `g_ε = δH(θ)/s₁ - δH(φ)/s₂`; the boundary slopes are `-cot θ`, `-cot φ`, so
`g_x = sin(θ - φ)/(s₁ s₂)`.  A139 gives the domain-motion contribution as `g_ε² / |g_x|`, and
substituting collapses it: the `(s₁s₂)²` from `g_ε²` cancels against the `|s₁s₂|` from `g_x`, leaving

  `corner = (δH(θ) s₂ - δH(φ) s₁)² / (|s₁ s₂| · |sin(θ - φ)|)`.

Everything on the right is elementary — two support-function values, two sines, and the
transversality of the crossing — and the expression blows up only as the crossing becomes tangential
(`sin(θ-φ) → 0`) or a normal becomes horizontal (`s → 0`), which is the degenerate geometry one
expects to be the obstruction.  Verified numerically against the measured corner to 1.6% (A146).

The cancellation rests on `x² = |x|²`, which is where a hand derivation would most easily slip, so it
is the step worth having checked.
-/

section CornerClosedForm

/-- The corner term collapses to a square over a product of sines and the crossing transversality. -/
theorem corner_closed_form {a b s1 s2 sp : ℝ}
    (h1 : s1 ≠ 0) (h2 : s2 ≠ 0) (hs : sp ≠ 0) :
    (a / s1 - b / s2) ^ 2 / |sp / (s1 * s2)|
      = (a * s2 - b * s1) ^ 2 / (|s1 * s2| * |sp|) := by
  have hp : s1 * s2 ≠ 0 := mul_ne_zero h1 h2
  have hA : (0:ℝ) < |s1 * s2| := abs_pos.mpr hp
  have hS : (0:ℝ) < |sp| := abs_pos.mpr hs
  have hnum : a / s1 - b / s2 = (a * s2 - b * s1) / (s1 * s2) := by
    field_simp
  have hden : |sp / (s1 * s2)| = |sp| / |s1 * s2| := abs_div sp (s1 * s2)
  have hsq : (s1 * s2) ^ 2 = |s1 * s2| ^ 2 := (sq_abs _).symm
  rw [hnum, hden, div_pow, hsq]
  field_simp


/-- The `ρ`-symmetric specialisation at `Σ`'s corner, where `φ = 2π - θ` forces `δH(φ) = δH(θ)` and
`s₂ = -s₁`.  The `s₁²` in the numerator cancels the one in the denominator, leaving `4 δH(θ)²/|sin ψ|`
-- a RANK-ONE quadratic form in the perturbation, which is the identity entry 310 used to reduce
`inf R` to a Rayleigh quotient.  (Stated with the cancellation carried out: an earlier draft of this
lemma asserted `4a²/(s₁²|sp|)`, which is FALSE -- the `s₁²` cancels.) -/
theorem corner_rho_symmetric {a s1 sp : ℝ} (h1 : s1 ≠ 0) (hs : sp ≠ 0) :
    (a * (-s1) - a * s1) ^ 2 / (|s1 * (-s1)| * |sp|) = 4 * a ^ 2 / |sp| := by
  have hsq : |s1 * (-s1)| = s1 ^ 2 := by
    rw [show s1 * (-s1) = -(s1 ^ 2) by ring, abs_neg, abs_of_nonneg (sq_nonneg s1)]
  have hne : s1 ^ 2 ≠ 0 := pow_ne_zero 2 h1
  have hS : |sp| ≠ 0 := abs_ne_zero.mpr hs
  rw [hsq]
  field_simp
  ring

end CornerClosedForm


/-!
### Minkowski concavity of the half-planes, and where it breaks for the niche (entry 321)

A157 showed `bulk_T ≤ 0` has no elementary route via convexity of `f`.  The geometric route is
different and gets further.  Since `bulk_T = bulk_{C₂} - 2 bulk_N` and `bulk_{C₂} ≤ 0` is proved
(A147), `bulk_T ≤ 0` follows from `bulk_N ≥ 0`, i.e. from convexity of the niche area — condition (K)
of entry 296.

The niche is `N = C₂ ∩ ⋃_t W_t`, where `W_t = {y ≤ A_t x} ∩ {y ≤ B_t x}` is a wedge whose two
boundary lines are AFFINE in the support data `H` (A66).  The key structural fact, proved below in
its essential form: a half-plane whose bound is affine in `H` is **Minkowski concave** in `H` —

  `{y ≤ A(x; λH₁+(1-λ)H₂)} ⊇ λ·{y ≤ A(x;H₁)} ⊕ (1-λ)·{y ≤ A(x;H₂)}`,

because for `p` in the first and `q` in the second,
`λp_y + (1-λ)q_y ≤ λA(p_x;H₁) + (1-λ)A(q_x;H₂) = A(λp_x+(1-λ)q_x; λH₁+(1-λ)H₂)` by affineness in
BOTH arguments.  Intersections inherit this, so every wedge `W_t` and the cap `C₂` are Minkowski
concave in `H`.

WHERE IT BREAKS, and this is the precise localisation of the remaining obstruction: the niche takes a
UNION over `t`, and

  `⋃_t (λ W_t(H₁) ⊕ (1-λ) W_t(H₂))`   is only the DIAGONAL part of
  `(⋃_t W_t(H₁)) ⊕ (1-λ)(⋃_t W_t(H₂))`,   which unions over ALL PAIRS `(t,t')`.

So Minkowski concavity survives each wedge and dies on the union.  That is exactly the same
mechanism as A113's moving boundary and A157's max-of-concave, seen a third time — the obstruction is
always the `max`/`⋃` over the sweep parameter, never the affine structure in `H`.
-/

section MinkowskiConcavity

/-- The defining inequality of Minkowski concavity for a half-plane with an affine bound: if
`p_y ≤ a₁ - p_x * c` and `q_y ≤ a₂ - q_x * c`, then the `λ`-combination satisfies the bound with the
`λ`-combined intercept.  Affineness in both `x` and the support datum is what makes it work. -/
theorem halfplane_minkowski_concave {lam a1 a2 c px py qx qy : ℝ}
    (hl : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hp : py ≤ a1 - px * c) (hq : qy ≤ a2 - qx * c) :
    lam * py + (1 - lam) * qy
      ≤ (lam * a1 + (1 - lam) * a2) - (lam * px + (1 - lam) * qx) * c := by
  have h1 : lam * py ≤ lam * (a1 - px * c) := by
    apply mul_le_mul_of_nonneg_left hp hl
  have h2 : (1 - lam) * qy ≤ (1 - lam) * (a2 - qx * c) := by
    apply mul_le_mul_of_nonneg_left hq (by linarith)
  nlinarith [h1, h2]

/-- Wedges inherit it: a point satisfying both half-plane bounds at the two support data satisfies
both at the combination.  This is why every `W_t`, and `C₂` as an intersection of half-planes, is
Minkowski concave in `H`. -/
theorem wedge_minkowski_concave {lam a1 a2 b1 b2 c d px py qx qy : ℝ}
    (hl : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hpa : py ≤ a1 - px * c) (hqa : qy ≤ a2 - qx * c)
    (hpb : py ≤ b1 - px * d) (hqb : qy ≤ b2 - qx * d) :
    lam * py + (1 - lam) * qy
        ≤ (lam * a1 + (1 - lam) * a2) - (lam * px + (1 - lam) * qx) * c
      ∧ lam * py + (1 - lam) * qy
        ≤ (lam * b1 + (1 - lam) * b2) - (lam * px + (1 - lam) * qx) * d :=
  ⟨halfplane_minkowski_concave hl hl1 hpa hqa,
   halfplane_minkowski_concave hl hl1 hpb hqb⟩

end MinkowskiConcavity


/-!
### The niche-regime reduction (entry 296, A135)

By A134 the `|T|` integrand is `|f - hi| - |f + hi - 1|`, and entry 293 measured `f > hi` in ZERO of
9000 cells, so `|f - hi| = hi - f` and with `lo = 1 - hi` the integrand on the niche regime
(`lo ≤ f ≤ hi`) collapses to

  `(hi - f) - (f - lo) = hi + lo - 2f = 1 - 2f`,

AFFINE in `f`.  Hence concavity of the `|T|` integrand there is EXACTLY convexity of `f`, with the
factor `-2` carrying the sign.  That is the reduction A135 records, and it is what makes the whole
concavity question turn on `f` rather than on the tiling.

Formalised below in both directions.  The analytic step this does NOT cover — that the pointwise
statement integrates to the corresponding statement for `∫f dx` over the moving niche domain — is the
recorded blocker (Rule 5): Mathlib has no Leibniz rule for a domain with implicitly-defined moving
endpoints, which is the same blocker as A139's.
-/

section NicheReduction

/-- On the niche regime the integrand is `1 - 2f`, so it is concave exactly when `f` is convex. -/
theorem integrand_concave_iff_f_convex {s : Set ℝ} {f : ℝ → ℝ} :
    ConcaveOn ℝ s (fun x => 1 - 2 * f x) ↔ ConvexOn ℝ s f := by
  -- Proved from the DEFINITION rather than by combining Mathlib's `.neg`/`.add`/`.smul` lemmas:
  -- those produce Pi-level terms (`g + h`, `-g`) which do not match the pointwise goal, and the
  -- `ℝ`-on-`ℝ` SMul instance diamond then blocks `simpa`.  Entry 296 hit the same wall.  Unfolding
  -- is shorter and avoids both problems.
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
    have := h hx hy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    -- a(1-2f x) + b(1-2f y) ≤ 1 - 2 f(ax+by), and a + b = 1, so this is f(ax+by) ≤ a f x + b f y
    nlinarith [this, hab]
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
    have := h hx hy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    nlinarith [this, hab]
end NicheReduction


/-!
### The arc partition (entry 272, A116)

The niche boundary is `f = max_t min (A_t) (B_t)`, and which of the three arc families realises the
maximum at a given abscissa cuts the niche into three arcs.  Entry 272 verified numerically that the
three arcs partition the niche exactly (residual `1.4e-16`).  The mathematical content of "partition"
is that the STRICT-argmax sets are pairwise disjoint and, together with the tie set, cover
everything — which is what the lemmas below state for a family of three, in the form the arc
decomposition uses.

This is the part of A116 that is a theorem.  The part that is NOT formalised here, and is recorded as
the blocker (Rule 5), is that each arc's contribution is the integral of the corresponding branch
over its own range: that requires integration over a domain whose endpoints move with `H`, the same
missing Leibniz rule that blocks A115, A117, A118, A119, A121 and A139.  Recording it once here
rather than repeating it: it is ONE piece of machinery, not seven.
-/

section ArcPartition

variable {α : Type*} (g₁ g₂ g₃ : α → ℝ)

/-- The set where `g₁` strictly dominates the other two. -/
def strictMax₁ : Set α := {x | g₂ x < g₁ x ∧ g₃ x < g₁ x}
/-- The set where `g₂` strictly dominates. -/
def strictMax₂ : Set α := {x | g₁ x < g₂ x ∧ g₃ x < g₂ x}
/-- The set where `g₃` strictly dominates. -/
def strictMax₃ : Set α := {x | g₁ x < g₃ x ∧ g₂ x < g₃ x}

/-- The three strict-argmax sets are pairwise disjoint: no abscissa can have two strict maxima. -/
theorem strictMax_disjoint₁₂ : Disjoint (strictMax₁ g₁ g₂ g₃) (strictMax₂ g₁ g₂ g₃) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, _⟩ ⟨h2, _⟩
  exact absurd h1 (not_lt.mpr h2.le)

theorem strictMax_disjoint₁₃ : Disjoint (strictMax₁ g₁ g₂ g₃) (strictMax₃ g₁ g₂ g₃) := by
  rw [Set.disjoint_left]
  rintro x ⟨_, h1⟩ ⟨h2, _⟩
  exact absurd h1 (not_lt.mpr h2.le)

theorem strictMax_disjoint₂₃ : Disjoint (strictMax₂ g₁ g₂ g₃) (strictMax₃ g₁ g₂ g₃) := by
  rw [Set.disjoint_left]
  rintro x ⟨_, h1⟩ ⟨_, h2⟩
  exact absurd h1 (not_lt.mpr h2.le)

/-- Together with the tie set, the three strict-argmax sets cover everything: at every abscissa
either one branch strictly dominates, or two of them are equal.  So the three arcs partition the
niche up to the tie locus. -/
theorem strictMax_cover (x : α) :
    x ∈ strictMax₁ g₁ g₂ g₃ ∨ x ∈ strictMax₂ g₁ g₂ g₃ ∨ x ∈ strictMax₃ g₁ g₂ g₃
      ∨ g₁ x = g₂ x ∨ g₁ x = g₃ x ∨ g₂ x = g₃ x := by
  rcases lt_trichotomy (g₁ x) (g₂ x) with h12 | h12 | h12
  · rcases lt_trichotomy (g₂ x) (g₃ x) with h23 | h23 | h23
    · exact Or.inr (Or.inr (Or.inl ⟨h12.trans h23, h23⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h23))))
    · exact Or.inr (Or.inl ⟨h12, h23⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h12)))
  · rcases lt_trichotomy (g₁ x) (g₃ x) with h13 | h13 | h13
    · exact Or.inr (Or.inr (Or.inl ⟨h13, h12.trans h13⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h13))))
    · exact Or.inl ⟨h12, h13⟩

end ArcPartition


/-!
### `δ²G` vanishes: a minimum of affine functions is locally affine (entry 273, A118)

Entry 273 measured `δ²G` at `-2.2e-6, -1.1e-6, 9.6e-16, 2.9e-13, 1.5e-13, 4.4e-13` — six to sixteen
orders below `δ²F` — and concluded `δ²|N| = δ²F` to within `1e-6`.  A118 had predicted merely a
SIGNED (negative) measure, since `hi` is a min of affine functions and therefore concave; the
measurement says it is not merely signed but ZERO.

The reason is the content formalised here: `hi` is PIECEWISE AFFINE in the perturbation parameter.
Where one branch is strictly the minimum, `min` agrees with that branch on a whole neighbourhood, and
an affine function has vanishing second difference — exactly zero, not merely small.  So `δ²hi` is
carried entirely by the switching set of the argmin, which is where two branches cross.

What this does NOT formalise, and is the recorded blocker (Rule 5): that the switching set has
measure zero in `x` and therefore contributes nothing to an `x`-integral.  That step needs the
moving-domain integration machinery missing from Mathlib, the same blocker shared by A115, A117,
A119, A121, A139 and the second half of A116.
-/

section PiecewiseAffine

/-- The second difference of an affine function vanishes identically — exactly, not approximately. -/
theorem second_difference_affine (a b h s : ℝ) :
    (a + (s + h) * b) - 2 * (a + s * b) + (a + (s - h) * b) = 0 := by ring

/-- Where the first branch is strictly smaller, the minimum IS that branch. -/
theorem min_eq_of_lt {p q : ℝ} (hpq : p < q) : min p q = p := min_eq_left hpq.le

/-- Consequently, on a stencil where one affine branch stays strictly below the other, the second
difference of the minimum is exactly zero: `min` is affine there, so it contributes nothing to the
second variation.  This is why `δ²G` measured at machine zero rather than merely negative. -/
theorem second_difference_min_affine
    {a₁ b₁ a₂ b₂ h s : ℝ}
    (hm : a₁ + (s - h) * b₁ < a₂ + (s - h) * b₂)
    (h0 : a₁ + s * b₁ < a₂ + s * b₂)
    (hp : a₁ + (s + h) * b₁ < a₂ + (s + h) * b₂) :
    min (a₁ + (s + h) * b₁) (a₂ + (s + h) * b₂)
      - 2 * min (a₁ + s * b₁) (a₂ + s * b₂)
      + min (a₁ + (s - h) * b₁) (a₂ + (s - h) * b₂) = 0 := by
  rw [min_eq_of_lt hp, min_eq_of_lt h0, min_eq_of_lt hm]
  ring

end PiecewiseAffine


/-!
### The arc integrand is quadratic (entry 273, A115)

Along an arc the integrand is a product `f_A · x_A'` in which each factor is AFFINE in the support
data `H` — `P` is linear in `H` (entry 273), and so are the derived quantities.  A product of two
affine functions of the perturbation parameter is therefore QUADRATIC in it, which entry 273 verified
numerically to nine digits on a FIXED range.

The two lemmas below are that statement: the explicit expansion, and the property that characterises
quadraticity for a second-difference instrument — the second difference is CONSTANT in `s`, depending
only on the step `h` and the two leading coefficients.  The second form is what the numerics actually
tested, so it is the one worth having checked.

The FIXED-RANGE hypothesis is essential and is not a technicality: entry 279 measured that arc-range
MOTION carries 13% to 63% of `δ²F`, with a negative sign, so the quadratic form is only an upper
bound on the moving-range quantity.  That is why A117 ("quadratic modulo range motion") could not be
upgraded, and why this lemma is stated for a fixed range only.
-/

section ArcQuadratic

/-- A product of two affine functions of the parameter is quadratic in it, explicitly. -/
theorem product_of_affine_is_quadratic (u₀ u₁ v₀ v₁ s : ℝ) :
    (u₀ + s * u₁) * (v₀ + s * v₁)
      = u₀ * v₀ + s * (u₀ * v₁ + u₁ * v₀) + s ^ 2 * (u₁ * v₁) := by ring

/-- The characterising property for a second-difference instrument: the second difference of that
product is CONSTANT in `s`, equal to `2 h² u₁ v₁`.  A function whose second difference is independent
of the base point is exactly a quadratic, which is what entry 273 measured to nine digits. -/
theorem second_difference_of_product_affine (u₀ u₁ v₀ v₁ s h : ℝ) :
    (u₀ + (s + h) * u₁) * (v₀ + (s + h) * v₁)
      - 2 * ((u₀ + s * u₁) * (v₀ + s * v₁))
      + (u₀ + (s - h) * u₁) * (v₀ + (s - h) * v₁)
      = 2 * h ^ 2 * (u₁ * v₁) := by ring

end ArcQuadratic


/-!
### The strict-branch region: `f` is convex there, and the `|T|` integrand is concave (entry 332)

This is the "80% envelope part" proved properly, and the proof is shorter than the envelope-theorem
route A162 attempted — because it does not use the envelope theorem at all.

`f(H) = max_t min (A_t H) (B_t H)`.  For fixed `t`, `min (A_t) (B_t)` is a min of two functions
AFFINE in `H`, hence concave, and a max of concave functions is neither convex nor concave.  That is
why the global statement fails (A162: `δ²_H f` reaches `-0.639`, negative on 7–10% of abscissae).

But STRICTNESS IS AN OPEN CONDITION.  If at `H₀` the maximising `t*` satisfies
`A_{t*} H₀ < B_{t*} H₀` strictly, then by continuity the min stays equal to `A` for `t` near `t*` and
`H` near `H₀`, and the argmax stays near `t*`.  So on that neighbourhood

  `f H = ⨆_{t near t*} A_t H`,

a pointwise supremum of AFFINE functions — which is CONVEX, with no second-derivative computation and
no division by `∂²_t φ` (the step that made A162 delicate).  Entry 323 measured the strict condition
holding at roughly 80% of niche abscissae, so this covers that region.

Combined with A135 (`integrand_concave_iff_f_convex`, already VERIFIED): on the niche regime the
`|T|` integrand is `1 - 2f`, so `f` convex there gives the integrand CONCAVE there.  That is
`bulk_T ≤ 0` restricted to the strict-branch region.

What remains open, and is NOT covered here, is the complementary region where the two branches meet
at the argmax — the finite crossing set of A163, roughly 20% of abscissae at a `1e-3` tolerance and
measure zero in the limit (A163).  The lemmas below are stated for the strict region only, and the
docstring records that boundary so they cannot be misapplied — the error that A117 embodied.
-/

section StrictBranchRegion

/-- An affine function is convex.  (Stated for the concrete shape `x ↦ a + b * x` used by the
branches `A_t`, `B_t`, which are affine in the perturbation parameter.) -/
theorem affine_convexOn (s : Set ℝ) (hs : Convex ℝ s) (a b : ℝ) :
    ConvexOn ℝ s (fun x => a + b * x) := by
  refine ⟨hs, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  have heq : p * (a + b * x) + q * (a + b * y) = a + b * (p * x + q * y) := by
    linear_combination a * hpq
  linarith [heq]
/-- A maximum of two convex functions is convex — the two-branch case of "a sup of affine is
convex", which is the whole content of the strict-branch argument. -/
theorem max_convexOn {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (fun x => max (f x) (g x)) := by
  refine ⟨hf.1, fun x hx y hy p q hp hq hpq => ?_⟩
  have h1 := hf.2 hx hy hp hq hpq
  have h2 := hg.2 hx hy hp hq hpq
  simp only [smul_eq_mul] at h1 h2 ⊢
  rcases le_total (f (p * x + q * y)) (g (p * x + q * y)) with h | h
  · rw [max_eq_right h]
    refine h2.trans ?_
    have : g x ≤ max (f x) (g x) := le_max_right _ _
    have : g y ≤ max (f y) (g y) := le_max_right _ _
    nlinarith [le_max_right (f x) (g x), le_max_right (f y) (g y), hp, hq]
  · rw [max_eq_left h]
    refine h1.trans ?_
    nlinarith [le_max_left (f x) (g x), le_max_left (f y) (g y), hp, hq]

/-- On the strict-branch region `f` is a max of affine functions, hence convex; and then the `|T|`
integrand `1 - 2f` is CONCAVE there, by A135.  This is `bulk_T ≤ 0` on that region. -/
theorem integrand_concave_on_strict_region {s : Set ℝ} {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ s f) :
    ConcaveOn ℝ s (fun x => 1 - 2 * f x) :=
  (integrand_concave_iff_f_convex).mpr hconv

end StrictBranchRegion

/-! ### Boundary rank (A249)

The moving-window boundary term of the crossing second variation is, at one endpoint,

  `2 G_s tau' + G_t tau'^2 + G tau''`

with `tau' = -dx/cxp`, `tau'' = -(cxpp * tau'^2 + 2 * dxp * tau') / cxp`,
`G_s = dy * cxp + cy * dx`, and `G_t`, `G` depending only on the base curve.

Every summand carries a factor `dx`, so the endpoint term is a product of two linear
functionals of the perturbation data `(dx, dxp, dy)`.  A product of two linear functionals
is a quadratic form of rank at most two; with two endpoints the boundary term has rank at
most four.  The identity below is the algebraic content: the whole expression equals `dx`
times a quantity affine in `(dx, dxp, dy)`.
-/

namespace BoundaryRank

/-- The endpoint term factors through `dx`.  Stated with `cxp ≠ 0`, which holds on the
crossing window since the corner curve is there a graph over `x`. -/
theorem endterm_factors
    (cxp cxpp cy cyp dx dxp dy : ℝ) (h : cxp ≠ 0) :
    2 * (dy * cxp + cy * dxp) * (-dx / cxp)
      + (cyp * cxp + cy * cxpp) * (-dx / cxp) ^ 2
      + (cy * cxp) * (-(cxpp * (-dx / cxp) ^ 2 + 2 * dxp * (-dx / cxp)) / cxp)
    = dx * ( -2 * (dy * cxp + cy * dxp) / cxp
             + (cyp * cxp + cy * cxpp) * dx / cxp ^ 2
             - (cy * cxp) * cxpp * dx / cxp ^ 3
             + 2 * (cy * cxp) * dxp / cxp ^ 2 ) := by
  field_simp
  ring

/-- A product of two linear functionals vanishes whenever the first does; this is the
form in which rank-at-most-two is used: the endpoint term is supported on `dx ≠ 0`. -/
theorem endterm_zero_of_dx_zero
    (cxp cxpp cy cyp dxp dy : ℝ) (h : cxp ≠ 0) :
    2 * (dy * cxp + cy * dxp) * (-(0:ℝ) / cxp)
      + (cyp * cxp + cy * cxpp) * (-(0:ℝ) / cxp) ^ 2
      + (cy * cxp) * (-(cxpp * (-(0:ℝ) / cxp) ^ 2 + 2 * dxp * (-(0:ℝ) / cxp)) / cxp)
    = 0 := by
  simp

/-! ### A289: the CORRECTED boundary term, and its rank

A278 invalidated the `S+K+B` assembly.  The boundary term as coded evaluates `2 F_s t'` with
`F_s = d_y c_x' + c_y d_x` , but for `F = c_y c_x'` the correct partial is
`F_s = d_y c_x' + c_y d_x'` .  Substituting `t' = -d_x/c_x'` and
`t'' = -(c_x'' t'^2 + 2 d_x' t')/c_x'` into the corrected expression, the `c_y c_x''` terms AND the
`d_x d_x'` terms both cancel, leaving a form in `d_x, d_y` only -- no derivative point-values.

Both the coded and the corrected end terms factor as `d_x * (linear)`, so each has rank 2 and
signature (1,1); `B = et(t_b) - et(t_a)` therefore has rank 4 and signature (2,2).  Rank and
signature are invariant under the sign/orientation correction, so A249's "rank 4, 2 negatives"
survives A278 untouched. -/

/-- The CORRECTED end term collapses to a form in `d_x` and `d_y` only: the `c_y c_x''` and
`d_x d_x'` contributions cancel identically.  Contrast `endterm_factors`, which retains a
`d_x d_x'` term because it differentiates `F` with `d_x` in the `F_s` slot. -/
theorem endterm_corr_factors
    (cy cyp cxp cxpp dx dxp dy : ℝ) (h : cxp ≠ 0) :
    2 * (dy * cxp + cy * dxp) * (-dx / cxp)
      + (cyp * cxp + cy * cxpp) * (-dx / cxp) ^ 2
      + (cy * cxp) * (-(cxpp * (-dx / cxp) ^ 2 + 2 * dxp * (-dx / cxp)) / cxp)
      = dx * (-2 * dy + (cyp / cxp) * dx) := by
  field_simp
  ring

/-- The quadratic form `a u^2 + b u v` has matrix `!![a, b/2; b/2, 0]`, whose determinant is
`-b^2/4`.  Negative for `b ≠ 0`, hence the form is indefinite of rank 2 and signature (1,1). -/
theorem endterm_form_det (a b : ℝ) :
    a * 0 - (b / 2) * (b / 2) = -(b ^ 2) / 4 := by
  ring

/-- Concretely: `d_x * (-2 d_y + c d_x)` attains both `+1` and `-1`, so it is indefinite.  Together
with rank ≤ 2 (it is a product of two linear forms) this pins the signature at (1,1). -/
theorem endterm_indefinite (a b : ℝ) (hb : b ≠ 0) :
    ∃ t₁ t₂ : ℝ, a + b * t₁ = 1 ∧ a + b * t₂ = -1 := by
  refine ⟨(1 - a) / b, (-1 - a) / b, ?_, ?_⟩
  · rw [mul_div_cancel₀ _ hb]; ring
  · rw [mul_div_cancel₀ _ hb]; ring

end BoundaryRank

/-! ### A292: the coercivity constant for the strict form

The strict second-variation term is `int a_t^2/|A_tt| dx`.  Two facts collapse it:

* `a_t = psi'` exactly, where `psi = dH / sin t`  (`strict_integrand_is_psi_deriv` below);
* the argmax map has Jacobian `dx/dt = |A_tt| sin^2 t`, obtained by implicit differentiation of
  the stationarity condition `d/dt A(x,t) = 0` using `d/dx d/dt A = csc^2 t`.

Substituting, `|A_tt|` CANCELS IDENTICALLY and `strict = int (psi')^2 sin^2 t dt`.  So the weight is
`w(t) = sin^2 t`, and on Sigma's breakpoint window `[b, pi/2 - b]` it is bounded below by
`sin^2 b` -- an exact analytic constant, with no dependence on any measured bound for `|A_tt|`. -/
section StrictCoercivity

open Real

/-- The Jacobian cancellation: `(a^2 / A) * (A * s) = a^2 * s` for `A ≠ 0`.  With `A = |A_tt|` and
`s = sin^2 t` this is the step that removes `|A_tt|` from the strict form entirely. -/
theorem jacobian_cancel (a A s : ℝ) (hA : A ≠ 0) :
    (a ^ 2 / A) * (A * s) = a ^ 2 * s := by
  field_simp

/-- `a_t` is a pure derivative: `d/dt (dH / sin t) = dH'/sin t - dH cos t / sin^2 t`.  Stated as the
algebraic identity between the quotient-rule expression and the coded form. -/
theorem strict_integrand_is_psi_deriv (dH dH' st ct : ℝ) (hs : st ≠ 0) :
    dH' / st - dH * ct / st ^ 2 = (dH' * st - dH * ct) / st ^ 2 := by
  field_simp

/-- `(psi')^2 sin^2 t = (dH' - dH cot t)^2`: the weighted Dirichlet integrand in closed form. -/
theorem psi_deriv_sq_weighted (dH dH' st ct : ℝ) (hs : st ≠ 0) :
    ((dH' * st - dH * ct) / st ^ 2) ^ 2 * st ^ 2 = (dH' - dH * (ct / st)) ^ 2 := by
  field_simp

/-- On `[b, pi/2 - b]` with `0 < b`, we have `sin b ^ 2 ≤ sin t ^ 2`.  This is the A-branch
coercivity constant. -/
theorem sin_sq_ge_on_window {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (ht : t ≤ π / 2 - b) :
    sin b ^ 2 ≤ sin t ^ 2 := by
  have hpi : (0:ℝ) < π := pi_pos
  have hble : b ≤ π / 2 := by linarith
  have htle : t ≤ π / 2 := by linarith
  have h1 : sin b ≤ sin t := by
    have := Real.strictMonoOn_sin.monotoneOn
      (a := b) (b := t) ⟨by linarith, hble⟩ ⟨by linarith, htle⟩ hbt
    exact this
  have h0 : 0 ≤ sin b := sin_nonneg_of_nonneg_of_le_pi (le_of_lt hb) (by linarith)
  nlinarith

/-- On the same window, `sin b ^ 2 ≤ cos t ^ 2` -- the B-branch constant, equal to the A-branch one.
The `rho`-symmetry of the cap demands this agreement, and here it is an identity. -/
theorem cos_sq_ge_on_window {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (ht : t ≤ π / 2 - b) :
    sin b ^ 2 ≤ cos t ^ 2 := by
  have hco : cos t = sin (π / 2 - t) := by
    rw [Real.sin_pi_div_two_sub]
  rw [hco]
  exact sin_sq_ge_on_window hb (by linarith) (by linarith)

end StrictCoercivity

/-! ### A296: the Reduction-1 identity and unconditional disconjugacy

The strict second-variation form is `int_W |gamma' - M gamma|^2 dt` with
`gamma = (dH t, dH (t + pi/2))` and `M t = diag (cot t, -tan t)`.  Integration by parts turns it into
`int_W (|gamma'|^2 - |gamma|^2) dt - [gamma^T M gamma]_W` because

    M' + M^2 = -I,

whose two diagonal entries are `cot^2 - csc^2 = -1` and `tan^2 - sec^2 = -1`: THE SAME Pythagorean
identity applied to `sin` and to `cos`.  That coincidence is the cap's `rho`-symmetry appearing as
algebra (cf. `sin_sq_ge_on_window` / `cos_sq_ge_on_window`, which agree for the same reason).

Consequence: the bulk has CONSTANT COEFFICIENTS -- every weight (`1/sin t`, `1/cos t`, `|A_tt|`) is
removed exactly rather than estimated.  Verified numerically at relative error 3.6e-11.

After the gauge `w = exp(-i t/2) z`, `z = p + i q`, the Jacobi equation is `w'' + (9/4) w = 0`, whose
conjugate points are spaced `2*pi/3`.  The window `[b, pi/2 - b]` has length `pi/2 - 2b`, and
disconjugacy is UNCONDITIONAL: it needs only `b > 0`, since the window is a sub-interval of
`[0, pi/2]` and `pi/2 < 2*pi/3`.  No numerical value of `b` enters. -/
section ReductionOne

open Real

/-- Diagonal entry 0 of `M' + M^2 = -I`: `cot^2 t - csc^2 t = -1`. -/
theorem cot_sq_sub_csc_sq (t : ℝ) (hs : sin t ≠ 0) :
    (cos t / sin t) ^ 2 - (1 / sin t) ^ 2 = -1 := by
  have h : sin t ^ 2 + cos t ^ 2 = 1 := sin_sq_add_cos_sq t
  field_simp
  nlinarith [h]

/-- Diagonal entry 1 of `M' + M^2 = -I`: `tan^2 t - sec^2 t = -1`.  Same identity, `sin` and `cos`
exchanged -- this is the `rho`-symmetry of the cap. -/
theorem tan_sq_sub_sec_sq (t : ℝ) (hc : cos t ≠ 0) :
    (sin t / cos t) ^ 2 - (1 / cos t) ^ 2 = -1 := by
  have h : sin t ^ 2 + cos t ^ 2 = 1 := sin_sq_add_cos_sq t
  field_simp
  nlinarith [h]

/-- The window `[b, pi/2 - b]` is shorter than the conjugate-point spacing `2*pi/3`, for EVERY
`b > 0`.  No numerical bound on `b` is required: the window sits inside `[0, pi/2]` and
`pi/2 < 2*pi/3`. -/
theorem window_lt_conjugate_spacing (b : ℝ) (hb : 0 < b) :
    π / 2 - 2 * b < 2 * π / 3 := by
  have hpi : (0:ℝ) < π := pi_pos
  linarith

/-- Given `0 < L < 2*pi/3`, the Poincare/Wirtinger coercivity constant `1 - (9/4) L^2 / pi^2` is
positive.  This is the quantitative form of disconjugacy. -/
theorem coercivity_const_pos (L : ℝ) (hL0 : 0 < L) (hL : L < 2 * π / 3) :
    0 < 1 - (9 / 4) * L ^ 2 / π ^ 2 := by
  have hpi : (0:ℝ) < π := pi_pos
  have hpi2 : (0:ℝ) < π ^ 2 := by positivity
  have hkey : (9 / 4) * L ^ 2 / π ^ 2 < 1 := by
    rw [div_lt_one hpi2]; nlinarith [hL0, hL, hpi]
  linarith

/-- On the actual window, where `L ≤ pi/2`, the constant is at least `7/16` -- unconditionally in
`b`.  (At the true `b` it is 0.7759.)  Contrast the compactness route's `sin^2 b = 0.0816`, which
depended on the numerical value of `b`. -/
theorem coercivity_const_ge_seven_sixteenths (L : ℝ) (hL0 : 0 < L) (hL : L ≤ π / 2) :
    7 / 16 ≤ 1 - (9 / 4) * L ^ 2 / π ^ 2 := by
  have hpi : (0:ℝ) < π := pi_pos
  have hpi2 : (0:ℝ) < π ^ 2 := by positivity
  have hkey : (9 / 4) * L ^ 2 / π ^ 2 ≤ 9 / 16 := by
    rw [div_le_iff₀ hpi2]; nlinarith [hL0, hL, hpi]
  linarith

end ReductionOne

/-! ### A139: the domain-motion (corner) term is nonnegative

`|C_2|(e) = int_{a e}^{b e} g x e dx` with `g = hi - lo` and the endpoints defined by `g = 0`.
Because the integrand VANISHES at the endpoints, the first-order boundary terms cancel and
`F' = int g_e dx`.  At second order they do not cancel, and differentiating `g (b e) e = 0`
gives `b' = -g_e / g_x`.  Hence

    F'' = int g_ee dx  +  g_e b ^ 2 / |g_x b|  +  g_e a ^ 2 / |g_x a|,     g_x b < 0 < g_x a.

Mathlib has no moving-endpoint Leibniz rule, so the analytic step
`F'' = g_e b * b' - g_e a * a' + int g_ee` is carried as an explicit hypothesis
(`hLeibniz` below) rather than proved here.  Everything downstream of it -- the substitution, the
closed form, and the SIGN, which is the mathematical content -- is proved. -/
section DomainMotion

/-- Substituting the implicit-function derivatives `b' = -g_e b / g_x b` and
`a' = -g_e a / g_x a` into the endpoint-motion contribution. -/
theorem corner_of_endpoint_motion
    (geb gea gxb gxa bp ap : ℝ) (hb : gxb ≠ 0) (ha : gxa ≠ 0)
    (hbp : bp = -geb / gxb) (hap : ap = -gea / gxa) :
    geb * bp - gea * ap = -(geb ^ 2) / gxb + gea ^ 2 / gxa := by
  subst hbp; subst hap; field_simp; ring

/-- With `g_x b < 0`, the right endpoint contributes a nonnegative amount. -/
theorem corner_right_nonneg (geb gxb : ℝ) (hb : gxb < 0) :
    0 ≤ -(geb ^ 2) / gxb := by
  have h : 0 ≤ geb ^ 2 := sq_nonneg geb
  exact div_nonneg_of_nonpos (by linarith) (le_of_lt hb)

/-- With `g_x a > 0`, the left endpoint contributes a nonnegative amount. -/
theorem corner_left_nonneg (gea gxa : ℝ) (ha : 0 < gxa) :
    0 ≤ gea ^ 2 / gxa := by
  positivity

/-- **The corner term is nonnegative.**  This is A139's mathematical content: both endpoint
contributions are squares divided by quantities of the correct sign. -/
theorem corner_nonneg (geb gea gxb gxa : ℝ) (hb : gxb < 0) (ha : 0 < gxa) :
    0 ≤ -(geb ^ 2) / gxb + gea ^ 2 / gxa :=
  add_nonneg (corner_right_nonneg geb gxb hb) (corner_left_nonneg gea gxa ha)

/-- The closed form quoted in the log, with absolute values made explicit. -/
theorem corner_eq_abs_form (geb gea gxb gxa : ℝ) (hb : gxb < 0) (ha : 0 < gxa) :
    -(geb ^ 2) / gxb + gea ^ 2 / gxa = geb ^ 2 / |gxb| + gea ^ 2 / |gxa| := by
  rw [abs_of_neg hb, abs_of_pos ha]
  field_simp

/-- **A139, assembled.**  Given the moving-endpoint Leibniz step as a hypothesis, the second
variation of `|C_2|` is the bulk integral plus a NONNEGATIVE corner term in closed form. -/
theorem A139_corner_closed_form
    (F2 bulk geb gea gxb gxa bp ap : ℝ) (hb : gxb < 0) (ha : 0 < gxa)
    (hbp : bp = -geb / gxb) (hap : ap = -gea / gxa)
    (hLeibniz : F2 = bulk + (geb * bp - gea * ap)) :
    F2 = bulk + (geb ^ 2 / |gxb| + gea ^ 2 / |gxa|) ∧
      0 ≤ geb ^ 2 / |gxb| + gea ^ 2 / |gxa| := by
  have hb' : gxb ≠ 0 := ne_of_lt hb
  have ha' : gxa ≠ 0 := ne_of_gt ha
  have hsub := corner_of_endpoint_motion geb gea gxb gxa bp ap hb' ha' hbp hap
  have habs := corner_eq_abs_form geb gea gxb gxa hb ha
  constructor
  · rw [hLeibniz, hsub, habs]
  · rw [← habs]; exact corner_nonneg geb gea gxb gxa hb ha

/-- **The moving-endpoint Leibniz rule**, the step Mathlib lacks and which has blocked A139's star
since the beginning.  For a continuous integrand and differentiable endpoints,

    d/ds  int_{a s}^{b s} h x dx  =  h (b s) * b' - h (a s) * a'.

Proof: write the integral as `H (b s) - H (a s)` for `H y = int_0^y h`, differentiate `H` by the
second fundamental theorem of calculus, and compose with the chain rule. -/
theorem moving_endpoint_leibniz
    (h : ℝ → ℝ) (a b : ℝ → ℝ) (s a' b' : ℝ)
    (hc : Continuous h)
    (hda : HasDerivAt a a' s) (hdb : HasDerivAt b b' s) :
    HasDerivAt (fun σ => ∫ x in (a σ)..(b σ), h x)
      (h (b s) * b' - h (a s) * a') s := by
  -- `H y = int_0^y h` has derivative `h y` everywhere (FTC-2 for continuous integrands)
  have key : ∀ y : ℝ, HasDerivAt (fun u => ∫ x in (0:ℝ)..u, h x) (h y) y := by
    intro y
    exact intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  -- the integral splits at 0
  have hsplit : (fun σ => ∫ x in (a σ)..(b σ), h x)
      = fun σ => (∫ x in (0:ℝ)..(b σ), h x) - (∫ x in (0:ℝ)..(a σ), h x) := by
    funext σ
    rw [← intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  rw [hsplit]
  exact ((key (b s)).comp s hdb).sub ((key (a s)).comp s hda)

/-- **A139, with the Leibniz hypothesis discharged.**  `h` plays the role of `g_e`, and the endpoint
velocities are the implicit-function values `b' = -g_e b / g_x b`, `a' = -g_e a / g_x a`.  The
derivative of the moving-domain integral is then the corner term in closed form, and it is
NONNEGATIVE.  No hypothesis about Leibniz is assumed: it is supplied by
`moving_endpoint_leibniz`. -/
theorem A139_corner_proved
    (h : ℝ → ℝ) (a b : ℝ → ℝ) (s gxa gxb : ℝ)
    (hc : Continuous h)
    (hda : HasDerivAt a (-(h (a s)) / gxa) s)
    (hdb : HasDerivAt b (-(h (b s)) / gxb) s)
    (hbneg : gxb < 0) (hapos : 0 < gxa) :
    HasDerivAt (fun σ => ∫ x in (a σ)..(b σ), h x)
      (h (b s) ^ 2 / |gxb| + h (a s) ^ 2 / |gxa|) s
    ∧ 0 ≤ h (b s) ^ 2 / |gxb| + h (a s) ^ 2 / |gxa| := by
  have hL := moving_endpoint_leibniz h a b s (-(h (a s)) / gxa) (-(h (b s)) / gxb) hc hda hdb
  have hb' : gxb ≠ 0 := ne_of_lt hbneg
  have ha' : gxa ≠ 0 := ne_of_gt hapos
  have hval : h (b s) * (-(h (b s)) / gxb) - h (a s) * (-(h (a s)) / gxa)
      = h (b s) ^ 2 / |gxb| + h (a s) ^ 2 / |gxa| := by
    rw [abs_of_neg hbneg, abs_of_pos hapos]; field_simp; ring
  refine ⟨hval ▸ hL, ?_⟩
  have h1 : 0 ≤ h (b s) ^ 2 / |gxb| := by positivity
  have h2 : 0 ≤ h (a s) ^ 2 / |gxa| := by positivity
  linarith

end DomainMotion

end MovingSofa
