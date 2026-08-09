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
  have h : Real.sqrt 3 < 2 := by
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
    {t : ℝ} (hc : Real.cos t ≠ 0) :
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
  · have hsl : Real.sin σ ≤ σ := le_of_lt (Real.sin_lt hpos)
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
  have hpi : Real.pi < 3141593 / 1000000 := by
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
  have hcs : Real.cos σ ^ 2 - 1 = -(Real.sin σ ^ 2) := by
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

end MovingSofa
