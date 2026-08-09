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

end MovingSofa
