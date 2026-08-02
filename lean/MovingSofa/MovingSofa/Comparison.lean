/-
# The ODE comparison principle for the Prüfer barrier

`Barrier.lean` verified the monotone bound the certificate rests on and left the
comparison principle — barrier dominates phase — as a hypothesis, on the grounds that
Mathlib has no Sturm–Liouville or Prüfer development.  That was the right description of
Mathlib's ODE library but the wrong conclusion: the comparison is not an ODE-theoretic
fact at all, it is the *fencing* lemma of the mean value theory, and Mathlib has it as

    image_le_of_deriv_right_lt_deriv_boundary'
      (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ x ∈ Icc a b, f x ≤ B x

whose hypothesis is checked ONLY where the two functions touch.  That is precisely the
ODE comparison structure: at a touching point `θ x = B x`, so `G(x, θ x) = G(x, B x)`, and
a strict barrier gives `θ' x < B' x` with no Lipschitz constant, no Grönwall, and no
first-crossing argument.

`ambi_barrier.py` produces a strict barrier: every slope is rounded UP to denominator
`10^7` after the fixed point is reached, so `B' > G(t, B)` on each segment with a margin
of at least `10^-7`.  Strictness is therefore free.

  * `prufer_comparison` — the comparison itself, for any `G` and any strict barrier.
  * `prufer_comparison_of_monotone` — the version the certificate uses, where `G` is
    given by the right-hand side of `Barrier.lean` and the strictness comes from the
    verified monotone bound `prufer_rhs_le`.
  * `barrier_certifies` — the end-to-end statement: a strict barrier ending below `π/2`
    forces the phase below `π/2`, which is the Dirichlet–Neumann eigenvalue criterion.

With this file the barrier certificate has no unproved analytic hypothesis; what remains
outside Lean is the Prüfer transformation itself, the change of variables from the
Sturm–Liouville problem to the phase equation, which is a definitional matter rather than
an estimate.
-/
import Mathlib
import MovingSofa.Barrier

namespace MovingSofa

open Real Set

/-- **The comparison principle.**  If `θ` solves `θ' = G(t, θ)`, `B` starts above `θ`,
and `B' > G(t, B)` wherever the two touch, then `B` dominates `θ`.

The hypothesis is required only at touching points, which is what makes the proof
hypothesis-free in `G`: no Lipschitz condition and no Grönwall bound appear. -/
theorem prufer_comparison
    (G : ℝ → ℝ → ℝ) (θ B θ' B' : ℝ → ℝ) {a b : ℝ}
    (hθc : ContinuousOn θ (Icc a b))
    (hθd : ∀ x ∈ Ico a b, HasDerivWithinAt θ (θ' x) (Ici x) x)
    (hBc : ContinuousOn B (Icc a b))
    (hBd : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (hstart : θ a ≤ B a)
    (hode : ∀ x ∈ Ico a b, θ' x = G x (θ x))
    (hbar : ∀ x ∈ Ico a b, G x (B x) < B' x) :
    ∀ ⦃x⦄, x ∈ Icc a b → θ x ≤ B x := by
  apply image_le_of_deriv_right_lt_deriv_boundary' hθc hθd hstart hBc hBd
  intro x hx htouch
  rw [hode x hx, htouch]
  exact hbar x hx

/-- **The version the certificate uses.**  `G` is the Prüfer right-hand side, and the
strict barrier inequality is supplied in the form the rational recursion produces: the
slope exceeds `1/w + ((m+c) − 1/w)·S` where `S` is the recorded upper bound for
`sin²(B x)`.  The monotone bound of `Barrier.lean` converts that into strictness. -/
theorem prufer_comparison_of_monotone
    (w m : ℝ → ℝ) (c : ℝ) (θ B θ' B' S : ℝ → ℝ) {a b : ℝ}
    (hθc : ContinuousOn θ (Icc a b))
    (hθd : ∀ x ∈ Ico a b, HasDerivWithinAt θ (θ' x) (Ici x) x)
    (hBc : ContinuousOn B (Icc a b))
    (hBd : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (hstart : θ a ≤ B a)
    (hode : ∀ x ∈ Ico a b,
      θ' x = cos (θ x) ^ 2 / w x + (m x + c) * sin (θ x) ^ 2)
    (hw : ∀ x ∈ Ico a b, 0 < w x)
    (hcoef : ∀ x ∈ Ico a b, 0 ≤ (m x + c) - 1 / w x)
    (hS : ∀ x ∈ Ico a b, sin (B x) ^ 2 ≤ S x)
    (hslope : ∀ x ∈ Ico a b, 1 / w x + ((m x + c) - 1 / w x) * S x < B' x) :
    ∀ ⦃x⦄, x ∈ Icc a b → θ x ≤ B x := by
  refine prufer_comparison (fun t y => cos y ^ 2 / w t + (m t + c) * sin y ^ 2)
    θ B θ' B' hθc hθd hBc hBd hstart hode ?_
  intro x hx
  exact lt_of_le_of_lt (prufer_rhs_le (w x) (m x) c (B x) (S x) (hw x hx)
    (hcoef x hx) (hS x hx)) (hslope x hx)

/-- **End to end.**  A strict barrier that ends below `π/2` certifies the phase below
`π/2` at the right endpoint, which is the Dirichlet–Neumann eigenvalue criterion `c₁ > c`
for the decoupled half. -/
theorem barrier_certifies
    (w m : ℝ → ℝ) (c : ℝ) (θ B θ' B' S : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hθc : ContinuousOn θ (Icc a b))
    (hθd : ∀ x ∈ Ico a b, HasDerivWithinAt θ (θ' x) (Ici x) x)
    (hBc : ContinuousOn B (Icc a b))
    (hBd : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (hstart : θ a ≤ B a)
    (hode : ∀ x ∈ Ico a b,
      θ' x = cos (θ x) ^ 2 / w x + (m x + c) * sin (θ x) ^ 2)
    (hw : ∀ x ∈ Ico a b, 0 < w x)
    (hcoef : ∀ x ∈ Ico a b, 0 ≤ (m x + c) - 1 / w x)
    (hS : ∀ x ∈ Ico a b, sin (B x) ^ 2 ≤ S x)
    (hslope : ∀ x ∈ Ico a b, 1 / w x + ((m x + c) - 1 / w x) * S x < B' x)
    (hend : B b < π/2) :
    θ b < π/2 :=
  lt_of_le_of_lt
    (prufer_comparison_of_monotone w m c θ B θ' B' S hθc hθd hBc hBd hstart hode
      hw hcoef hS hslope (right_mem_Icc.mpr hab))
    hend

end MovingSofa
