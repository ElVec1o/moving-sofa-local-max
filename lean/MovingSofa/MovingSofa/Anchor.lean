/-
# Admissibility forces the anchored structure

The concavity theorem of the note covers every *ordered anchored* cell, and there is an
unanchored sign pattern on which the second variation is positive
(`E₁ = E₂ = [0.4, 1.2]`, with `sup ½δ²Q/‖η‖² = +0.4123`).  That looked like a genuine
obstruction to any global statement: concavity is not merely unproved off the anchored
cells, it is false there.

It is not an obstruction, because no admissible cap realises such a pattern.  Under (RC)
the arm sandwich gives

    α₂' ≤ -α₁        and        α₁' ≥ α₂ ,

and orderedness (`E₁ ⊆ E₂`) says `α₂ ≤ 0 → α₁ ≥ 0`.  Together: wherever `α₂` is
nonpositive its derivative is nonpositive, so `{α₂ > 0}` is downward closed — anchored.
And on that set `α₁' ≥ α₂ > 0`, so `α₁` is strictly increasing and `{α₁ < 0}` is an
initial segment too.

`anchored_of_ordered` is the first half, `a1_strictMono_on_E2` the second.  The
hypothesis that the two arms do not vanish simultaneously is genuine and is stated: at a
point where `α₂ = 0` and `α₂` is about to become positive, the argument forces
`α₂' = α₁ = 0`, and only non-degeneracy rules that out.  At Σ it holds because
`α₁(0) = -H'(0) = -1/2`.

The consequence recorded in the note: the restriction to anchored cells is a restriction
on the bookkeeping, not on the competitor class.
-/
import Mathlib

namespace MovingSofa

open Set

/-- **The anchoring step.**  Under (RC) and orderedness, `{α₂ > 0}` is downward closed.

Stated as: if `a2` is nonpositive at the left endpoint, it stays nonpositive.  That is
what "anchored" means -- `E₂ = {α₂ > 0}` cannot be re-entered once left, so it is an
initial segment.

The three hypotheses are exactly the note's:

* `hsand` is the arm sandwich `α₂' ≤ -α₁` from (RC);
* `hord` is orderedness `E₁ ⊆ E₂`, in the contrapositive form `α₂ ≤ 0 → α₁ ≥ 0`;
* `hne` is the non-degeneracy, that the arms do not vanish simultaneously.

`hne` is doing real work and is not removable by a trick.  Without it the derivative bound
at a touching point is only `α₂' ≤ 0`, non-strict, and a non-strict bound does not fence:
`α₂` could sit at `0` and leave.  With it, `α₂ x = 0` forces `α₁ x ≠ 0`, orderedness makes
that `α₁ x > 0`, and the sandwich upgrades the bound to the strict `α₂' x < 0` that
Mathlib's fencing theorem asks for.  At Σ the hypothesis holds because `α₁(0) = -1/2`. -/
theorem anchored_of_ordered
    (a1 a2 a2' : ℝ → ℝ) {s t : ℝ}
    (hcont : ContinuousOn a2 (Icc s t))
    (hderiv : ∀ u ∈ Ico s t, HasDerivWithinAt a2 (a2' u) (Ici u) u)
    (hsand : ∀ u ∈ Ico s t, a2' u ≤ - a1 u)
    (hord : ∀ u ∈ Ico s t, a2 u ≤ 0 → 0 ≤ a1 u)
    (hne : ∀ u ∈ Ico s t, ¬(a1 u = 0 ∧ a2 u = 0))
    (hs : a2 s ≤ 0) :
    ∀ ⦃u⦄, u ∈ Icc s t → a2 u ≤ 0 := by
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := a2) (f' := a2')
    (B := fun _ => (0 : ℝ)) (B' := fun _ => (0 : ℝ)) hcont hderiv hs
    continuousOn_const (fun u _ => (hasDerivAt_const u (0 : ℝ)).hasDerivWithinAt)
    (fun u hu hz => by
      -- at a touching point `a2 u = 0`, non-degeneracy makes `a1 u` strictly positive
      have h0 : a2 u = 0 := hz
      have hge : 0 ≤ a1 u := hord u hu (le_of_eq h0)
      have hnz : a1 u ≠ 0 := fun h => hne u hu ⟨h, h0⟩
      have hpos : 0 < a1 u := lt_of_le_of_ne hge (Ne.symm hnz)
      calc a2' u ≤ - a1 u := hsand u hu
        _ < 0 := by linarith)
  exact fun u hu => key hu

/-- **The second half.**  On `E₂` the sandwich gives `α₁' ≥ α₂ > 0`, so `α₁` is strictly
increasing there and `{α₁ < 0}` is an initial segment.  Stated as the monotonicity that
delivers it. -/
theorem a1_strictMono_on_E2
    (a1 a1' a2 : ℝ → ℝ) {s t : ℝ}
    (hcont : ContinuousOn a1 (Icc s t))
    (hderiv : ∀ u ∈ interior (Icc s t), HasDerivAt a1 (a1' u) u)
    (hsand : ∀ u ∈ interior (Icc s t), a2 u ≤ a1' u)
    (hE2 : ∀ u ∈ interior (Icc s t), 0 < a2 u) :
    StrictMonoOn a1 (Icc s t) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc s t) hcont
  intro u hu
  rw [(hderiv u hu).deriv]
  exact lt_of_lt_of_le (hE2 u hu) (hsand u hu)

/-- **Ordering forces a corner.**  The moment bound behind `prop:corner`: under (RC) the
absolutely continuous part of `H + H''` is at most `1`, so its `sin`-moment over
`[0, π/2]` is at most `∫ sin = 1`.  Since `α₂(0) = ∫₀^{π/2} r sin - 1 + a` and ordering
forces `α₂(0) > 0` (because `α₁(0) = -1/2 < 0` always puts `0` in `E₁`), the atom mass `a`
at `π/2` must be strictly positive unless `r = 1` almost everywhere. -/
theorem moment_le_one {r : ℝ → ℝ} (hint : IntervalIntegrable r MeasureTheory.volume 0 (Real.pi / 2))
    (hr : ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2), r s ≤ 1) :
    ∫ s in (0 : ℝ)..(Real.pi / 2), r s * Real.sin s ≤ 1 := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hsin : ∫ s in (0 : ℝ)..(Real.pi / 2), Real.sin s = 1 := by
    rw [integral_sin]; simp
  calc ∫ s in (0 : ℝ)..(Real.pi / 2), r s * Real.sin s
      ≤ ∫ s in (0 : ℝ)..(Real.pi / 2), Real.sin s := by
        apply intervalIntegral.integral_mono_on hpi (hint.mul_continuousOn
          (Real.continuous_sin.continuousOn)) (Real.continuous_sin.intervalIntegrable _ _)
        intro s hs
        have h0 : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
          (le_trans hs.2 (by linarith [Real.pi_pos]))
        nlinarith [hr s hs, h0]
    _ = 1 := hsin

/-- **The corner bound.**  Packaging `moment_le_one` with the sign hypothesis: if
`α₂(0) = m - 1 + a > 0` and `m ≤ 1`, then the atom mass `a` is strictly positive.  This is
what makes `anchored_of_ordered` non-vacuous -- without an atom no cap is ordered at all,
and the anchoring theorem would be a statement about the empty set. -/
theorem atom_pos_of_ordered {m a : ℝ} (hm : m ≤ 1) (hpos : 0 < m - 1 + a) : 0 < a := by
  linarith

end MovingSofa
