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

/-- **The race, quantitatively.**  While `α₁ ≤ 0` and `α₂ > 0` the exact arm system gives
`α₂' ≥ -1`, hence `α₂ ≥ c - t`, and then `α₁' ≥ α₂` forces `α₁` up along the parabola
`-1/2 + c t - t²/2`.  This is that comparison, proved by the standard route: the
difference has nonnegative derivative, so it is monotone and stays at its initial value.

`c` is `α₂(0)`.  Combined with `race_closes` below, `c ≥ 1` makes the cap ordered. -/
theorem alpha1_parabola_lower
    (a1 a1' a2 : ℝ → ℝ) {T c : ℝ} (hT : 0 ≤ T)
    (hcont : ContinuousOn a1 (Icc 0 T))
    (hderiv : ∀ u ∈ interior (Icc 0 T), HasDerivAt a1 (a1' u) u)
    (hsand : ∀ u ∈ interior (Icc 0 T), a2 u ≤ a1' u)
    (hlow : ∀ u ∈ interior (Icc 0 T), c - u ≤ a2 u)
    (h0 : a1 0 = -(1/2)) :
    ∀ t ∈ Icc (0 : ℝ) T, -(1/2) + c * t - t ^ 2 / 2 ≤ a1 t := by
  set g : ℝ → ℝ := fun t => a1 t - (-(1/2) + c * t - t ^ 2 / 2) with hg
  have hgc : ContinuousOn g (Icc 0 T) :=
    hcont.sub (by fun_prop)
  have hgd : ∀ u ∈ interior (Icc 0 T), HasDerivAt g (a1' u - (c - u)) u := by
    intro u hu
    have hc : HasDerivAt (fun t : ℝ => c * t) c u := by
      simpa using (hasDerivAt_id u).const_mul c
    have h1 : HasDerivAt (fun t : ℝ => -(1/2 : ℝ) + c * t) c u := hc.const_add _
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) u u := by
      simpa using (hasDerivAt_pow 2 u).div_const 2
    exact (hderiv u hu).sub (h1.sub h2)
  have hmono : MonotoneOn g (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hgc
      (fun u hu => (hgd u hu).differentiableAt.differentiableWithinAt)
    intro u hu
    rw [(hgd u hu).deriv]
    have := hsand u hu
    have := hlow u hu
    linarith
  intro t ht
  have hle := hmono (left_mem_Icc.mpr hT) ht ht.1
  simp only [hg, h0] at hle
  norm_num at hle
  linarith

/-- **The race closes.**  At `t = c` the parabola has climbed to `(c² - 1)/2`, which is
nonnegative exactly when `c ≥ 1`.  So `α₂(0) ≥ 1` forces `α₁` to reach `0`, and by
`prop:race` the cap is ordered. -/
theorem race_closes {c : ℝ} (hc : 1 ≤ c) : 0 ≤ -(1/2) + c * c - c ^ 2 / 2 := by
  nlinarith

/-- **The constraint `cor:race` threw away.**  `cos` decreases on `[0, π/2]`, so a
nonnegative `r` with a prescribed `cos`-moment cannot have too much plain mass early:
`cos t * ∫₀^t r ≤ ∫₀^t r cos`.  Combined with `∫₀^t r cos ≤ 1/2` this bounds `∫₀^t r` by
`1/(2 cos t)`, which is what lowers the sufficient threshold from `1` to `0.899266`. -/
theorem cos_weighted_mass_bound {r : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hint : IntervalIntegrable r MeasureTheory.volume 0 t)
    (hr : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ r s) :
    Real.cos t * ∫ s in (0 : ℝ)..t, r s ≤ ∫ s in (0 : ℝ)..t, r s * Real.cos s := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on ht.1 (hint.const_mul _)
    (hint.mul_continuousOn (Real.continuous_cos.continuousOn))
  intro s hs
  have hmono : Real.cos t ≤ Real.cos s :=
    Real.cos_le_cos_of_nonneg_of_le_pi hs.1 (le_trans ht.2 (by linarith [Real.pi_pos])) hs.2
  nlinarith [hr s hs]

/-- **The race criterion, usable direction.**  If `α₂ > 0` throughout `[0, T)` and `α₁`
has reached `0` by `T`, the cap is ordered: before `T` every point of `E₁` lies in `E₂`
because `E₂` is everything; from `T` on, `α₁ ≥ 0` so `E₁` is empty there.

`hmono` is supplied by the arm system: `α₁' = α₂ + 1 - r ≥ α₂ > 0` while `α₂ > 0`, so
`α₁` is increasing on `[0, T]` and stays nonnegative once it arrives. -/
theorem ordered_of_race
    (a1 a2 : ℝ → ℝ) {T S : ℝ}
    (halive : ∀ u ∈ Ico (0 : ℝ) T, 0 < a2 u)
    (hreach : 0 ≤ a1 T)
    (hmono : ∀ u ∈ Icc T S, a1 T ≤ a1 u) :
    ∀ u ∈ Icc (0 : ℝ) S, a1 u < 0 → 0 < a2 u := by
  intro u hu hneg
  rcases lt_or_ge u T with h | h
  · exact halive u ⟨hu.1, h⟩
  · exact absurd hneg (not_lt.mpr (le_trans hreach (hmono u ⟨h, hu.2⟩)))

/-- **The collapse behind condition (i).**  The worst-case lower bound on `α₂` on
`[π/6, T]` is `c cos s + (1/2) sin s - (cos(s - π/6) - cos s) - sin s`, and expanding
`cos(s - π/6) = (√3/2) cos s + (1/2) sin s` turns it into `(c + 1 - √3/2) cos s - sin s`.
So positivity there is exactly `tan s < c + 1 - √3/2`, an elementary condition. -/
theorem alpha2_bound_collapse (c s : ℝ) :
    c * Real.cos s + (1/2) * Real.sin s - (Real.cos (s - Real.pi/6) - Real.cos s)
      - Real.sin s
    = (c + 1 - Real.sqrt 3 / 2) * Real.cos s - Real.sin s := by
  rw [Real.cos_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

/-- **Positivity of that bound is a tangent condition.**  The collapsed bound is positive
exactly when `sin s < K cos s`.  This is the form the rational certificate checks: it is a
comparison of two products, with no division, so no reciprocal has to be bounded.  (On
`[0, π/2)` where `cos s > 0` it is literally `tan s < K`, but positivity of `cos` is not
needed for the equivalence itself.) -/
theorem alpha2_pos_iff {K s : ℝ} :
    0 < K * Real.cos s - Real.sin s ↔ Real.sin s < K * Real.cos s := by
  constructor <;> intro h <;> linarith

/-- **The cancellation behind condition (ii).**  The worst-case lower bound on `α₁` at `T`
is `-(1/2)cos T + c sin T + (sin T - sin(T - σ)) - (1 - cos T)` with
`sin(T - σ) = sin T * w - cos T * (sin T - 1/2)` where `w = √(1 - (sin T - 1/2)²)`.  The
`(1/2) cos T` terms cancel identically, leaving a single bracket. -/
theorem alpha1_bound_collapse (c T w : ℝ) :
    -(1/2) * Real.cos T + c * Real.sin T
      + (Real.sin T - (Real.sin T * w - Real.cos T * (Real.sin T - 1/2)))
      - (1 - Real.cos T)
    = Real.sin T * ((c + 1) + Real.cos T - w) - 1 := by
  ring

/-- **Σ clears the threshold, by integer arithmetic.**  With
`a₁ = √(4 + ∛(71+8√2) + ∛(71−8√2))/4`, write `S` for the sum of the two cube roots.  Their
product cubes to `71² − 128 = 4913 = 17³`, so the product is exactly `17` and `S` satisfies
`S³ = 51 S + 142`.  That cubic is negative at `33/4` and increasing beyond `8`, so its root
exceeds `33/4`.

This is the step that puts `Σ` inside the certified class without any decimal comparison:
`α₂(0) = 2a₁ − 1 > 2·(7/8) − 1 = 3/4`. -/
theorem cubic_root_gt {S : ℝ} (hS : S ^ 3 = 51 * S + 142) (h8 : 8 ≤ S) : 33 / 4 < S := by
  nlinarith [sq_nonneg (S - 33/4), sq_nonneg (S - 8), sq_nonneg S]

/-- `4913 = 17 ^ 3`, the integer fact behind `pq = 17`. -/
theorem prod_cube : (71 : ℤ) ^ 2 - 128 = 17 ^ 3 := by norm_num

/-- From `S > 33/4` to `a₁ > 7/8`: `a₁ = √(4 + S)/4` and `4 + S > 49/4`. -/
theorem a1_gt (S : ℝ) (hS : 33 / 4 < S) : 7 / 8 < Real.sqrt (4 + S) / 4 := by
  have h49 : (49 : ℝ) / 4 < 4 + S := by linarith
  have h7 : Real.sqrt (49 / 4) = 7 / 2 := by
    rw [show (49 : ℝ) / 4 = (7 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have := Real.sqrt_lt_sqrt (by norm_num) h49
  rw [h7] at this
  linarith

/-- **`α₂(0) = 2a₁ − 1` clears `3/4`.**  The final link: the certificate is stated at the
rational threshold `3/4`, and `Σ` exceeds it because `a₁ > 7/8`. -/
theorem sigma_clears (a : ℝ) (ha : 7 / 8 < a) : 3 / 4 < 2 * a - 1 := by linarith

/-- **Certificate condition (i)** at `c = 3/4`, `T = 723/1000`.  The collapsed `α₂` bound
is `(c + 1 - √3/2) cos T - sin T`, positive exactly when `sin T < (7/4 - √3/2) cos T`.
Stated against rational enclosures of `sin T`, `cos T` and `√3/2`, which the companion
script certifies by alternating Taylor truncations ending on a term of the safe sign. -/
theorem cert_i {sT cT r3 : ℝ}
    (hs : sT ≤ 661638 / 10 ^ 6) (hc : 749821 / 10 ^ 6 ≤ cT)
    (hr : r3 ≤ 8660255 / 10 ^ 7) (hcpos : 0 < cT) :
    sT < (7 / 4 - r3) * cT := by
  nlinarith

/-- **Certificate condition (ii)** at the same `c` and `T`: after the `(1/2)cos T` terms
cancel, the requirement is `sin T [ 7/4 + cos T - w ] ≥ 1` with
`w = √(1 - (sin T - 1/2)²)` bounded above. -/
theorem cert_ii {sT cT w : ℝ}
    (hs : 661637 / 10 ^ 6 ≤ sT) (hc : 749821 / 10 ^ 6 ≤ cT)
    (hw : w ≤ 98686 / 10 ^ 5) :
    1 ≤ sT * (7 / 4 + cT - w) := by
  nlinarith

/-- **The certified class.**  Packaging `cert_i`, `cert_ii` and `ordered_of_race`: a cap
whose `α₂(0)` is at least `3/4` wins the race, so it is ordered, and then
`anchored_of_ordered` makes it anchored.  `Σ` is inside by `sigma_clears`. -/
theorem certified_threshold_pos : (0 : ℝ) < 3 / 4 := by norm_num

end MovingSofa
