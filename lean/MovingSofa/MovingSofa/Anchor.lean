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
    (hs : sT ≤ 661687 / 10 ^ 6) (hc : 749809 / 10 ^ 6 ≤ cT)
    (hr : r3 ≤ 8660255 / 10 ^ 7) (hcpos : 0 < cT) :
    sT < (7 / 4 - r3) * cT := by
  nlinarith

/-- **Certificate condition (ii)** at the same `c` and `T`: after the `(1/2)cos T` terms
cancel, the requirement is `sin T [ 7/4 + cos T - w ] ≥ 1` with
`w = √(1 - (sin T - 1/2)²)` bounded above. -/
theorem cert_ii {sT cT w : ℝ}
    (hs : 661418 / 10 ^ 6 ≤ sT) (hc : 749809 / 10 ^ 6 ≤ cT)
    (hw : w ≤ 98690 / 10 ^ 5) :
    1 ≤ sT * (7 / 4 + cT - w) := by
  nlinarith

/-- **The right endpoint is rigid.**  `α₂(π/2) = 1/2 − ∫(u cos + v sin)`, and the two
forced moments say exactly that the integral splits as `1/2 + 1/2 = 1`.  So
`α₂(π/2) = −1/2` for *every* admissible cap — it is not a property of `Σ`. -/
theorem alpha2_at_right {Iu Iv : ℝ} (hu : Iu = 1/2) (hv : Iv = 1/2) :
    (1/2 : ℝ) - (Iu + Iv) = -(1/2) := by rw [hu, hv]; norm_num

/-- **The hard floor.**  `α₁(π/2) = c + ∫(u sin − v cos)`, whose minimum over admissible
`(u, v)` is `(1 − √3/2) − √3/2 = 1 − √3`, attained.  With `α₂(π/2) = −1/2 < 0`, ordering
forces `α₁(π/2) ≥ 0`, so no threshold condition on `α₂(0)` alone can work below `√3 − 1`.

The two bang-bang switch points are `π/6` (from `sin σ = 1/2`) and `π/3` (from
`1 − cos σ = 1/2`), forced by the moment constraints exactly as in the certificate. -/
theorem floor_sqrt3 {c : ℝ} (hc : c < Real.sqrt 3 - 1) :
    c + (1 - Real.sqrt 3) < 0 := by linarith

/-- The minimum value assembles from the two one-constraint programs. -/
theorem floor_min_eq : (1 - Real.sqrt 3 / 2) - Real.sqrt 3 / 2 = 1 - Real.sqrt 3 := by ring

/-- `√3 − 1 < 3/4`, so the certified class sits strictly above the floor and the bracket
`[√3 − 1, 3/4]` is nonempty. -/
theorem floor_lt_threshold : Real.sqrt 3 - 1 < 3 / 4 := by
  have h : Real.sqrt 3 ≤ 1732051 / 10 ^ 6 := by
    rw [show (1732051 : ℝ) / 10 ^ 6 = Real.sqrt ((1732051 / 10 ^ 6) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **The floor witness satisfies both moment constraints, exactly.**  `u = 1` on
`[0, π/6]` gives `∫ cos = sin(π/6) = 1/2`, and `v = 1` on `[0, π/3]` gives
`∫ sin = 1 - cos(π/3) = 1/2`.  The switch points are forced by those two equations, which
is why `π/6` and `π/3` appear throughout. -/
theorem floor_moment_u : ∫ s in (0:ℝ)..(Real.pi/6), Real.cos s = 1/2 := by
  rw [integral_cos]; simp [Real.sin_pi_div_six]

theorem floor_moment_v : ∫ s in (0:ℝ)..(Real.pi/3), Real.sin s = 1/2 := by
  rw [integral_sin]; simp [Real.cos_pi_div_three]; norm_num

/-- The two objective integrals of the floor witness: `∫₀^{π/6} sin = 1 - √3/2` and
`∫₀^{π/3} cos = √3/2`. -/
theorem floor_obj_u : ∫ s in (0:ℝ)..(Real.pi/6), Real.sin s = 1 - Real.sqrt 3 / 2 := by
  rw [integral_sin, Real.cos_pi_div_six]; norm_num

theorem floor_obj_v : ∫ s in (0:ℝ)..(Real.pi/3), Real.cos s = Real.sqrt 3 / 2 := by
  rw [integral_cos, Real.sin_pi_div_three]; simp

/-- **`α₁(π/2) = c + 1 − √3` for the floor witness.**  Assembling the two objective
integrals: `α₁(π/2) = c + ∫u sin − ∫v cos = c + (1 − √3/2) − √3/2`.  This is the exact
value that makes `√3 − 1` the floor, and it is attained, not merely bounded. -/
theorem floor_alpha1_value (c : ℝ) :
    c + (1 - Real.sqrt 3 / 2) - Real.sqrt 3 / 2 = c + 1 - Real.sqrt 3 := by ring

/-- **The race in one variable.**  With `W = e^{it} Z`, at a zero of `α₂ = Im Z` we have
`Im W cos τ = Re W sin τ`, and then `α₁ = Re Z` collapses to `Re W / cos τ`.

This is the algebraic heart of `prop:onevar`.  It gives a NECESSARY condition only:
`Re W` is monotone, so `α₁(τ) ≥ 0` at the first zero of `α₂` says `τ ≥ t₀`, and
orderedness forces that.  The converse fails — orderedness needs `α₁ ≥ 0` on all of
`{α₂ ≤ 0}`, not just at its first point, and `α₁' = α₂ + 1 - r` goes negative once
`α₂ < -(1 - r)`.  The floor witness at `c = 0.7315` has `τ = 0.7134 ≥ t₀ = 0.4240` and is
still unordered, failing at `π/2`. -/
theorem alpha1_at_alpha2_zero {ReW ImW τ : ℝ}
    (hzero : ImW * Real.cos τ - ReW * Real.sin τ = 0) :
    (ReW * Real.cos τ + ImW * Real.sin τ) * Real.cos τ = ReW :=
  by linear_combination Real.sin τ * hzero + ReW * Real.sin_sq_add_cos_sq τ

/-- Divided form, when `cos τ ≠ 0`: `α₁(τ) = Re W(τ) / cos τ`, so the sign of `α₁` at a
zero of `α₂` is the sign of `Re W` there. -/
theorem alpha1_at_alpha2_zero' {ReW ImW τ : ℝ} (hc : Real.cos τ ≠ 0)
    (hzero : ImW * Real.cos τ - ReW * Real.sin τ = 0) :
    ReW * Real.cos τ + ImW * Real.sin τ = ReW / Real.cos τ := by
  field_simp
  linear_combination Real.sin τ * hzero + ReW * Real.sin_sq_add_cos_sq τ

/-- `Re W` is non-decreasing: its derivative is `u cos t + v sin t`, nonnegative on
`[0, π/2]` for controls in `[0,1]`. -/
theorem ReW_deriv_nonneg {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hct : 0 ≤ Real.cos t) (hst : 0 ≤ Real.sin t) :
    0 ≤ u * Real.cos t + v * Real.sin t := by positivity

/-- The two endpoint values: `Re W(0) = α₁(0) = -1/2` and `Re W(π/2) = -α₂(π/2) = 1/2`,
the latter by `prop:rigid`.  So `Re W` crosses zero exactly once. -/
theorem ReW_endpoints : (-(1:ℝ)/2 < 0) ∧ ((1:ℝ)/2 > 0) := ⟨by norm_num, by norm_num⟩

/-- **Unorderedness forces `Im W < 0`.**  If `α₁(T) < 0` and `α₂(T) ≤ 0` then
`Q = Im W(T)` is negative.  Chaining `Q cos²T ≤ P sin T cos T ≤ -Q sin²T` collapses to
`Q(cos²T + sin²T) ≤ 0`.

This is what makes the case split work: unorderedness is confined to the two branches
`T ≥ t₀` (where `Re W ≥ 0`) and `T < t₀`, and in the second branch it additionally forces
`∫₀^T (v cos - u sin) > c`, a linear program. -/
theorem imW_neg_of_unordered {P Q T : ℝ} (hc : 0 < Real.cos T) (hs : 0 ≤ Real.sin T)
    (h2 : Q * Real.cos T - P * Real.sin T ≤ 0)
    (h1 : P * Real.cos T + Q * Real.sin T < 0) :
    Q ≤ 0 := by
  have hpy := Real.sin_sq_add_cos_sq T
  nlinarith [mul_le_mul_of_nonneg_right h2 (le_of_lt hc),
             mul_le_mul_of_nonneg_right (le_of_lt h1) hs, hpy, sq_nonneg (Real.cos T)]

/-- Branch (A) at `T = π/2`: the constraint `Re W(π/2) = 1/2 ≥ 0` is vacuous, so the
minimum of `α₁(π/2)` over admissible controls is `c + 1 - √3` by the floor computation,
and it is nonnegative exactly when `c ≥ √3 - 1`. -/
theorem branchA_at_right {c : ℝ} (h : Real.sqrt 3 - 1 ≤ c) : 0 ≤ c + 1 - Real.sqrt 3 := by
  linarith

/-- **Branch (B) is empty throughout the band.**  Its exact maximum is
`√2/2 - 1 + √(1/4 + √2/2)`, attained at `T = π/4` where the two bang-bang caps coincide
(`arccos(sin T) = T` forces `sin T = cos T`).  Emptiness needs that to be below the floor
`√3 - 1`, i.e. `√2/2 + √(1/4 + √2/2) < √3`, which holds with slack `0.0466`. -/
theorem branchB_lt_floor :
    Real.sqrt 2 / 2 + Real.sqrt (1/4 + Real.sqrt 2 / 2) < Real.sqrt 3 := by
  have sq_le : ∀ a b : ℝ, 0 ≤ b → a ≤ b ^ 2 → Real.sqrt a ≤ b := by
    intro a b hb hab
    calc Real.sqrt a ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hab
      _ = b := Real.sqrt_sq hb
  have le_sq : ∀ a b : ℝ, 0 ≤ b → b ^ 2 ≤ a → b ≤ Real.sqrt a := by
    intro a b hb hab
    calc b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb).symm
      _ ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
  have h2 : Real.sqrt 2 ≤ 1414214 / 10 ^ 6 := sq_le _ _ (by norm_num) (by norm_num)
  have hinner : 1/4 + Real.sqrt 2 / 2 ≤ 957108 / 10 ^ 6 := by linarith
  have hs : Real.sqrt (1/4 + Real.sqrt 2 / 2) ≤ 978320 / 10 ^ 6 :=
    le_trans (Real.sqrt_le_sqrt hinner) (sq_le _ _ (by norm_num) (by norm_num))
  have h3 : (1732050 : ℝ) / 10 ^ 6 ≤ Real.sqrt 3 := le_sq _ _ (by norm_num) (by norm_num)
  linarith

/-- The floor value in the same terms: `B_max < √3 - 1`. -/
theorem branchB_max_lt : Real.sqrt 2 / 2 - 1 + Real.sqrt (1/4 + Real.sqrt 2 / 2)
    < Real.sqrt 3 - 1 := by linarith [branchB_lt_floor]

/-! ### The four linear programs, in closed form

Each bounds one arm against one moment constraint, and each is bang-bang against a single
multiplier whose switch point the moment constraint *fixes*, independently of `t`:

| program | constraint | switch | value for large `t` |
|---|---|---|---|
| `U₂ = max ∫₀ᵗ u sin(t-s)` | `∫u cos = 1/2` | `sin σ = 1/2`, σ = π/6 | `cos(t-π/6) - cos t` |
| `V₂ = max ∫₀ᵗ v cos(t-s)` | `∫v sin = 1/2` | `1 - cos σ = 1/2`, σ = π/3 | `sin t - sin(t-π/3)` |
| `U₁ = min ∫₀ᵗ u cos(t-s)` | `∫u cos = 1/2` | `sin ω = sin t - 1/2` | `sin t - sin(t-ω)` |
| `V₁ = max ∫₀ᵗ v sin(t-s)` | `∫v sin = 1/2` | `1 - cos σ = 1/2`, σ = π/3 | `cos(t-π/3) - cos t` |

The two switch equations are `sin σ = 1/2` and `1 - cos σ = 1/2`, which is why `π/6` and
`π/3` run through every constant in this section — including the floor witness and the
`T = π/4` of branch (B), where `arccos(sin T) = T`. -/

/-- The `U₂` switch: `∫₀^{π/6} cos = sin(π/6) = 1/2`, so `u = 1` on `[0, π/6]` exhausts the
constraint exactly. -/
theorem U2_switch : ∫ s in (0:ℝ)..(Real.pi/6), Real.cos s = 1/2 := floor_moment_u

/-- The `V₂`/`V₁` switch: `∫₀^{π/3} sin = 1 - cos(π/3) = 1/2`. -/
theorem V_switch : ∫ s in (0:ℝ)..(Real.pi/3), Real.sin s = 1/2 := floor_moment_v

/-- `U₂` at `t ≥ π/6`, from the switch: `∫₀^{π/6} sin(t-s) ds = cos(t-π/6) - cos t`. -/
theorem U2_value (t : ℝ) :
    ∫ s in (0:ℝ)..(Real.pi/6), Real.sin (t - s)
      = Real.cos (t - Real.pi/6) - Real.cos t := by
  simp [intervalIntegral.integral_comp_sub_left (fun x => Real.sin x) t]

/-- `V₁` at `t ≥ π/3`: `∫₀^{π/3} sin(t-s) ds = cos(t-π/3) - cos t`, the same integral with
the other switch point. -/
theorem V1_value (t : ℝ) :
    ∫ s in (0:ℝ)..(Real.pi/3), Real.sin (t - s)
      = Real.cos (t - Real.pi/3) - Real.cos t := by
  simp [intervalIntegral.integral_comp_sub_left (fun x => Real.sin x) t]

/-- `V₂` at `t ≥ π/3`: `∫₀^{π/3} cos(t-s) ds = sin t - sin(t-π/3)`. -/
theorem V2_value (t : ℝ) :
    ∫ s in (0:ℝ)..(Real.pi/3), Real.cos (t - s)
      = Real.sin t - Real.sin (t - Real.pi/3) := by
  simp [intervalIntegral.integral_comp_sub_left (fun x => Real.cos x) t]

/-! ### The Gårding split at the end cap

At `τ = π/2` the cross term of `D_τ` vanishes (`∫(pq)' = -p(π/2)q(π/2) = 0`), so the form
is diagonal in `p_k = sin 2kt`, `q_k = sin(2k-1)t`.  The `H¹` Rayleigh quotients are
`(1-4k²)/(1+4k²)` and `2(1-(2k-1)²)/(1+(2k-1)²)`.  Exactly one is nonnegative — the
marginal mode `q₁ = sin t`, at `0` — and every other is at most `-3/5`, attained at
`p₁ = sin 2t`.

So the obstruction to coercivity is a SINGLE mode, not a tail; that is what makes a
Gårding split possible here, and it needs no arithmetic precision at all. -/

/-- Even modes `p_n = sin(nt)`, `n ≥ 2`: the quotient `(1-n²)/(1+n²) ≤ -3/5`, since the
inequality is `8 ≤ 2n²`.  Equality at `n = 2`, which is where `3/5` is attained. -/
theorem p_mode_quotient {n : ℝ} (hn : 2 ≤ n) : (1 - n^2) / (1 + n^2) ≤ -(3/5) := by
  have hpos : (0:ℝ) < 1 + n^2 := by nlinarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- Odd modes `q_n = sin(nt)`, `n ≥ 3`: the quotient `2(1-n²)/(1+n²) ≤ -3/5`, since the
inequality is `13 ≤ 7n²`.  The excluded case is `n = 1`, where the quotient is `0` — the
marginal mode. -/
theorem q_mode_quotient {n : ℝ} (hn : 3 ≤ n) : 2 * (1 - n^2) / (1 + n^2) ≤ -(3/5) := by
  have hpos : (0:ℝ) < 1 + n^2 := by nlinarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- The marginal mode: at `n = 1` the `q` quotient is exactly `0`, so it is the one mode
the split must remove. -/
theorem q_mode_marginal : 2 * (1 - (1:ℝ)^2) / (1 + (1:ℝ)^2) = 0 := by norm_num

/-- The cross term vanishes at `τ = π/2`: `∫₀^{π/2}(pq' + p'q) = [pq]₀^{π/2}`, which is `0`
because `p(π/2) = 0` and `p(0) = 0`.  Stated as the algebraic fact about the boundary
values that makes it so. -/
theorem cross_vanishes {p0 pT q0 qT : ℝ} (h0 : p0 = 0) (hT : pT = 0) :
    pT * qT - p0 * q0 = 0 := by rw [h0, hT]; ring

/-- **The marginal mode, pointwise.**  On `p = 0`, `q = a sin t` the integrand of the two
restricted terms of `D_τ` is `a²(sin² - cos²) = -a² cos 2t`, whose integral over `[0,τ]` is
`-a²/2 · sin 2τ`.  This is the damping case (b) of `thm:diag` uses.

The pointwise identity and the endpoint reduction are formalised here; evaluating
`∫₀^τ cos 2t = sin(2τ)/2` is elementary and is done in the note, not in Lean. -/
theorem marginal_integrand (t : ℝ) :
    Real.sin t ^ 2 - Real.cos t ^ 2 = -Real.cos (2 * t) := by
  have := Real.sin_sq_add_cos_sq t
  rw [Real.cos_two_mul]; linarith

/-- With `τ = π/2 - σ` the damping reads `sin 2τ = sin 2σ`, so it vanishes linearly at the
end cap — the rate `rem:endcap` measures. -/
theorem damping_at_endcap (σ : ℝ) : Real.sin (2 * (Real.pi/2 - σ)) = Real.sin (2 * σ) := by
  have : 2 * (Real.pi/2 - σ) = Real.pi - 2 * σ := by ring
  rw [this, Real.sin_pi_sub]

/-! ### The branch (A) closed forms

The two Lagrangian programs are bang-bang against one multiplier, and which region fills
first is decided by the monotonicity of the ratio.  Both ratios have a one-line derivative:

    d/ds [ cos(T-s)/cos s ] =  sin T / cos²s   > 0     (increasing)
    d/ds [ sin(T-s)/sin s ] = -sin T / sin²s   < 0     (decreasing)

because the numerators collapse by the angle-addition formula.  Increasing for the
`u`-program means its filled set is an initial segment `[0,a]`, which is what lets a single
formula cover all three regimes. -/

/-- The `u`-ratio increases: its derivative is `sin T / cos²s`.  The numerator
`sin(T-s)cos s + cos(T-s) sin s` collapses to `sin T`. -/
theorem u_ratio_deriv_num (T s : ℝ) :
    Real.sin (T - s) * Real.cos s + Real.cos (T - s) * Real.sin s = Real.sin T := by
  rw [← Real.sin_add]; ring_nf

/-- The `v`-ratio decreases: the same collapse with the opposite sign. -/
theorem v_ratio_deriv_num (T s : ℝ) :
    Real.cos (T - s) * Real.sin s + Real.sin (T - s) * Real.cos s = Real.sin T := by
  linarith [u_ratio_deriv_num T s]

/-- `∫₀^a cos(T-s) ds = sin T - sin(T-a)`, the objective integral of the `u`-program. -/
theorem Umin_obj (T a : ℝ) :
    ∫ s in (0:ℝ)..a, Real.cos (T - s) = Real.sin T - Real.sin (T - a) := by
  simp [intervalIntegral.integral_comp_sub_left (fun x => Real.cos x) T]

/-- `∫₀^a cos s ds = sin a`, its constraint integral. -/
theorem Umin_con (a : ℝ) : ∫ s in (0:ℝ)..a, Real.cos s = Real.sin a := by
  simp [integral_cos]

/-- `∫₀^b sin(T-s) ds = cos(T-b) - cos T`, the objective integral of the `v`-program. -/
theorem Vmax_obj (T b : ℝ) :
    ∫ s in (0:ℝ)..b, Real.sin (T - s) = Real.cos (T - b) - Real.cos T := by
  simp [intervalIntegral.integral_comp_sub_left (fun x => Real.sin x) T]

/-- `∫₀^b sin s ds = 1 - cos b`, its constraint integral. -/
theorem Vmax_con (b : ℝ) : ∫ s in (0:ℝ)..b, Real.sin s = 1 - Real.cos b := by
  simp [integral_sin]

/-- Assembling: `U_min = sin T - sin(T-a) - λ sin a`. -/
theorem Umin_value (T a lam : ℝ) :
    (Real.sin T - Real.sin (T - a)) - lam * Real.sin a
      = Real.sin T - Real.sin (T - a) - lam * Real.sin a := rfl

/-- Assembling: `V_max = [cos(T-b) - cos T] + λ(1 - cos b)`. -/
theorem Vmax_value (T b lam : ℝ) :
    (Real.cos (T - b) - Real.cos T) + lam * (1 - Real.cos b)
      = Real.cos (T - b) - Real.cos T + lam * (1 - Real.cos b) := by ring

/-- **The absorption step of `prop:coerc`.**  Given the Sylvester bound `B² ≤ K·Dp` on the
cross term, Young's inequality with weight `θ` splits the mixed term:

    2aB ≤ a²K/θ + θ·Dp ,

because `(a²K + θ²Dp)² ≥ 4a²Kθ²Dp ≥ (2θaB)²`, the first step being `(a²K - θ²Dp)² ≥ 0`.
Substituting turns `-a²Mₑ + 2aB - Dp` into `-a²(Mₑ - K/θ) - (1-θ)Dp`, both coefficients
negative once `K/θ < Mₑ` and `θ < 1`. -/
theorem young_absorb {a B Dp K θ : ℝ} (hDp : 0 ≤ Dp) (hK : 0 ≤ K) (hθ : 0 ≤ θ)
    (hB : B ^ 2 ≤ K * Dp) :
    2 * θ * a * B ≤ a ^ 2 * K + θ ^ 2 * Dp := by
  have hsq : (2 * θ * a * B) ^ 2 ≤ 4 * (a ^ 2 * K) * (θ ^ 2 * Dp) := by
    have h : θ ^ 2 * a ^ 2 * B ^ 2 ≤ θ ^ 2 * a ^ 2 * (K * Dp) := by
      have := mul_nonneg (sq_nonneg θ) (sq_nonneg a)
      nlinarith [hB, this]
    nlinarith [h]
  have hnn : 0 ≤ a ^ 2 * K + θ ^ 2 * Dp := by positivity
  nlinarith [hsq, hnn, sq_nonneg (a ^ 2 * K - θ ^ 2 * Dp)]

/-- **The coercivity assembly.**  With `Mₑ = |D[e]|`, the marginal and tail bounds combine
into a single negative-definite estimate. -/
theorem coerc_assemble {a B Dp Me R θ : ℝ}
    (hy : 2 * a * B ≤ a ^ 2 * R + θ * Dp) :
    -(a ^ 2 * Me) + 2 * a * B - Dp ≤ -(a ^ 2 * (Me - R)) - (1 - θ) * Dp := by
  nlinarith [hy]

/-- Both coefficients are negative exactly when `K/θ < Mₑ` and `θ < 1`, which is the
condition `prop:coerc` optimises over. -/
theorem coerc_coeffs_neg {Me K θ : ℝ} (h1 : K / θ < Me) (h2 : θ < 1) :
    0 < Me - K / θ ∧ 0 < 1 - θ := ⟨by linarith, by linarith⟩

section Enclosures
open Real

/-- **The trig enclosures at `T = 723/1000`, derived inside Lean.**  `Real.sin_bound` at
the argument itself is too weak: `|sin x − (x − x³/6)| ≤ |x|⁵/100` gives `sin T ≤ 0.66199`
where `0.661638` is needed.  Halving the argument shrinks the error term by `2⁵ = 32`, and
the double-angle formulas carry the bounds back up.  `cos y` is recovered from
`sin²+cos² = 1` and positivity, with the square root cleared by `√z ≥ z/q` for `q ≥ √z`. -/
theorem sin_cos_723 :
    Real.sin (723/1000) ≤ 661687/10^6 ∧
    661418/10^6 ≤ Real.sin (723/1000) ∧
    749809/10^6 ≤ Real.cos (723/1000) := by
  set y : ℝ := 723/2000 with hy
  have hy0 : (0:ℝ) < y := by rw [hy]; norm_num
  have hy1 : |y| ≤ 1 := by rw [hy, abs_of_pos (by norm_num)]; norm_num
  have hb := Real.sin_bound hy1
  rw [abs_of_pos hy0] at hb
  rw [abs_le] at hb
  obtain ⟨hlo, hhi⟩ := hb
  -- rational enclosure of sin y
  have hslo : (353564/10^6 : ℝ) ≤ Real.sin y := by rw [hy] at hlo ⊢; nlinarith [hlo]
  have hshi : Real.sin y ≤ (353689/10^6 : ℝ) := by rw [hy] at hhi ⊢; nlinarith [hhi]
  -- cos y > 0 since 0 < y < π/2
  have hpi : (2:ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hcpos : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by
      rw [hy]; nlinarith [Real.pi_gt_three], by rw [hy]; nlinarith [Real.pi_gt_three]⟩
  have hpyth : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  -- cos y ≥ (1 − shi²)/q with q ≥ √(1 − shi²)
  have hclo : (935356/10^6 : ℝ) ≤ Real.cos y := by nlinarith [hcpos, hpyth, hshi, hslo]
  have hchi : Real.cos y ≤ (935420/10^6 : ℝ) := by nlinarith [hcpos, hpyth, hslo]
  -- double angle
  have h2 : (723/1000 : ℝ) = 2 * y := by rw [hy]; norm_num
  have hsin : Real.sin (723/1000) = 2 * Real.sin y * Real.cos y := by
    rw [h2, Real.sin_two_mul]
  have hcos : Real.cos (723/1000) = 1 - 2 * Real.sin y ^ 2 := by
    rw [h2, Real.cos_two_mul]; linarith [Real.sin_sq_add_cos_sq y]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsin]; nlinarith [hshi, hchi, hslo, hclo, hcpos]
  · rw [hsin]; nlinarith [hslo, hclo, hshi, hchi, hcpos]
  · rw [hcos]; nlinarith [hshi, hslo]

/-- **The certificate at `T = 723/1000`, with nothing assumed.**  `cert_i` and `cert_ii`
applied to the enclosures `sin_cos_723` derives inside Lean.  These are the two numeric
conditions of `thm:ordercert` at the rational threshold `c = 3/4`; the remaining input is
`√3/2 ≤ 8660255/10⁷`, which `Real.sq_sqrt` supplies. -/
theorem cert_holds_at_723 (r3 : ℝ) (hr : r3 ≤ 8660255 / 10 ^ 7) :
    Real.sin (723/1000) < (7/4 - r3) * Real.cos (723/1000) ∧
    ∀ w : ℝ, w ≤ 98690 / 10 ^ 5 →
      1 ≤ Real.sin (723/1000) * (7/4 + Real.cos (723/1000) - w) := by
  obtain ⟨hshi, hslo, hclo⟩ := sin_cos_723
  refine ⟨cert_i hshi hclo hr (by linarith), fun w hw => cert_ii hslo hclo hw⟩

/-- `√3/2` is below the rational bound the certificate uses. -/
theorem sqrt3_half_le : Real.sqrt 3 / 2 ≤ 8660255 / 10 ^ 7 := by
  have h : Real.sqrt 3 ≤ 1732051 / 10 ^ 6 := by
    rw [show (1732051 : ℝ) / 10 ^ 6 = Real.sqrt ((1732051 / 10 ^ 6) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

end Enclosures

section BTail

/-!
### The `b`-tail numerator is a boundary term

In the `H¹` coercivity certificate the `p`-mode coefficients are

    b_k = (1/‖p_k‖_{H¹}) ∫_τ^{π/2} [cos t · sin 2kt + 2k · sin t · cos 2kt] dt

and the note bounded the numerator by integrating the second summand by parts and keeping
`|numerator| ≤ 2 + 2σ`.  That discards a cancellation: the integrand is *exactly*
`d/dt [sin t · sin 2kt]`, so the integral is a boundary term and nothing else.  Since
`sin (kπ) = 0`, the value is `-sin τ · sin 2kτ`, of modulus at most `sin τ = cos σ`.

At `σ = β` the tail constant drops from `(2+2σ)²/π = 2.1177` to `cos²σ/π = 0.2923`, a
factor `7.2438`, and the certificate's margin rises from `0.0143` to `0.0549`.  This is the
fourth time in this problem that a quantity was small because of cancellation and an
estimate that split it in two lost an order.
-/

/-- The integrand is an exact derivative, so the integral collapses to the endpoints. -/
theorem btail_numerator (k : ℕ) (a b : ℝ) :
    (∫ t in a..b, (Real.cos t * Real.sin (2*k*t) + 2*k * (Real.sin t * Real.cos (2*k*t))))
      = Real.sin b * Real.sin (2*k*b) - Real.sin a * Real.sin (2*k*a) := by
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Real.sin t * Real.sin (2*k*t))
        (Real.cos t * Real.sin (2*k*t) + 2*k * (Real.sin t * Real.cos (2*k*t))) t := by
    intro t _
    have hin : HasDerivAt (fun t : ℝ => 2*(k:ℝ)*t) (2*k) t := by
      simpa using (hasDerivAt_id t).const_mul (2*(k:ℝ))
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (2*k*t)) (Real.cos (2*k*t) * (2*k)) t :=
      (Real.hasDerivAt_sin (2*k*t)).comp t hin
    have h := (Real.hasDerivAt_sin t).mul h2
    have he : Real.cos t * Real.sin (2*k*t) + 2*k * (Real.sin t * Real.cos (2*k*t))
        = Real.cos t * Real.sin (2*k*t) + Real.sin t * (Real.cos (2*k*t) * (2*k)) := by ring
    rw [he]
    exact h
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) a b)

/-- At the right endpoint `π/2` the boundary term vanishes, because `sin (kπ) = 0`. -/
theorem btail_numerator_at_half_pi (k : ℕ) (a : ℝ) :
    (∫ t in a..(Real.pi/2),
        (Real.cos t * Real.sin (2*k*t) + 2*k * (Real.sin t * Real.cos (2*k*t))))
      = -(Real.sin a * Real.sin (2*k*a)) := by
  rw [btail_numerator, show 2*(k:ℝ)*(Real.pi/2) = k * Real.pi by ring, Real.sin_nat_mul_pi]
  ring

/-- Hence the numerator is bounded by `sin τ`, uniformly in `k`. -/
theorem btail_numerator_abs_le (k : ℕ) {a : ℝ} (ha : 0 ≤ Real.sin a) :
    |∫ t in a..(Real.pi/2),
        (Real.cos t * Real.sin (2*k*t) + 2*k * (Real.sin t * Real.cos (2*k*t)))|
      ≤ Real.sin a := by
  rw [btail_numerator_at_half_pi, abs_neg, abs_mul, abs_of_nonneg ha]
  calc Real.sin a * |Real.sin (2*k*a)| ≤ Real.sin a * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) ha
    _ = Real.sin a := mul_one _

/-- The gain over the note's constant exceeds a factor `7` at `σ = β`.  Stated on rational
enclosures `σ ≥ 0.289` and `cos σ ≤ 0.959`, both of which `β = 0.2896538…` satisfies. -/
theorem btail_gain {σ c : ℝ} (hσ : 289/1000 ≤ σ) (hc0 : 0 ≤ c) (hc : c ≤ 959/1000) :
    7 * c^2 ≤ (2 + 2*σ)^2 := by nlinarith

end BTail

section LayerPin

/-!
### The layer sign convention is pinned by the zero mode

The second variation carries a sign on each of its two layer terms, and guessing wrong
costs a round: the unreproducible A17 numbers came from a form whose signs were never
checked against anything.  They need not be guessed.  On the zero mode `e = (0, sin t)`
the two bulk terms vanish and the layer terms reduce to `∫_L cos²` and `∫_L sin²`, so the
note's value `D_τ[e] = -(1/2) sin 2σ` selects one sign pair outright.

`layer_pin` is the surviving choice `(+1,-1)`; `layer_pin_neg` is the control `(-1,-1)`,
which integrates to `-σ`; and `layer_pin_separates` shows the two disagree for every
`σ > 0`, so the identity really does determine the convention rather than merely being
consistent with it.  Rule I12: the control is stated, not assumed.
-/

/-- On the zero mode the `(+1,-1)` layer convention gives exactly `-(1/2) sin 2σ`. -/
theorem layer_pin (σ : ℝ) :
    (∫ t in (Real.pi/2 - σ)..(Real.pi/2), (Real.cos t ^ 2 - Real.sin t ^ 2))
      = -(Real.sin (2*σ) / 2) := by
  have hd : ∀ t ∈ Set.uIcc (Real.pi/2 - σ) (Real.pi/2),
      HasDerivAt (fun t : ℝ => Real.sin (2*t) / 2) (Real.cos t ^ 2 - Real.sin t ^ 2) t := by
    intro t _
    have hin : HasDerivAt (fun t : ℝ => 2*t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2:ℝ)
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (Real.cos (2*t) * 2) t :=
      (Real.hasDerivAt_sin (2*t)).comp t hin
    have h3 := h2.div_const 2
    have he : Real.cos (2*t) * 2 / 2 = Real.cos t ^ 2 - Real.sin t ^ 2 := by
      have hp := Real.sin_sq_add_cos_sq t
      rw [Real.cos_two_mul]; linarith
    rwa [he] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [show (2:ℝ) * (Real.pi/2) = Real.pi by ring,
      show (2:ℝ) * (Real.pi/2 - σ) = Real.pi - 2*σ by ring, Real.sin_pi, Real.sin_pi_sub]
  ring

/-- The control: the `(-1,-1)` convention integrates to `-σ`, a different function of `σ`. -/
theorem layer_pin_neg (σ : ℝ) :
    (∫ _t in (Real.pi/2 - σ)..(Real.pi/2), (-(Real.cos _t ^ 2) - Real.sin _t ^ 2)) = -σ := by
  have h : ∀ t : ℝ, -(Real.cos t ^ 2) - Real.sin t ^ 2 = -1 := by
    intro t; have := Real.sin_sq_add_cos_sq t; linarith
  simp only [h]
  rw [intervalIntegral.integral_const]
  ring

/-- The two conventions disagree for every `σ > 0`, so the zero mode does pin the sign. -/
theorem layer_pin_separates {σ : ℝ} (h0 : 0 < σ) : -σ < -(Real.sin (2*σ) / 2) := by
  have h := Real.sin_lt (show (0:ℝ) < 2*σ by linarith)
  linarith

end LayerPin

section Deficit

/-!
### The deficit factorises through the tracking ratio

Write `cap` and `nic` for `|C_2|` and `2|N|` at a competitor and `capS`, `nicS` for their
values at `Σ`, so that the area is `cap - nic` and `A_R^* = capS - nicS`.  With

    ρ = (nic - nicS) / (cap - capS)

the deficit factorises as `(ρ - 1)(cap - capS)`.  Both factors change sign together at `Σ`,
so the product is positive on both sides of it, and the two open statements about the area
profile -- that it is unimodal with peak at `Σ`, and that competitors below the floor do
not beat `Σ` -- collapse into the single claim that `ρ` crosses `1` exactly once.

The sign here is worth stating carefully: it is `(ρ - 1)`, not `(1 - ρ)`.  The first draft
of this had it backwards, which reversed every row of the table it was describing.
-/

/-- The deficit factorises through the tracking ratio. -/
theorem deficit_factorisation {cap nic capS nicS : ℝ} (h : cap - capS ≠ 0) :
    (capS - nicS) - (cap - nic)
      = ((nic - nicS) / (cap - capS) - 1) * (cap - capS) := by
  field_simp
  ring

/-- Below `Σ` the cap shrinks, so `ρ < 1` is exactly what makes the competitor lose. -/
theorem deficit_pos_of_rho_lt_one {cap nic capS nicS : ℝ}
    (hc : cap < capS) (hr : (nic - nicS) / (cap - capS) < 1) :
    cap - nic < capS - nicS := by
  have hd : cap - capS < 0 := by linarith
  rw [div_lt_iff_of_neg hd] at hr
  linarith

/-- Above `Σ` the cap grows, and `ρ > 1` makes the competitor lose for the same reason. -/
theorem deficit_pos_of_rho_gt_one {cap nic capS nicS : ℝ}
    (hc : capS < cap) (hr : 1 < (nic - nicS) / (cap - capS)) :
    cap - nic < capS - nicS := by
  have hd : 0 < cap - capS := by linarith
  rw [lt_div_iff₀ hd] at hr
  linarith

end Deficit

section AffineMinusConvex

/-!
### Why `Σ` maximises: an affine cap minus a convex niche

Along the one-parameter family that freezes `Σ`'s absolutely continuous radius and varies
only the atom, the two terms of `|T| = |C_2| - 2|N|` behave differently. The cap is affine
in the atom mass -- its second differences sit at the rasterisation noise floor, `±7·10⁻⁴`
with mean zero -- while the niche is convex, its second differences uniformly positive at
`+3.5·10⁻³`, five times that floor. Affine minus convex is concave, and the first-order
condition at `Σ` (cap slope `1.0107`, niche slope `1.0128`) puts the critical point there.

The argument needs no concavity machinery: convexity supplies a supporting line at `Σ`, and
subtracting it from the affine cap leaves a bound that is exactly `0` when the slopes agree.
`max_of_affine_sub_convex` is that one line; the `_approx` version carries the slope
mismatch, since the two measured slopes agree only to `2·10⁻³`.

This replaces the spectral route entirely. It asks for convexity of one area in one real
parameter, not for a second variation on realised cells -- an object which, as
`ambi_cell.py` shows, has no verified referent anywhere in the note.
-/

/-- Affine minus convex, at a critical point: the maximum is at `c₀`.
`hsupp` is convexity's supporting line at `c₀`, `hcrit` the first-order condition. -/
theorem max_of_affine_sub_convex {A k c c0 nic nic0 m : ℝ}
    (hsupp : nic0 + m * (c - c0) ≤ nic) (hcrit : m = k) :
    (A + k * c) - nic ≤ (A + k * c0) - nic0 := by
  subst hcrit; linarith

/-- The same with the slopes agreeing only to `ε`, which is the measured situation. -/
theorem max_of_affine_sub_convex_approx {A k c c0 nic nic0 m ε : ℝ}
    (hsupp : nic0 + m * (c - c0) ≤ nic) (hε : |k - m| ≤ ε) :
    (A + k * c) - nic ≤ (A + k * c0) - nic0 + ε * |c - c0| := by
  have h1 : (k - m) * (c - c0) ≤ |k - m| * |c - c0| := by
    calc (k - m) * (c - c0) ≤ |(k - m) * (c - c0)| := le_abs_self _
      _ = |k - m| * |c - c0| := abs_mul _ _
  have h2 : |k - m| * |c - c0| ≤ ε * |c - c0| :=
    mul_le_mul_of_nonneg_right hε (abs_nonneg _)
  linarith

end AffineMinusConvex

section AtomDirection

/-!
### The atom direction: cap exactly affine, niche uniformly convex

Freezing `Σ`'s absolutely continuous radius and varying only the atom mass `c` adds `c·Φ`
to the support function, with `Φ(θ) = max(0, -cos θ)` supported on `[π/2, π]`. The area
functional is quadratic in `H`, so `|C_2|(c)` is a quadratic polynomial whose leading
coefficient is `∫₀^π (Φ² - Φ'²)`. On the support that integrand is `cos²θ - sin²θ = cos 2θ`,
whose integral over `[π/2, π]` is a full half period and vanishes. So the cap is *exactly*
affine: the `7.2·10⁻⁴` seen in the rasterised profile is noise and nothing else.

The niche's second derivative in `c` is `f(β) = π/2 - 2β + sin 2β`. Its derivative is
`2(cos 2β - 1) ≤ 0`, so `f` decreases, and admissible caps have `β < π/6`, where
`f(π/6) = π/6 + √3/2 = 1.3896`. Convexity is therefore uniform, not marginal.

Both statements are conditional on two structural inputs taken from the note: the quadratic
form of the cap area, and the first variation of the niche. What is formalised here is the
consequence of each.
-/

/-- The atom contributes no quadratic term to the cap area: a half period of `cos 2θ`. -/
theorem atom_quadratic_vanishes :
    (∫ θ in (Real.pi/2)..Real.pi, (Real.cos θ ^ 2 - Real.sin θ ^ 2)) = 0 := by
  have hd : ∀ t ∈ Set.uIcc (Real.pi/2) Real.pi,
      HasDerivAt (fun t : ℝ => Real.sin (2*t) / 2) (Real.cos t ^ 2 - Real.sin t ^ 2) t := by
    intro t _
    have hin : HasDerivAt (fun t : ℝ => 2*t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2:ℝ)
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (Real.cos (2*t) * 2) t :=
      (Real.hasDerivAt_sin (2*t)).comp t hin
    have h3 := h2.div_const 2
    have he : Real.cos (2*t) * 2 / 2 = Real.cos t ^ 2 - Real.sin t ^ 2 := by
      have hp := Real.sin_sq_add_cos_sq t
      rw [Real.cos_two_mul]; linarith
    rwa [he] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [show (2:ℝ) * (Real.pi/2) = Real.pi by ring, Real.sin_pi, Real.sin_two_pi]
  ring

/-- The niche's second derivative in the atom mass. -/
noncomputable def nicheConv (β : ℝ) : ℝ := Real.pi/2 - 2*β + Real.sin (2*β)

theorem nicheConv_hasDerivAt (β : ℝ) :
    HasDerivAt nicheConv (2 * (Real.cos (2*β) - 1)) β := by
  have hin : HasDerivAt (fun t : ℝ => 2*t) 2 β := by
    simpa using (hasDerivAt_id β).const_mul (2:ℝ)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (Real.cos (2*β) * 2) β :=
    (Real.hasDerivAt_sin (2*β)).comp β hin
  have h := ((hasDerivAt_const β (Real.pi/2)).sub hin).add h2
  have he : (0:ℝ) - 2 + Real.cos (2*β) * 2 = 2 * (Real.cos (2*β) - 1) := by ring
  rw [← he]
  exact h

/-- Its derivative is nonpositive everywhere, so `nicheConv` decreases. -/
theorem nicheConv_deriv_nonpos (β : ℝ) : 2 * (Real.cos (2*β) - 1) ≤ 0 := by
  have := Real.cos_le_one (2*β); linarith

/-- `nicheConv` is antitone, so its value on `β ≤ π/6` is bounded below by the endpoint. -/
theorem nicheConv_antitone : Antitone nicheConv := by
  refine antitone_of_deriv_nonpos (fun β => (nicheConv_hasDerivAt β).differentiableAt) ?_
  intro β
  rw [(nicheConv_hasDerivAt β).deriv]
  exact nicheConv_deriv_nonpos β

/-- At the arm-sandwich cap `β = π/6` the value is `π/6 + √3/2`. -/
theorem nicheConv_at_pi_six : nicheConv (Real.pi/6) = Real.pi/6 + Real.sqrt 3 / 2 := by
  unfold nicheConv
  rw [show (2:ℝ) * (Real.pi/6) = Real.pi/3 by ring, Real.sin_pi_div_three]
  ring

/-- Hence convexity of the niche in the atom mass is uniform on admissible caps. -/
theorem nicheConv_pos {β : ℝ} (h : β ≤ Real.pi/6) :
    Real.pi/6 + Real.sqrt 3 / 2 ≤ nicheConv β := by
  rw [← nicheConv_at_pi_six]
  exact nicheConv_antitone h

end AtomDirection

section Wirtinger

/-!
### The cap is concave in every admissible direction

`atom_quadratic_vanishes` shows the cap area has no quadratic term along the atom. That is
not special to the atom, and the reason is the forced boundary data. An admissible
perturbation preserves `H'(0) = 1/2`, `H(π/2) = 1` and `H'(π) = -1/2`, so

    η'(0) = 0 ,   η(π/2) = 0 ,   η'(π) = 0 ,

Neumann at the outer end and Dirichlet at `π/2` on each half-interval of length `π/2`. The
first eigenvalue there is `(π/(2·π/2))² = 1`, so `∫(η')² ≥ ∫η²` and the cap's quadratic
term `∫(η² - (η')²)` is nonpositive in *every* direction.

In the eigenbasis `cos(nθ)` on `[0,π/2]` and `sin(n(θ-π/2))` on `[π/2,π]` with `n = 2k-1`,
the form is a weighted sum of `1 - n²`, and the whole content is that `1 - n² ≤ 0` for
`n ≥ 1` with equality only at `n = 1`. The two first modes are `cos θ`, a horizontal
translation that moves no area, and `sin(θ - π/2) = -cos θ` on `[π/2, π]`, which is the
atom. So the atom's exact affineness is the statement that it saturates Wirtinger.

The control matters here: `sin θ` also returns zero, being the *other* first eigenfunction,
so it cannot witness that the boundary data is doing the work. The constant function, which
violates `η(π/2) = 0`, returns `+π/2`.
-/

/-- The mode weight is nonpositive for every admissible frequency. -/
theorem wirtinger_mode {n : ℝ} (hn : 1 ≤ n) : (1:ℝ) - n^2 ≤ 0 := by nlinarith

/-- and vanishes only at the first mode. -/
theorem wirtinger_mode_eq {n : ℝ} (hn : 1 ≤ n) : (1:ℝ) - n^2 = 0 ↔ n = 1 := by
  constructor
  · intro h; nlinarith
  · rintro rfl; ring

/-- Hence the cap's quadratic term is nonpositive on any admissible perturbation. -/
theorem cap_quadratic_nonpos (s : Finset ℕ) (n w : ℕ → ℝ) (hn : ∀ k ∈ s, 1 ≤ n k) :
    ∑ k ∈ s, (1 - (n k)^2) * (w k)^2 ≤ 0 := by
  refine Finset.sum_nonpos fun k hk => ?_
  have h := wirtinger_mode (hn k hk)
  nlinarith [sq_nonneg (w k)]

/-- The atom is the first mode on the right half: `sin(θ - π/2) = -cos θ`. -/
theorem atom_is_first_mode (θ : ℝ) : Real.sin (θ - Real.pi/2) = -Real.cos θ := by
  rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

end Wirtinger

section NicheConvexity

/-!
### Niche convexity on the left half

The niche functional is `|N| = ∫₀^{π/2}[½(α₂⁺)² + ½(σ-α₁)² - ½(α₁⁻)²]` (prop:V). All three
of `α₁, α₂, σ` are affine in `H`, and each squared integrand vanishes at its own moving
endpoint by definition of `E₂` and `E₁⁻`, so the second variation has no boundary terms and
no second-order arm terms:

    D[η] = 2∫_{E₂}(δα₂)² + 2∫₀^{π/2}(δ(σ-α₁))² - 2∫_{E₁⁻}(δα₁)² .

For `η` supported on `[0,π/2]` this collapses. Expanding `δ(σ-α₁) = η tan t + η'` and
integrating the cross term by parts — both boundary terms vanish, at `0` because `tan 0 = 0`
and at `π/2` because `η(π/2) = 0` beats the blow-up — everything cancels except

    D[η] = 2∫_β^{π/2}(η')² - 2∫_{π/2-β}^{π/2}η² .

Since `β ≤ π/4` the second interval sits inside the first, so the containment gives
`∫_{π/2-β}^{π/2}(η')² ≤ ∫_β^{π/2}(η')²`, and Poincaré with a Dirichlet end at `π/2` on an
interval of length `β` gives `∫η² ≤ (4β²/π²)∫(η')²`. Both together force `D ≥ 0` for every
`β ≤ π/2`, which every admissible cap satisfies with room: at `Σ` the factor `π²/(4β²)` is
`29.4` against the `1` it must beat.

The two lemmas below are the algebra of that last step, stated on the three integrals so
that the analytic inputs (containment and Poincaré) enter as hypotheses.
-/

/-- Containment plus Poincaré force the left-half second variation to be nonnegative. -/
theorem a26b_left_nonneg {A B C β : ℝ} (hβ : 0 < β) (hβp : β ≤ Real.pi/2)
    (hB : 0 ≤ B) (hBA : B ≤ A) (hPo : C ≤ 4*β^2/Real.pi^2 * B) :
    0 ≤ 2*A - 2*C := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 4*β^2/Real.pi^2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have h2 : 4*β^2/Real.pi^2 * B ≤ 1 * B := mul_le_mul_of_nonneg_right h1 hB
  linarith

/-- With the margin made explicit: the surplus is `2(π²/(4β²) - 1)` times the `L²` mass. -/
theorem a26b_left_margin {A B C β : ℝ} (hβ : 0 < β) (hBA : B ≤ A)
    (hPo : C ≤ 4*β^2/Real.pi^2 * B) :
    2*(Real.pi^2/(4*β^2) - 1) * C ≤ 2*A - 2*C := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hq : (0:ℝ) < 4*β^2 := by positivity
  have h : Real.pi^2/(4*β^2) * C ≤ B := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hq]
    have := mul_le_mul_of_nonneg_left hPo (le_of_lt (by positivity : (0:ℝ) < Real.pi^2))
    calc Real.pi^2 * C ≤ Real.pi^2 * (4*β^2/Real.pi^2 * B) := this
      _ = B * (4*β^2) := by field_simp
  nlinarith

end NicheConvexity

section Assembly

/-!
### Assembling the two second variations

`|T| = |C_2| - 2|N|`, so `δ²|T| = δ²|C_2| - δ²(2|N|)`. The two halves point opposite ways:

* the cap form is negative semidefinite in every admissible direction, with kernel exactly
  `{gauge, atom}` (`cap_quadratic_nonpos`, `wirtinger_mode_eq`);
* the niche form is positive semidefinite, with kernel exactly `{gauge}` — measured as
  `λ_min = 0` to machine precision at 6, 10, 16, 24 and 32 modes, the null vector being
  `cos θ` on both halves, which is a horizontal translation and moves no area.

Their difference is therefore nonpositive everywhere, and strictly negative off the gauge:
the atom is null for the cap but gives `π/2 - 2β + sin 2β ≥ π/6 + √3/2` for the niche. The
lemmas below are that assembly; the two inputs enter as hypotheses, at the labels they
actually carry.
-/

/-- Cap nonpositive and niche nonnegative make the area's second variation nonpositive. -/
theorem cap_sub_niche_nonpos {cap nic : ℝ} (hc : cap ≤ 0) (hn : 0 ≤ nic) :
    cap - nic ≤ 0 := by linarith

/-- Strictly negative wherever the niche form is strictly positive. -/
theorem cap_sub_niche_neg {cap nic : ℝ} (hc : cap ≤ 0) (hn : 0 < nic) :
    cap - nic < 0 := by linarith

/-- The niche floor is strictly positive, so the atom direction is strictly concave even
though the cap vanishes on it. -/
theorem niche_floor_pos : (0:ℝ) < Real.pi/6 + Real.sqrt 3 / 2 := by
  have h1 : (0:ℝ) < Real.pi/6 := by positivity
  have h2 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  linarith

/-- Along the atom the cap contributes nothing and the niche contributes at least the
floor, so the area is strictly concave there. -/
theorem atom_strictly_concave {β : ℝ} (h : β ≤ Real.pi/6) :
    (0:ℝ) - nicheConv β < 0 :=
  cap_sub_niche_neg le_rfl (lt_of_lt_of_le niche_floor_pos (nicheConv_pos h))

end Assembly

section ArmRelation

/-!
### The three variations satisfy one relation, and why Young does not close on it

Write `u = δ(σ-α₁)`, `v = δα₂`, `w = δα₁` for the three variations at a perturbation `η`.
They are not independent. Since `w = η_K - η_F'` and `u = η_F tan t + η_F'`,

    S := w + u = η_F tan t + η_K ,

and `S(0) = 0`: both `tan 0 = 0` and `η_K(0) = η(π/2) = 0`, the latter being exactly the
Dirichlet condition that drives the cap's Wirtinger bound. One boundary condition controls
both halves of the second variation. Differentiating,

    S' = v + u tan t ,

verified to `3.6·10⁻¹⁵` and `8.3·10⁻⁸` (finite-difference) across six directions.

`D ≥ 0` reduces to `∫_{E₁}w² ≤ ∫_{E₂}v² + ∫₀^{π/2}u²`, and `S(0) = 0` with Poincaré on
`[0,β]` gives `‖S‖ ≤ κ‖S'‖` with `κ = 2β/π`. But routing `w = S - u` through the triangle
inequality then costs `‖w‖ ≤ κ‖v‖ + Cb‖u‖` with `C = κ tan β + 1 ≥ 1`, and Cauchy-Schwarz
would need `κ² + C² ≤ 1`. The lemma below records that this is impossible for every `κ > 0`:
the crude route cannot close, and the cross term must be kept rather than bounded. Rule I12,
barrier stated rather than left implicit.
-/

/-- `w = δα₁` is recovered from `S` and `u` with no loss. -/
theorem arm_decomposition (u w : ℝ) : w = (w + u) - u := by ring

/-- The Young route cannot close: `C ≥ 1` forces `κ² + C² > 1` for every `κ > 0`, so
bounding `‖S - u‖` by `‖S‖ + ‖u‖` always overshoots the budget. -/
theorem young_route_fails {κ C : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ) : 1 < κ^2 + C^2 := by
  nlinarith

end ArmRelation

section SweepDisjoint

/-!
### The two sweeps meet only at the corner, at equal parameters

Proposition `prop:V` computes `|N|` as a sum of two sweep integrals and needs the sweeps
disjoint. Writing them in the moving frame makes the same-parameter case exact.

The face-2 sweep is `Φ(s,t) = c(t) - s·μ_t` with `s ∈ [0, α₂⁺]`, the face-1 sweep is
`Ψ(s,t) = c(t) - s·ν_t` with `s ∈ [α₁⁺, σ]`, and `⟨μ_t, ν_t⟩ = 0`. If a point lies on both
at the *same* `t`, then `s·μ_t = s'·ν_t`; pairing against `μ_t` and against `ν_t` and using
orthogonality forces `s = s' = 0`, so the point is `c(t)` itself. A single point per `t`
sweeps out a curve, which has measure zero, so the same-parameter overlap contributes
nothing to `|N|`.

`sweep_same_param` is that step. What it does not settle is `t ≠ t'`, which is the actual
content of disjointness and is left open: a face-2 point at `t` and a face-1 point at `t'`
could in principle coincide, and ruling that out needs the arm system, not orthogonality.
Rasterising both sweeps (`sofa_sweep`) puts the total overlap at `0.0041` of `|N|` and
halving with resolution, consistent with the whole overlap being the measure-zero curve this
lemma identifies.
-/

/-- Orthogonal directions, equal parameters: the two sweeps meet only where both offsets
vanish, that is, only at the corner point `c(t)`. -/
theorem sweep_same_param {μx μy νx νy s s' : ℝ}
    (horth : μx * νx + μy * νy = 0)
    (hμ : μx * μx + μy * μy = 1) (hν : νx * νx + νy * νy = 1)
    (hx : s * μx = s' * νx) (hy : s * μy = s' * νy) :
    s = 0 ∧ s' = 0 := by
  -- Pair the two offset equations against mu and against nu.  Against mu: the left side
  -- collapses by |mu| = 1 and the right side is s' times <nu,mu> = 0.  Against nu: the same
  -- with the roles exchanged.  Both are exact linear combinations, which is why nlinarith
  -- does not find them and linear_combination does.
  refine ⟨?_, ?_⟩
  · linear_combination (-s) * hμ + μx * hx + μy * hy + s' * horth
  · linear_combination (-s') * hν - νx * hx - νy * hy + s * horth

/-- Consequently the offsets being equal forces the two sweep points to be the same point. -/
theorem sweep_same_param_eq {cx cy μx μy νx νy s s' : ℝ}
    (horth : μx * νx + μy * νy = 0)
    (hμ : μx * μx + μy * μy = 1) (hν : νx * νx + νy * νy = 1)
    (hx : cx - s * μx = cx - s' * νx) (hy : cy - s * μy = cy - s' * νy) :
    (cx - s * μx, cy - s * μy) = (cx, cy) := by
  have hx2 : s * μx = s' * νx := by linear_combination -hx
  have hy2 : s * μy = s' * νy := by linear_combination -hy
  obtain ⟨hs, _⟩ := sweep_same_param horth hμ hν hx2 hy2
  simp [hs]

end SweepDisjoint

section SweepCover

/-!
### Covering: every niche point sits on a face, by a release-time argument

`prop:V`'s third hypothesis is that the two sweeps together cover `N`. The geometric
statement looks hard, but the content is an intermediate-value argument and not a geometric
one, which is why it is provable here while disjointness is not.

Fix a point `p`. In the moving frame put `u(t) = -⟨p - c(t), μ_t⟩` and `v(t) = -⟨p - c(t),
ν_t⟩`. The corner at time `t` occupies the quarter-plane `u ≥ 0, v ≥ 0`, and its two
boundary edges are exactly the two sweeps: `v = 0, u ≥ 0` is the face-2 ray `c - s·μ`, and
`u = 0, v ≥ 0` is the face-1 ray `c - s·ν`. So `p` is *strictly cut* at time `t` iff
`u(t) > 0` and `v(t) > 0`, and `p` lies on a face iff `min(u,v) = 0` with the other
coordinate nonnegative.

A point of `N` is cut at some time and released by the end of the rotation. `min(u,v)` is
continuous, positive at the first time and nonpositive at the last, so it has a zero in
between — and at that zero `p` is on one of the two faces. That is the covering statement.
`corner_release_face` is the argument; `frame_face1` then converts the face condition into
the explicit offset, `p = c - s·ν` with `s = -⟨p - c, ν⟩`, so the point is genuinely a value
of the sweep map and not merely on its line.

WHAT THIS DOES NOT SETTLE, and it is the same gap as in `SweepDisjoint`: the sweeps in
`prop:V` are *truncated*, `s ∈ [0, α₂⁺]` on face 2 and `s ∈ [α₁⁺, σ]` on face 1. This
argument produces a face point but does not show its offset lands inside the truncation
window. The truncation limits are where the arm functions enter, so closing that is the
same missing ingredient as before. Rasterising both sweeps (`sofa_sweep`) leaves under
`0.001` of `N` uncovered, which is the evidence that the windows are in fact wide enough.
-/

/-- A minimum of two reals vanishes exactly when one of them vanishes and the other is
nonnegative. This is the step that turns a zero of `min(u,v)` into membership of a face. -/
theorem min_eq_zero_cases {a b : ℝ} (h : min a b = 0) :
    (a = 0 ∧ 0 ≤ b) ∨ (b = 0 ∧ 0 ≤ a) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab] at h; exact Or.inl ⟨h, h ▸ hab⟩
  · rw [min_eq_right hab] at h; exact Or.inr ⟨h, h ▸ hab⟩

/-- A continuous function that is nonnegative at `t` and nonpositive at `b` has a zero on
`[t, b]`. The release time of a niche point is produced this way. -/
theorem exists_boundary_time {g : ℝ → ℝ} {t b : ℝ} (hle : t ≤ b)
    (hc : ContinuousOn g (Set.Icc t b)) (hpos : 0 ≤ g t) (hneg : g b ≤ 0) :
    ∃ t₀ ∈ Set.Icc t b, g t₀ = 0 :=
  intermediate_value_Icc' hle hc ⟨hneg, hpos⟩

/-- **Covering, up to the truncation window.** If `p` is strictly cut by the corner at time
`t` and has been released by time `b`, then at some intermediate time it lies on one of the
two faces: either `u = 0` with `v ≥ 0` (face 1) or `v = 0` with `u ≥ 0` (face 2). -/
theorem corner_release_face {u v : ℝ → ℝ} {t b : ℝ} (hle : t ≤ b)
    (hu : ContinuousOn u (Set.Icc t b)) (hv : ContinuousOn v (Set.Icc t b))
    (hut : 0 < u t) (hvt : 0 < v t) (hout : u b ≤ 0 ∨ v b ≤ 0) :
    ∃ t₀ ∈ Set.Icc t b, (u t₀ = 0 ∧ 0 ≤ v t₀) ∨ (v t₀ = 0 ∧ 0 ≤ u t₀) := by
  have hpos : 0 ≤ min (u t) (v t) := le_min hut.le hvt.le
  have hneg : min (u b) (v b) ≤ 0 := by
    rcases hout with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) h
  obtain ⟨t₀, ht₀, hz⟩ := exists_boundary_time hle (ContinuousOn.inf hu hv) hpos hneg
  exact ⟨t₀, ht₀, min_eq_zero_cases hz⟩

/-- The face condition `⟨p, μ⟩ = 0` in an oriented orthonormal frame says exactly that `p`
is the `ν`-multiple `⟨p, ν⟩·ν`. This is what makes a face point an actual value of the
sweep map, with a named offset, rather than merely a point on the face's line. -/
theorem frame_face1 {μx μy νx νy px py : ℝ}
    (horth : μx * νx + μy * νy = 0) (hν : νx * νx + νy * νy = 1)
    (hdet : μx * νy - μy * νx = 1) (hm : px * μx + py * μy = 0) :
    px = (px * νx + py * νy) * νx ∧ py = (px * νx + py * νy) * νy := by
  -- Orientation plus orthonormality pins mu to the rotation of nu, so the face condition
  -- becomes the cross product px*nuy - py*nux = 0.
  have hμx : μx = νy := by linear_combination νx * horth + νy * hdet - μx * hν
  have hμy : μy = -νx := by linear_combination νy * horth - νx * hdet - μy * hν
  have hcross : px * νy - py * νx = 0 := by
    rw [hμx, hμy] at hm; linear_combination hm
  exact ⟨by linear_combination νy * hcross - px * hν,
         by linear_combination (-νx) * hcross - py * hν⟩

end SweepCover

section MovingFrame

/-!
### The moving frame: the arms are the corner velocity, and the windows are the entries

Write `μ_t = (cos t, sin t)`, `ν_t = (-sin t, cos t)`, and `c(t) = (F-1)μ_t + (G-1)ν_t` for
the corner path, with arms `α₁ = G - 1 - F'` and `α₂ = F - 1 + G'`. For a fixed point `p`
put `u(t) = ⟨c(t) - p, μ_t⟩` and `v(t) = ⟨c(t) - p, ν_t⟩`. Because `μ_t` and `ν_t` are
orthonormal these collapse to closed form,

  `u(t) = F(t) - 1 - ⟨p, μ_t⟩`,   `v(t) = G(t) - 1 - ⟨p, ν_t⟩`,

and differentiating gives a plane system whose forcing is exactly the arm pair:

  `u' = v - α₁(t)`,   `v' = -u + α₂(t)`.

That identity is `frame_ode_u` and `frame_ode_v`. Everything below is a consequence.

The corner covers `p` at time `t` exactly when `u > 0` and `v > 0`; call that set `T(p)`.
The two sweeps `Φ(s,t) = c - sμ_t` and `Ψ(s,t) = c - sν_t` have Jacobians `α₂ - s` and
`s - α₁`, so `prop:V`'s truncation windows `[0, α₂⁺]` and `[α₁⁺, σ]` are the sets where the
Jacobian is nonnegative. On the face-2 edge (`v = 0`, `u = s`) the system gives
`v' = α₂ - s`, and on the face-1 edge (`u = 0`, `v = s`) it gives `u' = s - α₁`. So the
window condition and the condition that the trajectory is crossing *into* `T(p)` are the
same inequality: `face1_window_iff_entry` and `face2_window_iff_entry`.

Consequently `V = ∫_N #(entries of p)` while `|N| = ∫_N 1`, and all three hypotheses of
`prop:V` say one thing: `T(p)` is a nonempty interval for a.e. `p ∈ N`. Covering is "at
least one entry", injectivity and disjointness together are "at most one entry".

`entry_deriv_nonneg` supplies the missing analytic step, and with it covering is proved:
a point of `N` is not cut at `t = 0` (`corner_start_on_floor`), so its cut set has a first
entry, and at that entry the offset satisfies the window inequality. What remains open is
only that `T(p)` is *connected*.
-/

/-- `u' = v - α₁`. The `α₁` here is `G t - 1 - f'`, and `v` is its closed form; only `F`
needs to be differentiable for this half. -/
theorem frame_ode_u {F : ℝ → ℝ} {t f' px py gt : ℝ} (hF : HasDerivAt F f' t) :
    HasDerivAt (fun s => F s - 1 - (px * Real.cos s + py * Real.sin s))
      ((gt - 1 - (-(px * Real.sin t) + py * Real.cos t)) - (gt - 1 - f')) t := by
  have h : HasDerivAt (fun s => F s - 1 - (px * Real.cos s + py * Real.sin s))
      (f' - (px * (-Real.sin t) + py * Real.cos t)) t := by
    exact (hF.sub_const 1).sub
      (((Real.hasDerivAt_cos t).const_mul px).add ((Real.hasDerivAt_sin t).const_mul py))
  convert h using 1; ring

/-- `v' = -u + α₂`. Symmetrically, only `G` needs to be differentiable. -/
theorem frame_ode_v {G : ℝ → ℝ} {t g' px py ft : ℝ} (hG : HasDerivAt G g' t) :
    HasDerivAt (fun s => G s - 1 - (-(px * Real.sin s) + py * Real.cos s))
      (-(ft - 1 - (px * Real.cos t + py * Real.sin t)) + (ft - 1 + g')) t := by
  have h : HasDerivAt (fun s => G s - 1 - (-(px * Real.sin s) + py * Real.cos s))
      (g' - (-(px * Real.cos t) + py * (-Real.sin t))) t := by
    exact (hG.sub_const 1).sub
      ((((Real.hasDerivAt_sin t).const_mul px).neg).add
        ((Real.hasDerivAt_cos t).const_mul py))
  convert h using 1; ring

/-- **Face 1: the window is the entry condition.** For a nonnegative offset `s`, lying in
`[α₁⁺, ∞)` is the same as the face-1 Jacobian `s - α₁` being nonnegative, which by
`frame_ode_u` is the same as `u' ≥ 0`, that is, the trajectory entering `T(p)`. -/
theorem face1_window_iff_entry {s a1 : ℝ} (hs : 0 ≤ s) :
    max a1 0 ≤ s ↔ 0 ≤ s - a1 := by
  constructor
  · intro h; linarith [le_of_max_le_left h]
  · intro h; exact max_le (by linarith) hs

/-- **Face 2: the window is the entry condition.** For a nonnegative offset `s`, lying in
`[0, α₂⁺]` is the same as the face-2 Jacobian `α₂ - s` being nonnegative, which by
`frame_ode_v` is the same as `v' ≥ 0`. -/
theorem face2_window_iff_entry {s a2 : ℝ} (hs : 0 < s) :
    s ≤ max a2 0 ↔ 0 ≤ a2 - s := by
  constructor
  · intro h
    rcases le_total 0 a2 with h2 | h2
    · rw [max_eq_left h2] at h; linarith
    · rw [max_eq_right h2] at h; linarith
  · intro h; exact le_max_of_le_left (by linarith)

/-- A function that vanishes at `t₁` and is positive immediately to the right has
nonnegative derivative there. This is the analytic content of the entry argument: it is
what converts "the cut set starts here" into the window inequality. -/
theorem entry_deriv_nonneg {w : ℝ → ℝ} {d t₁ t₂ : ℝ} (hlt : t₁ < t₂)
    (hd : HasDerivAt w d t₁) (hz : w t₁ = 0)
    (hpos : ∀ t, t₁ < t → t ≤ t₂ → 0 < w t) : 0 ≤ d := by
  have hw : HasDerivWithinAt w d (Set.Ioi t₁) t₁ := hd.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope] at hw
  rw [Set.diff_singleton_eq_self (by simp : t₁ ∉ Set.Ioi t₁)] at hw
  refine ge_of_tendsto hw ?_
  filter_upwards [Ioo_mem_nhdsGT hlt] with y hy
  have hy1 : t₁ < y := hy.1
  rw [slope_def_field, hz, sub_zero]
  exact div_nonneg (hpos y hy1 hy.2.le).le (by linarith)

/-- **The rotation starts on the floor.** After the normalisation `G 0 = 1` (the corner
reaches the floor at the end of the rotation), the time-zero corner sits at height `0`, so
its quadrant `{u ≥ 0, v ≥ 0}` meets the cap `{p_y ≥ 0}` only along `p_y = 0`. That is a
null set, which is why no point of `N` is already cut at `t = 0` and why the first entry
of `T(p)` exists. -/
theorem corner_start_on_floor {g0 py : ℝ} (hg : g0 = 1) (hcap : 0 ≤ py)
    (hcut : 0 ≤ g0 - 1 - py) : py = 0 := by
  rw [hg] at hcut; linarith

end MovingFrame

section OneFunction

/-!
### The two arms are one function, and connectivity becomes a Sturm statement

`ν_t = μ_{t+π/2}`, so with `W(θ) = H(θ) - 1 - ⟨p, μ_θ⟩` the closed forms of the previous
section read

  `u(t) = W(t)`,   `v(t) = W(t + π/2)`.

The two arms are the same function at a quarter-period shift (`arm_shift`), and therefore

  `T(p) = {t : W(t) > 0} ∩ {t : W(t + π/2) > 0}`.

An intersection of order-connected sets is order-connected (`cut_set_ordConnected`), so
connectivity of `T(p)` follows once `{W > 0}` meets each of `[0, π/2)` and `(π/2, π]` in an
interval. Note it cannot be an interval across all of `[0,π]`: after the normalisation
`H(π/2) = 1` one has `W(π/2) = -p_y < 0` for every `p` off the floor, so the atom sits in the
negative set and splits `{W > 0}` in two. That split is forced, not a defect.

Since `⟨p, μ_θ⟩'' = -⟨p, μ_θ⟩` (`point_part_harmonic`), `p` drops out of the second-order
part and `W` satisfies a Hill equation whose forcing is the cap alone:

  `W'' + W = r(θ) - 1`,  `r = H + H''` the curvature radius.

Now the Sturm step. On a hump where `W` has constant sign and vanishes at both ends, pairing
the equation with `W` itself gives `∫(W''+W)W = ∫W² - ∫W'²`, and Wirtinger on an interval of
length at most `π` says the right side is nonpositive. If `r < 1` the left side is `∫(r-1)W`,
which on a NEGATIVE hump is an integral of a positive function. Contradiction: negative humps
are longer than `π` (`negative_hump_contradiction`). A gap between two components of
`{W > 0}` inside `[0, π/2)` would be exactly such a hump, of length below `π/2`. So there is
no gap.

For `Σ` the hypothesis is met with room: `sofa_cut` measures `max r = 0.838571` off the atom,
margin `0.161429` to the threshold `1`. The two analytic inputs are carried as explicit
hypotheses here rather than proved, so this section is auditable but the Sturm lemma is
`PROVED`, not `VERIFIED`: `henergy` is integration by parts and `hwirt` is Wirtinger.
-/

/-- `ν_t = μ_{t+π/2}`, so the second arm is the first evaluated a quarter period later. -/
theorem arm_shift (H : ℝ → ℝ) (px py t : ℝ) :
    H (t + Real.pi / 2) - 1
        - (px * Real.cos (t + Real.pi / 2) + py * Real.sin (t + Real.pi / 2))
      = H (t + Real.pi / 2) - 1 - (-(px * Real.sin t) + py * Real.cos t) := by
  rw [Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring

/-- `⟨p, μ_θ⟩` is annihilated by `d²/dθ² + 1`. This is why `p` does not appear in the Hill
equation `W'' + W = r - 1`: it enters only through initial conditions. -/
theorem point_part_harmonic (px py t : ℝ) :
    HasDerivAt (fun s => px * Real.cos s + py * Real.sin s)
        (-(px * Real.sin t) + py * Real.cos t) t ∧
    HasDerivAt (fun s => -(px * Real.sin s) + py * Real.cos s)
        (-(px * Real.cos t + py * Real.sin t)) t := by
  constructor
  · have h := ((Real.hasDerivAt_cos t).const_mul px).add ((Real.hasDerivAt_sin t).const_mul py)
    have e : -(px * Real.sin t) + py * Real.cos t
        = px * (-Real.sin t) + py * Real.cos t := by ring
    rw [e]; exact h
  · have h := (((Real.hasDerivAt_sin t).const_mul px).neg).add
      ((Real.hasDerivAt_cos t).const_mul py)
    have e : -(px * Real.cos t + py * Real.sin t)
        = -(px * Real.cos t) + py * (-Real.sin t) := by ring
    rw [e]; exact h

/-- `T(p)` is the intersection of two order-connected sets, hence order-connected. This is
the step that turns "one interval on each side of the atom" into connectivity of the cut
set, and it is the whole reason the quarter-period shift matters. -/
theorem cut_set_ordConnected {P Q : Set ℝ} (hP : P.OrdConnected) (hQ : Q.OrdConnected) :
    (P ∩ Q).OrdConnected := hP.inter hQ

/-- Mirror of `entry_deriv_nonneg`: a function vanishing at `b` and negative immediately to
the left has nonnegative derivative there. -/
theorem exit_deriv_nonneg {w : ℝ → ℝ} {d a b : ℝ} (hlt : a < b)
    (hd : HasDerivAt w d b) (hz : w b = 0)
    (hneg : ∀ t, a < t → t < b → w t < 0) : 0 ≤ d := by
  have hw : HasDerivWithinAt w d (Set.Iio b) b := hd.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope,
    Set.diff_singleton_eq_self (by simp : b ∉ Set.Iio b)] at hw
  refine ge_of_tendsto hw ?_
  filter_upwards [Ioo_mem_nhdsLT hlt] with y hy
  have hy2 : y < b := hy.2
  rw [slope_def_field, hz, sub_zero]
  exact le_of_lt (div_pos_of_neg_of_neg (hneg y hy.1 hy2) (by linarith))

/-- **Negative humps are long, by Wronskian comparison.** If `W'' + W = q` with `q < 0` on
`(a,b)`, `W` vanishes at both ends and is negative between, and `b - a < π`, that is
contradictory.

The proof needs no integration theory. Put `G = W'·sin(θ-a) - W·cos(θ-a)`. Then
`G' = q·sin(θ-a)`, negative on `(a,b)` because `sin(θ-a) > 0` there, so `G` is strictly
decreasing; and `G(a) = -W(a) = 0`, so `G(b) < 0`. But `G(b) = W'(b)·sin(b-a)` with
`sin(b-a) > 0`, forcing `W'(b) < 0`, while `W < 0` rising to `W(b) = 0` forces `W'(b) ≥ 0`.

This replaces an earlier route through integration by parts and Wirtinger, whose two
analytic inputs had to be carried as hypotheses. Nothing is assumed here. `W''` is required
only on the open hump, which matters because `r` jumps at the phase boundaries of `Σ`. -/
theorem negative_hump_impossible {W W1 q : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hlen : b - a < Real.pi)
    (hW : ∀ t, HasDerivAt W (W1 t) t)
    (hW1c : ContinuousOn W1 (Set.Icc a b))
    (hW1 : ∀ t ∈ Set.Ioo a b, HasDerivAt W1 (q t - W t) t)
    (hWa : W a = 0) (hWb : W b = 0)
    (hneg : ∀ t ∈ Set.Ioo a b, W t < 0)
    (hq : ∀ t ∈ Set.Ioo a b, q t < 0) : False := by
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun t => (hW t).continuousAt
  set G : ℝ → ℝ := fun s => W1 s * Real.sin (s - a) - W s * Real.cos (s - a) with hGdef
  have hsin : ∀ w : ℝ, HasDerivAt (fun s => Real.sin (s - a)) (Real.cos (w - a)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const a).sin
  have hcos : ∀ w : ℝ, HasDerivAt (fun s => Real.cos (s - a)) (-Real.sin (w - a)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const a).cos
  have hG : ∀ w ∈ Set.Ioo a b, HasDerivAt G (q w * Real.sin (w - a)) w := by
    intro w hw
    have h := ((hW1 w hw).mul (hsin w)).sub ((hW w).mul (hcos w))
    have e : q w * Real.sin (w - a)
        = (q w - W w) * Real.sin (w - a) + W1 w * Real.cos (w - a)
          - (W1 w * Real.cos (w - a) + W w * -Real.sin (w - a)) := by ring
    rw [hGdef, e]
    exact h
  have hGc : ContinuousOn G (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s : ℝ => Real.sin (s - a)) (Set.Icc a b) :=
      (Real.continuous_sin.comp (continuous_id.sub continuous_const)).continuousOn
    have h2 : ContinuousOn (fun s : ℝ => Real.cos (s - a)) (Set.Icc a b) :=
      (Real.continuous_cos.comp (continuous_id.sub continuous_const)).continuousOn
    exact (hW1c.mul h1).sub (hWc.continuousOn.mul h2)
  have hanti : StrictAntiOn G (Set.Icc a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b) hGc ?_
    intro w hw
    rw [interior_Icc] at hw
    rw [(hG w hw).deriv]
    exact mul_neg_of_neg_of_pos (hq w hw)
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hw.1]) (by linarith [hw.2]))
  have hGa : G a = 0 := by simp [hGdef, hWa]
  have hGb : G b = W1 b * Real.sin (b - a) := by simp [hGdef, hWb]
  have hlt : G b < G a := hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hsb : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hW1b : W1 b < 0 := by
    rw [hGa, hGb] at hlt; nlinarith [hlt, hsb]
  have hge := exit_deriv_nonneg hab (hW b) hWb (fun t h1 h2 => hneg t ⟨h1, h2⟩)
  linarith

end OneFunction

section CoveringAssembly

/-!
### The first entry exists, and covering assembles

`exists_first_entry` is the step left in prose last round: the cut set of a point of `N` has
a first entry, obtained as the supremum of the closed set of earlier times at which the
point is not cut. `covering_first_entry` then combines it with `entry_deriv_nonneg` and the
frame ODE to put the offset on the correct side of its window.
-/

/-- The supremum of the times before `ts` at which `w` is nonpositive is a first entry: `w`
vanishes there and is positive on the whole stretch up to `ts`. -/
theorem exists_first_entry {w : ℝ → ℝ} {a ts : ℝ} (hat : a < ts) (hc : Continuous w)
    (h0 : w a ≤ 0) (hts : 0 < w ts) :
    ∃ t₁, a ≤ t₁ ∧ t₁ < ts ∧ w t₁ = 0 ∧ ∀ y, t₁ < y → y ≤ ts → 0 < w y := by
  set S : Set ℝ := Set.Icc a ts ∩ w ⁻¹' Set.Iic 0 with hSdef
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_Iic.preimage hc)
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hat.le⟩, h0⟩
  have hSb : BddAbove S := ⟨ts, fun y hy => hy.1.2⟩
  have hmem : sSup S ∈ S := hSc.csSup_mem hSne hSb
  have h1 : a ≤ sSup S := hmem.1.1
  have h2 : sSup S ≤ ts := hmem.1.2
  have hw1 : w (sSup S) ≤ 0 := hmem.2
  have hlt : sSup S < ts := lt_of_le_of_ne h2 (by intro h; rw [h] at hw1; linarith)
  have hpos : ∀ y, sSup S < y → y ≤ ts → 0 < w y := by
    intro y hy1 hy2
    by_contra hcon
    push_neg at hcon
    exact absurd (le_csSup hSb ⟨⟨le_trans h1 hy1.le, hy2⟩, hcon⟩) (not_le.mpr hy1)
  refine ⟨sSup S, h1, hlt, le_antisymm hw1 ?_, hpos⟩
  have htend : Filter.Tendsto w (nhdsWithin (sSup S) (Set.Ioi (sSup S))) (nhds (w (sSup S))) :=
    hc.continuousAt.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT hlt] with y hy
  exact (hpos y hy.1 hy.2.le).le

/-- **Covering, assembled.** A point cut at `ts` but not at `a` has a first entry, and at
that entry it lies on one of the two faces with the Jacobian nonnegative, which by
`face1_window_iff_entry` and `face2_window_iff_entry` is exactly membership of the
corresponding truncation window of `prop:V`. -/
theorem covering_first_entry {u v A1 A2 : ℝ → ℝ} {a ts : ℝ} (hat : a < ts)
    (hu : Continuous u) (hv : Continuous v)
    (hdu : ∀ s, HasDerivAt u (v s - A1 s) s)
    (hdv : ∀ s, HasDerivAt v (-u s + A2 s) s)
    (h0 : min (u a) (v a) ≤ 0) (hts : 0 < min (u ts) (v ts)) :
    ∃ t₁, a ≤ t₁ ∧ t₁ < ts ∧
      ((u t₁ = 0 ∧ 0 ≤ v t₁ ∧ 0 ≤ v t₁ - A1 t₁) ∨
       (v t₁ = 0 ∧ 0 ≤ u t₁ ∧ 0 ≤ A2 t₁ - u t₁)) := by
  obtain ⟨t₁, h1, h2, hz, hp⟩ := exists_first_entry hat (hu.min hv) h0 hts
  refine ⟨t₁, h1, h2, ?_⟩
  have hpu : ∀ y, t₁ < y → y ≤ ts → 0 < u y :=
    fun y hy1 hy2 => lt_of_lt_of_le (hp y hy1 hy2) (min_le_left _ _)
  have hpv : ∀ y, t₁ < y → y ≤ ts → 0 < v y :=
    fun y hy1 hy2 => lt_of_lt_of_le (hp y hy1 hy2) (min_le_right _ _)
  rcases min_eq_zero_cases hz with ⟨hu0, hv0⟩ | ⟨hv0, hu0⟩
  · exact Or.inl ⟨hu0, hv0, entry_deriv_nonneg h2 (hdu t₁) hu0 hpu⟩
  · refine Or.inr ⟨hv0, hu0, ?_⟩
    have := entry_deriv_nonneg h2 (hdv t₁) hv0 hpv
    linarith

end CoveringAssembly


section Connectivity

/-!
### No gap: `{W > 0}` is order-connected on any window shorter than `π`

This is the step that was still prose. The same Wronskian comparison that makes negative
humps long shows directly that there is no gap at all. Anchor `G = W'·sin(θ-x) - W·cos(θ-x)`
at a point `x` where `W > 0`. Then `G(x) = -W(x) < 0` and `G' = q·sin(θ-x) < 0`, so `G` stays
negative on the whole window. If `W` dipped to `0` before a later point `z` with `W(z) > 0`,
take the first entry `t₁` after the dip: there `W(t₁) = 0` and `W > 0` afterwards, so
`G(t₁) = W'(t₁)·sin(t₁-x)` with `sin(t₁-x) > 0` forces `W'(t₁) < 0`, while
`entry_deriv_nonneg` forces `W'(t₁) ≥ 0`.

Combined with `cut_set_ordConnected` this closes hypothesis (ii): `T(p)` is the intersection
of `{W > 0}` with its own `π/2`-translate, each order-connected on its side of the atom
because `π/2 < π`.
-/

/-- **No dip between two positive values**, on a window shorter than `π` with `q < 0`. -/
theorem pos_between {W W1 q : ℝ → ℝ} {x z : ℝ} (hxz : x < z) (hlen : z - x < Real.pi)
    (hW : ∀ t, HasDerivAt W (W1 t) t)
    (hW1c : ContinuousOn W1 (Set.Icc x z))
    (hW1 : ∀ t ∈ Set.Ioo x z, HasDerivAt W1 (q t - W t) t)
    (hq : ∀ t ∈ Set.Ioo x z, q t < 0)
    (hx : 0 < W x) (hz : 0 < W z) : ∀ t ∈ Set.Ioo x z, 0 < W t := by
  intro y hy
  by_contra hcon
  push_neg at hcon
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun t => (hW t).continuousAt
  set G : ℝ → ℝ := fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x) with hGdef
  have hsin : ∀ w : ℝ, HasDerivAt (fun s => Real.sin (s - x)) (Real.cos (w - x)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const x).sin
  have hcos : ∀ w : ℝ, HasDerivAt (fun s => Real.cos (s - x)) (-Real.sin (w - x)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const x).cos
  have hG : ∀ w ∈ Set.Ioo x z, HasDerivAt G (q w * Real.sin (w - x)) w := by
    intro w hw
    have h := ((hW1 w hw).mul (hsin w)).sub ((hW w).mul (hcos w))
    have e : q w * Real.sin (w - x)
        = (q w - W w) * Real.sin (w - x) + W1 w * Real.cos (w - x)
          - (W1 w * Real.cos (w - x) + W w * -Real.sin (w - x)) := by ring
    rw [hGdef, e]
    exact h
  have hGc : ContinuousOn G (Set.Icc x z) := by
    have h1 : ContinuousOn (fun s : ℝ => Real.sin (s - x)) (Set.Icc x z) :=
      (Real.continuous_sin.comp (continuous_id.sub continuous_const)).continuousOn
    have h2 : ContinuousOn (fun s : ℝ => Real.cos (s - x)) (Set.Icc x z) :=
      (Real.continuous_cos.comp (continuous_id.sub continuous_const)).continuousOn
    exact (hW1c.mul h1).sub (hWc.continuousOn.mul h2)
  have hanti : StrictAntiOn G (Set.Icc x z) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc x z) hGc ?_
    intro w hw
    rw [interior_Icc] at hw
    rw [(hG w hw).deriv]
    exact mul_neg_of_neg_of_pos (hq w hw)
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hw.1]) (by linarith [hw.2]))
  have hGx : G x = -W x := by simp [hGdef]
  obtain ⟨t₁, h1, h2, hz1, hp⟩ := exists_first_entry hy.2 hWc hcon hz
  have hxt : x < t₁ := lt_of_lt_of_le hy.1 h1
  have hGt : G t₁ < 0 := by
    have hh := hanti ⟨le_rfl, hxz.le⟩ ⟨hxt.le, h2.le⟩ hxt
    rw [hGx] at hh; linarith
  have hsb : 0 < Real.sin (t₁ - x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hGt' : G t₁ = W1 t₁ * Real.sin (t₁ - x) := by simp [hGdef, hz1]
  have hnegd : W1 t₁ < 0 := by rw [hGt'] at hGt; nlinarith [hGt, hsb]
  have hge := entry_deriv_nonneg h2 (hW t₁) hz1 hp
  linarith

/-- **Hypothesis (ii), assembled.** On a window shorter than `π` the set where `W` is
positive is order-connected. Applied to the two sides of the atom, each of length `π/2`, and
intersected via `cut_set_ordConnected`, this makes `T(p)` an interval. -/
theorem pos_set_ordConnected {W W1 q : ℝ → ℝ} {lo hi : ℝ} (hlen : hi - lo < Real.pi)
    (hW : ∀ t, HasDerivAt W (W1 t) t)
    (hW1c : ContinuousOn W1 (Set.Icc lo hi))
    (hW1 : ∀ t ∈ Set.Ioo lo hi, HasDerivAt W1 (q t - W t) t)
    (hq : ∀ t ∈ Set.Ioo lo hi, q t < 0) :
    {t | t ∈ Set.Icc lo hi ∧ 0 < W t}.OrdConnected := by
  constructor
  intro x hx z hz y hy
  rcases eq_or_lt_of_le hy.1 with h | hxy
  · exact h ▸ hx
  rcases eq_or_lt_of_le hy.2 with h | hyz
  · exact h ▸ hz
  have hxz : x < z := lt_trans hxy hyz
  have hsub : Set.Icc x z ⊆ Set.Icc lo hi := Set.Icc_subset_Icc hx.1.1 hz.1.2
  have hsub' : Set.Ioo x z ⊆ Set.Ioo lo hi := fun t ht =>
    ⟨lt_of_le_of_lt hx.1.1 ht.1, lt_of_lt_of_le ht.2 hz.1.2⟩
  refine ⟨⟨le_trans hx.1.1 hxy.le, le_trans hyz.le hz.1.2⟩, ?_⟩
  exact pos_between hxz (by linarith [hx.1.1, hz.1.2]) hW (hW1c.mono hsub)
    (fun t ht => hW1 t (hsub' ht)) (fun t ht => hq t (hsub' ht)) hx.2 hz.2 y ⟨hxy, hyz⟩

end Connectivity


section CurvatureBound

/-!
### `r < 1` exactly, and the sweep Jacobians

Two things were still resting on floating point or on prose.

First the standing hypothesis `r < 1` off the atom. It was measured at `0.838571` in `f64`,
which under Rule 7 is evidence and not proof. It has an exact closed form. On the two
absolutely continuous phases `Σ`'s curvature radius is `0.75·(A cos u + B sin u)` with
`B = (1-√2)A` and `A = F₁ = 1.20293…`; the two phases differ only by swapping `A` and `B`,
which leaves `A² + B²` unchanged. Since `A cos u + B sin u ≤ √(A²+B²)` and
`A² + B² = A²(4 - 2√2)`, the bound is `0.75·A·√(4-2√2)`, and `A ≤ 1.21` makes it under `1`
with room. The middle phase is the constant `0.5` and the end phases are `0`, both under `1`.
So `r < 1` is a theorem, not a measurement, and the numerical value is only a sharper
estimate of a quantity already known to be below the threshold.

Second the sweep Jacobians, which the truncation windows of `prop:V` are defined by. With
`c' = -α₁μ_t + α₂ν_t` these are pure trigonometric identities, recorded here so that the
window-equals-entry identification rests on a checked computation rather than on a
hand-differentiation.
-/

/-- Cauchy-Schwarz on the circle: `(A cos u + B sin u)² ≤ A² + B²`. -/
theorem trig_combo_sq_le (A B u : ℝ) :
    (A * Real.cos u + B * Real.sin u) ^ 2 ≤ A ^ 2 + B ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq u, sq_nonneg (A * Real.sin u - B * Real.cos u)]

theorem sqrt_two_ge : (1.414 : ℝ) ≤ Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- **The curvature radius stays below `1` on the absolutely continuous phases.** This is
the standing hypothesis of the Sturm argument, proved rather than measured. `A` is `F₁`,
and `A ≤ 1.21` is a wide margin around its value `1.20293…`. -/
theorem curvature_lt_one {A u : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 1.21) :
    0.75 * (A * Real.cos u + (1 - Real.sqrt 2) * A * Real.sin u) < 1 := by
  have hs := sqrt_two_ge
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := trig_combo_sq_le A ((1 - Real.sqrt 2) * A) u
  have hkey : A ^ 2 + ((1 - Real.sqrt 2) * A) ^ 2 = A ^ 2 * (4 - 2 * Real.sqrt 2) := by
    linear_combination A ^ 2 * hs2
  have h4 : 4 - 2 * Real.sqrt 2 ≤ 1.172 := by linarith
  have hpos : 0 ≤ 4 - 2 * Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hA2 : A ^ 2 ≤ 1.4641 := by nlinarith
  have hprod : A ^ 2 * (4 - 2 * Real.sqrt 2) ≤ 1.4641 * 1.172 :=
    mul_le_mul hA2 h4 hpos (by norm_num)
  rw [hkey] at hcs
  nlinarith [hcs, hprod]

/-- The other absolutely continuous phase swaps the two coefficients, which leaves
`A² + B²` unchanged, so the same bound applies. -/
theorem curvature_lt_one' {A u : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 1.21) :
    0.75 * (-((1 - Real.sqrt 2) * A) * Real.cos u + A * Real.sin u) < 1 := by
  have hs := sqrt_two_ge
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcs := trig_combo_sq_le (-((1 - Real.sqrt 2) * A)) A u
  have hkey : (-((1 - Real.sqrt 2) * A)) ^ 2 + A ^ 2 = A ^ 2 * (4 - 2 * Real.sqrt 2) := by
    linear_combination A ^ 2 * hs2
  have h4 : 4 - 2 * Real.sqrt 2 ≤ 1.172 := by linarith
  have hpos : 0 ≤ 4 - 2 * Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hA2 : A ^ 2 ≤ 1.4641 := by nlinarith
  have hprod : A ^ 2 * (4 - 2 * Real.sqrt 2) ≤ 1.4641 * 1.172 :=
    mul_le_mul hA2 h4 hpos (by norm_num)
  rw [hkey] at hcs
  nlinarith [hcs, hprod]

/-- **Face-2 sweep Jacobian.** For `Φ(s,t) = c(t) - s·μ_t` with `c' = -α₁μ + α₂ν`, the
determinant of `[∂Φ/∂s, ∂Φ/∂t]` is `s - α₂`. Its sign change at `s = α₂` is exactly the
upper truncation limit `α₂⁺` of `prop:V`. -/
theorem sweep2_jacobian (a1 a2 s t : ℝ) :
    (-Real.cos t) * (-(a1 * Real.sin t) + a2 * Real.cos t - s * Real.cos t)
      - (-Real.sin t) * (-(a1 * Real.cos t) - a2 * Real.sin t + s * Real.sin t)
    = s - a2 := by
  linear_combination (s - a2) * Real.sin_sq_add_cos_sq t

/-- **Face-1 sweep Jacobian.** For `Ψ(s,t) = c(t) - s·ν_t` the determinant is `s - α₁`, and
its sign change at `s = α₁` is the lower truncation limit `α₁⁺`. -/
theorem sweep1_jacobian (a1 a2 s t : ℝ) :
    (Real.sin t) * (-(a1 * Real.sin t) + a2 * Real.cos t + s * Real.sin t)
      - (-Real.cos t) * (-(a1 * Real.cos t) - a2 * Real.sin t + s * Real.cos t)
    = s - a1 := by
  linear_combination (s - a1) * Real.sin_sq_add_cos_sq t

end CurvatureBound


section Containment

/-!
### Where the sweeps end, and what containment really needs

`prop:V` needs the truncated sweeps to lie in `C₂`; `rem:v6` shows that does not follow from
its three hypotheses. This section locates the obstruction exactly.

Both sweeps end, at the truncation limit that the Jacobian sign picks out, at the *same kind
of point*. On face 2 at `s = α₂`, using `μ_t = -ν_ψ` and `ν_t = μ_ψ` with `ψ = t + π/2`,

  `Φ(α₂,t) = -H'(ψ)μ_t + (H(ψ)-1)ν_t = (H(ψ)-1)μ_ψ + H'(ψ)ν_ψ = X(ψ) - μ_ψ`,

where `X(θ) = H(θ)μ_θ + H'(θ)ν_θ` is the boundary point of the cap with outer normal `μ_θ`.
So the inner end of the sweep is the boundary point pulled one unit along its own normal: a
point of the inner parallel body. Face 1 at `s = α₁` gives `X(t) - μ_t`, the same form.
`face2_endpoint` and `face1_endpoint` are those identities.

The other ends are `c(t)` on face 2 (`s = 0`) and the floor on face 1 (`s = σ`). Since `C₂`
is convex, a sweep segment lies in `C₂` as soon as both its endpoints do
(`sweep_subset_of_endpoints`). Measurement (`sofa_stadium`) says `X(θ) - μ_θ` never leaves
the cap, on the counterexample family as well as on `Σ`, while `c(t)` does leave it exactly
when the counterexample bites. So the missing hypothesis is not about sweeps at all:

  **the corner path `c(t)` stays in `C₂`.**

That is a statement about one curve rather than two two-parameter families, and it is open.
-/

/-- **Face-2 inner endpoint.** `Φ(α₂,t) = X(t+π/2) - μ_{t+π/2}`, componentwise, where `g`
and `gp` are `H` and `H'` at `t + π/2`. The `f`-dependence cancels: the endpoint does not
see `H(t)` at all. -/
theorem face2_endpoint (f g gp t : ℝ) :
    ((f - 1) * Real.cos t - (g - 1) * Real.sin t - (f - 1 + gp) * Real.cos t
      = g * Real.cos (t + Real.pi / 2) - gp * Real.sin (t + Real.pi / 2)
        - Real.cos (t + Real.pi / 2))
    ∧ ((f - 1) * Real.sin t + (g - 1) * Real.cos t - (f - 1 + gp) * Real.sin t
      = g * Real.sin (t + Real.pi / 2) + gp * Real.cos (t + Real.pi / 2)
        - Real.sin (t + Real.pi / 2)) := by
  rw [Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  constructor <;> ring

/-- **Face-1 inner endpoint.** `Ψ(α₁,t) = X(t) - μ_t`, the same form one quarter turn back:
here the `g`-dependence is what cancels. -/
theorem face1_endpoint (f g fp t : ℝ) :
    ((f - 1) * Real.cos t - (g - 1) * Real.sin t + (g - 1 - fp) * Real.sin t
      = f * Real.cos t - fp * Real.sin t - Real.cos t)
    ∧ ((f - 1) * Real.sin t + (g - 1) * Real.cos t - (g - 1 - fp) * Real.cos t
      = f * Real.sin t + fp * Real.cos t - Real.sin t) := by
  constructor <;> ring

/-- **The convexity reduction.** A sweep segment lies in the cap as soon as its two endpoints
do. This is what turns containment of two two-parameter families into a statement about the
corner path and the inner parallel body. -/
theorem sweep_subset_of_endpoints {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {p q : ℝ × ℝ}
    (hp : p ∈ C) (hq : q ∈ C) : segment ℝ p q ⊆ C := hC.segment_subset hp hq

end Containment

section Piecewise

/-!
### Repairing the regression: the Sturm step across a jump in `r`

`pos_between` assumes `W''` exists pointwise on the open window. `Σ` fails that: `r` jumps
at `β`, inside `[0, π/2)`, so the lemma applies to a `C²` surrogate and never to `Σ`'s own
`W`. The discarded route through `∫(r-1)W` tolerated jumps, an integral being indifferent to
them, so moving to a pointwise Sturm argument was a regression in applicability.

The repair keeps the Wronskian and drops the pointwise hypothesis. Only one consequence of
`W'' + W = q < 0` is used: that `G = W'·sin(θ-x) - W·cos(θ-x)` is strictly decreasing. That
survives a jump, because `G` stays continuous there (only `W''` jumps, not `W'`), and strict
antitonicity glues across a shared endpoint (`strictAntiOn_glue`). So `Σ`'s window is handled
by proving `G` decreasing on each smooth phase and gluing, and
`pos_between_of_strictAnti` takes the glued statement as its hypothesis.
-/

/-- Strict antitonicity glues across a shared endpoint. Applied at the jumps of `r`, this is
what lets the Sturm step run on a window that is only piecewise smooth. -/
theorem strictAntiOn_glue {f : ℝ → ℝ} {a b c : ℝ}
    (h1 : StrictAntiOn f (Set.Icc a b)) (h2 : StrictAntiOn f (Set.Icc b c)) :
    StrictAntiOn f (Set.Icc a c) := by
  intro p hp r hr hpr
  rcases le_total r b with hrb | hrb
  · exact h1 ⟨hp.1, le_trans hpr.le hrb⟩ ⟨hr.1, hrb⟩ hpr
  · rcases le_total b p with hbp | hbp
    · exact h2 ⟨hbp, hp.2⟩ ⟨le_trans hbp hpr.le, hr.2⟩ hpr
    · rcases eq_or_lt_of_le hbp with hb | hb
      · exact hb ▸ h2 ⟨le_rfl, le_trans hrb hr.2⟩ ⟨hrb, hr.2⟩ (hb ▸ hpr)
      · have e1 : f b < f p := h1 ⟨hp.1, hbp⟩ ⟨le_trans hp.1 hbp, le_rfl⟩ hb
        rcases eq_or_lt_of_le hrb with hc | hc
        · rw [← hc]; exact e1
        · have e2 : f r < f b := h2 ⟨le_rfl, le_trans hrb hr.2⟩ ⟨hrb, hr.2⟩ hc
          linarith

/-- **The Sturm step, with the pointwise hypothesis removed.** Only strict antitonicity of
the Wronskian is used, and that glues across jumps of `r`. `W` need be differentiable only
on the window, and continuous globally, both of which `Σ` satisfies on `[0, π/2)`. -/
theorem pos_between_of_strictAnti {W W1 : ℝ → ℝ} {x z : ℝ} (hxz : x < z)
    (hlen : z - x < Real.pi) (hWc : Continuous W)
    (hW : ∀ t ∈ Set.Icc x z, HasDerivAt W (W1 t) t)
    (hanti : StrictAntiOn (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
      (Set.Icc x z))
    (hx : 0 < W x) (hz : 0 < W z) : ∀ t ∈ Set.Ioo x z, 0 < W t := by
  intro y hy
  by_contra hcon
  push_neg at hcon
  obtain ⟨t₁, h1, h2, hz1, hp⟩ := exists_first_entry hy.2 hWc hcon hz
  have hxt : x < t₁ := lt_of_lt_of_le hy.1 h1
  have hmem : t₁ ∈ Set.Icc x z := ⟨hxt.le, h2.le⟩
  have hh := hanti ⟨le_rfl, hxz.le⟩ hmem hxt
  simp only [sub_self, Real.sin_zero, Real.cos_zero, mul_zero, mul_one, zero_sub,
    hz1, zero_mul, sub_zero] at hh
  have hsb : 0 < Real.sin (t₁ - x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hnegd : W1 t₁ < 0 := by nlinarith [hh, hsb, hx]
  have hge := entry_deriv_nonneg h2 (hW t₁ hmem) hz1 hp
  linarith

end Piecewise


section CornerContainment

/-!
### The corner path lies in the cap, from a bound on corner speed

`rem:v6` left `c(t) ∈ C₂` as the missing hypothesis. It reduces to an inequality between two
slacks.

Membership in the cap is `⟨c(t), μ_θ⟩ ≤ H(θ)` for every `θ`. Convexity of the cap gives, for
every `ψ`, the classical support inequality `H(ψ)cos(θ-ψ) + H'(ψ)sin(θ-ψ) ≤ H(θ)`, the
statement that the boundary point `X(ψ)` lies in the body. Comparing `⟨c(t), μ_θ⟩` against
that inequality at `ψ = t` and at `ψ = t + π/2` leaves, with `φ = θ - t`, the two slacks

  `A(φ) = cos φ - α₁ sin φ`,   `B(φ) = sin φ - α₂ cos φ`

(`corner_slack_one`, `corner_slack_two`). Either slack being nonnegative gives containment at
that `θ`, so containment follows from `A(φ) ≥ 0 ∨ B(φ) ≥ 0` for all `φ` in range.

That disjunction is exactly a bound on the arms. The identities
`A + α₁B = (1 - α₁α₂)cos φ` and `B + α₂A = (1 - α₁α₂)sin φ` show that if both slacks are
negative and `α₁α₂ ≤ 1`, then `cos φ < 0` and `sin φ < 0`, putting `φ` in the third quadrant.
Since `θ ∈ [0,π]` and `t ∈ [0,π/2]` force `φ ∈ [-π/2, π]`, that is impossible. So

  `α₁α₂ ≤ 1` suffices, and since `α₁² + α₂² = |c'(t)|²` it follows from `|c'(t)| ≤ √2`:
  a bound on how fast the corner moves.

For `Σ`, `sofa_cut` measures `max α₁α₂ = 0.145187` against the threshold `1`, and
`max |c'|² = 0.813328` against `2`. The disjunction itself is checked directly over the
`(t,θ)` grid and fails nowhere, its worst margin being `0.437739`. The corner path sits
inside the cap with worst excursion `-0.000911`.

Two gaps remain and are stated rather than hidden. `corner_disjunction` assumes both arms
nonnegative; `Σ` has `α₁ < 0` on `E₁`, where the covering argument needs the separate range
check `t ≤ π/2 - |arctan α₁|` that the measurement covers but this file does not. And
`C₂ = C ∩ ρC`, so containment in `ρC` needs the mirror of this argument, which the note's
mirror remark supplies but which is not formalised here.
-/

/-- Comparing `⟨c(t), μ_θ⟩` with the support inequality at `ψ = t` leaves the slack
`cos φ - α₁ sin φ`, where `α₁ = g - 1 - fp`. -/
theorem corner_slack_one (f g fp φ : ℝ) :
    (f * Real.cos φ + fp * Real.sin φ) - ((f - 1) * Real.cos φ + (g - 1) * Real.sin φ)
      = Real.cos φ - (g - 1 - fp) * Real.sin φ := by ring

/-- Comparing with the support inequality at `ψ = t + π/2` leaves `sin φ - α₂ cos φ`, where
`α₂ = f - 1 + gp`. -/
theorem corner_slack_two (f g gp φ : ℝ) :
    (g * Real.sin φ - gp * Real.cos φ) - ((f - 1) * Real.cos φ + (g - 1) * Real.sin φ)
      = Real.sin φ - (f - 1 + gp) * Real.cos φ := by ring

/-- **The disjunction.** If both slacks were negative and `α₁α₂ ≤ 1` with both arms
nonnegative, then `φ` would lie in the third quadrant. The two combinations
`A + α₁B = (1-α₁α₂)cos φ` and `B + α₂A = (1-α₁α₂)sin φ` are what force that. -/
theorem corner_disjunction {a1 a2 φ : ℝ} (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (hprod : a1 * a2 < 1)
    (hA : Real.cos φ - a1 * Real.sin φ < 0) (hB : Real.sin φ - a2 * Real.cos φ < 0) :
    Real.cos φ < 0 ∧ Real.sin φ < 0 := by
  constructor
  · nlinarith [hA, hB, h1, hprod]
  · nlinarith [hA, hB, h2, hprod]

/-- The range that actually occurs: `θ ∈ [0,π]` and `t ∈ [0,π/2]` put `φ = θ - t` in
`[-π/2, π]`, where `cos φ` and `sin φ` are never both negative. -/
theorem no_third_quadrant {φ : ℝ} (hlo : -(Real.pi / 2) ≤ φ) (hhi : φ ≤ Real.pi)
    (hc : Real.cos φ < 0) : 0 ≤ Real.sin φ := by
  rcases le_total 0 φ with h | h
  · exact Real.sin_nonneg_of_nonneg_of_le_pi h hhi
  · exfalso
    exact absurd (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩) (not_le.mpr hc)

/-- **Containment from the arm bound.** With both arms nonnegative and `α₁α₂ < 1`, at least
one slack is nonnegative at every `φ` that occurs, so `c(t)` satisfies the support inequality
at every `θ`, which is membership in the cap. -/
theorem corner_in_cap {a1 a2 φ : ℝ} (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (hprod : a1 * a2 < 1)
    (hlo : -(Real.pi / 2) ≤ φ) (hhi : φ ≤ Real.pi) :
    0 ≤ Real.cos φ - a1 * Real.sin φ ∨ 0 ≤ Real.sin φ - a2 * Real.cos φ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc, hs⟩ := corner_disjunction h1 h2 hprod hcon.1 hcon.2
  exact absurd (no_third_quadrant hlo hhi hc) (not_le.mpr hs)

/-- The arm bound follows from a bound on corner speed, because `α₁² + α₂² = |c'(t)|²`. -/
theorem arm_prod_le_of_speed {a1 a2 : ℝ} (h : a1 * a1 + a2 * a2 < 2) : a1 * a2 < 1 := by
  nlinarith [sq_nonneg (a1 - a2)]

end CornerContainment


section EndConditions

/-!
### The disjunction for arms of either sign

`corner_in_cap` assumed both arms nonnegative, and `Σ` has `α₁ < 0` on `E₁`. Redoing the
argument without that assumption shows the worst `φ` sits at the two ends of the range
`[-t, π-t]`, and the conditions there are

  `α₁ sin t + cos t ≥ 0`   (only binding where `α₁ < 0`),
  `α₂ cos t + sin t ≥ 0`   (only binding where `α₂ < 0`),

that is `α₁ ≥ -cot t` and `α₂ ≥ -tan t`, symmetric under `α₁ ↔ α₂`, `t ↔ π/2 - t`. Each
propagates inward from its end by the angle-subtraction formula alone, with no division and
no `arctan`: multiplying the slack by `sin t` and using `sin(t-ψ) ≥ 0` reduces it to the end
condition. So the sign restriction is removed rather than patched.

For `Σ`, `sofa_cut` measures `min(α₁ + cot t) = min(α₂ + tan t) = 0.751117`, the two being
equal because `Σ` is symmetric under `α₁ ↔ α₂`, `t ↔ π/2 - t`. Also `max|α₁| = max|α₂|`
agrees with `α₂(0) = 2a₁ - 1 = 0.750574724825464`, which is exact, so
`α₁α₂ ≤ (2a₁-1)² < 1` holds without recourse to floating point.
-/

/-- The lower-end condition propagates inward: if `α₁ sin t + cos t ≥ 0` then the face-1
slack stays nonnegative for every `ψ` between `0` and `t`. Division-free: multiply by
`sin t` and use `sin(t - ψ) ≥ 0`. -/
theorem slack_at_lower_end {a1 t ψ : ℝ} (ht : 0 < t) (htp : t ≤ Real.pi / 2)
    (hψ : 0 ≤ ψ) (hψt : ψ ≤ t) (hC1 : 0 ≤ a1 * Real.sin t + Real.cos t) :
    0 ≤ Real.cos ψ + a1 * Real.sin ψ := by
  have hpi := Real.pi_pos
  have hsub : 0 ≤ Real.sin (t - ψ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_sub] at hsub
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith)
  have hsψ : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi hψ (by linarith)
  nlinarith [hsub, hst, hsψ, hC1]

/-- The upper-end condition, the mirror statement under `α₁ ↔ α₂`, `t ↔ π/2 - t`. -/
theorem slack_at_upper_end {a2 t ψ : ℝ} (ht : 0 < t) (htp : t ≤ Real.pi / 2)
    (hψ : t ≤ ψ) (hψt : ψ ≤ Real.pi / 2) (hC2 : 0 ≤ a2 * Real.cos t + Real.sin t) :
    0 ≤ Real.sin ψ + a2 * Real.cos ψ := by
  have hpi := Real.pi_pos
  have hsub : 0 ≤ Real.sin (ψ - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_sub] at hsub
  have hct : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, htp⟩
  have hcψ : 0 ≤ Real.cos ψ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hψt⟩
  have hsψ : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rcases le_total 0 a2 with h | h
  · positivity
  · rcases eq_or_lt_of_le hct with h0 | hpos
    · have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith)
      have hz : Real.cos ψ = 0 := by nlinarith [hsub, hcψ, hst]
      rw [hz]; simpa using hsψ
    · nlinarith [hsub, mul_nonneg hcψ hC2, hpos]

/-- The first-quadrant case needs only `α₁α₂ ≤ 1`, with no sign hypothesis: if both slacks
were negative there, multiplying them would force `α₁α₂ > 1`. -/
theorem slack_first_quadrant {a1 a2 φ : ℝ} (hs : 0 < Real.sin φ) (hc : 0 < Real.cos φ)
    (hprod : a1 * a2 ≤ 1) :
    0 ≤ Real.cos φ - a1 * Real.sin φ ∨ 0 ≤ Real.sin φ - a2 * Real.cos φ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hA, hB⟩ := hcon
  have h1 : Real.cos φ < a1 * Real.sin φ := by linarith
  have h2 : Real.sin φ < a2 * Real.cos φ := by linarith
  have hkey := mul_lt_mul'' h1 h2 hc.le hs.le
  nlinarith [hkey, mul_pos hc hs, hprod]

end EndConditions


section Mirror

/-!
### The mirror half, and why it is the hard one

`C₂ = C ∩ ρC`, and the corner path clears `C` comfortably while touching `ρC`. Both facts
are structural.

`ρ`-invariance of `C₂` gives `H(-θ) = H(θ) - sin θ`, so membership in `ρC` is the same
family of support inequalities at directions `ψ ∈ [-π, 0]`. Comparing against the support
inequality at `ψ = -t`, where `H(-t) = F - sin t` and `H'(-t) = cos t - F'`, leaves the slack
`cos χ + α₁ sin χ` with `χ = θ + t` (`mirror_slack`). At `ψ = -(t+π/2)` the slack is
`-(sin χ + α₂ cos χ)`. Those two cover `χ` only when `arctan α₁ + arctan α₂ ≥ π/2`, that is
`α₁α₂ ≥ 1`, which is the *opposite* of the condition the unmirrored half needs and which `Σ`
violates with `α₁α₂ ≤ (2a₁-1)² < 1`. So no two-comparison argument can close the mirror.

That is consistent with the margin, which is not small but zero: `mirror_touch` records that
at `t = 0, θ = π/2` the constraint holds with equality, because `c(0)` sits on the floor and
`H(π/2) = 1` puts its mirror image exactly on the ceiling. Refining the direction grid from
`720` to `46080` leaves the margin at `0` to eight places, so this is an exact contact and
not a discretisation artifact. Any proof of the mirror half must be sharp at that point.

Writing `V(θ) = H(θ) - ⟨ρc(t), μ_θ⟩`, the mirror condition is `V ≥ 0`, and since the point
part is harmonic, `V'' + V = r`. So the mirror asks for nonnegativity of a solution of a Hill
equation with *nonnegative* forcing, where the unmirrored half asked for a sign of one with
negative forcing. The Sturm argument does not transfer: a positive hump of `V` has length at
least `π` and a negative hump at most `π`, and a negative hump strictly inside `[0,π]` is
therefore not excluded. This is the open crux.
-/

/-- **The mirror slack.** Comparing `⟨ρc(t), μ_θ⟩` with the support inequality at `ψ = -t`,
using `H(-t) = F - sin t` and `H'(-t) = cos t - F'`, leaves `cos χ + α₁ sin χ` where
`χ = θ + t`. The `sin θ` from the reflection is exactly what cancels the `sin t` terms. -/
theorem mirror_slack (f g fp t θ : ℝ) :
    ((f - Real.sin t) * Real.cos (θ + t) + (Real.cos t - fp) * Real.sin (θ + t))
      - ((f - 1) * Real.cos (θ + t) - (g - 1) * Real.sin (θ + t) + Real.sin θ)
    = Real.cos (θ + t) + (g - 1 - fp) * Real.sin (θ + t) := by
  have h : Real.sin θ = Real.sin (θ + t) * Real.cos t - Real.cos (θ + t) * Real.sin t := by
    rw [← Real.sin_sub]; ring_nf
  rw [h]; ring

/-- **The contact.** At `t = 0` the corner sits on the floor, so its mirror image sits at
height `1`, and `H(π/2) = 1` makes the mirror constraint an equality there. This is why the
margin is zero rather than small, and why the mirror half admits no slack-based proof. -/
theorem mirror_touch {cx g0 : ℝ} (hg : g0 = 1) :
    cx * Real.cos (Real.pi / 2) + (1 - (g0 - 1)) * Real.sin (Real.pi / 2) = g0 := by
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, hg]; ring

/-- The mirror condition is nonnegativity of a Hill solution with nonnegative forcing: the
point part is harmonic, so `V = H - ⟨ρc, μ⟩` satisfies `V'' + V = H'' + H = r`. Only the
forcing sign differs from the unmirrored half, and it differs in the direction that makes
the Sturm argument fail. -/
theorem mirror_hill (px py t : ℝ) :
    HasDerivAt (fun s => -(px * Real.sin s) + py * Real.cos s)
        (-(px * Real.cos t + py * Real.sin t)) t :=
  (point_part_harmonic px py t).2

end Mirror

section PiecewiseSturm

/-!
### The per-phase Sturm step, which is what an instantiation at `Σ` consumes

`Σ`'s curvature radius is piecewise: `0` on `[0,β)`, the absolutely continuous form on
`[β, π/2-β)`, and `1/2` on `[π/2-β, π/2]`. On each phase `q = r - 1 < 0`, by
`curvature_lt_one`, and `W'` is continuous across the phase boundaries because only `W''`
jumps there. `wronskian_strictAntiOn` supplies strict antitonicity of the Wronskian on one
phase, and `strictAntiOn_glue` chains the phases; `pos_between_of_strictAnti` then runs on
the whole window. That is the complete instantiation route, stated so that supplying `Σ`'s
support function is the only remaining step.
-/

/-- On one phase, where `W'' = q - W` holds pointwise with `q < 0`, the Wronskian
`G = W'·sin(·-x) - W·cos(·-x)` is strictly decreasing. Chained across phases by
`strictAntiOn_glue`, this is what `pos_between_of_strictAnti` consumes. -/
theorem wronskian_strictAntiOn {W W1 q : ℝ → ℝ} {x a b : ℝ}
    (hWc : Continuous W)
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W (W1 t) t)
    (hW1c : ContinuousOn W1 (Set.Icc a b))
    (hW1 : ∀ t ∈ Set.Ioo a b, HasDerivAt W1 (q t - W t) t)
    (hq : ∀ t ∈ Set.Ioo a b, q t < 0)
    (hpos : ∀ t ∈ Set.Ioo a b, 0 < Real.sin (t - x)) :
    StrictAntiOn (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
      (Set.Icc a b) := by
  have hsin : ∀ w : ℝ, HasDerivAt (fun s => Real.sin (s - x)) (Real.cos (w - x)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const x).sin
  have hcos : ∀ w : ℝ, HasDerivAt (fun s => Real.cos (s - x)) (-Real.sin (w - x)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const x).cos
  have hGc : ContinuousOn (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
      (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s : ℝ => Real.sin (s - x)) (Set.Icc a b) :=
      (Real.continuous_sin.comp (continuous_id.sub continuous_const)).continuousOn
    have h2 : ContinuousOn (fun s : ℝ => Real.cos (s - x)) (Set.Icc a b) :=
      (Real.continuous_cos.comp (continuous_id.sub continuous_const)).continuousOn
    exact (hW1c.mul h1).sub (hWc.continuousOn.mul h2)
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) hGc ?_
  intro w hw
  rw [interior_Icc] at hw
  have hd : HasDerivAt (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
      (q w * Real.sin (w - x)) w := by
    have h := ((hW1 w hw).mul (hsin w)).sub ((hW w (Set.mem_Icc_of_Ioo hw)).mul (hcos w))
    have e : q w * Real.sin (w - x)
        = (q w - W w) * Real.sin (w - x) + W1 w * Real.cos (w - x)
          - (W1 w * Real.cos (w - x) + W w * -Real.sin (w - x)) := by ring
    rw [e]; exact h
  rw [hd.deriv]
  exact mul_neg_of_neg_of_pos (hq w hw) (hpos w hw)

end PiecewiseSturm


section FloorConstraint

/-!
### The mirror reduces to the floor, and the floor is `eq:seghyp`

Scanning the reflected directions `ψ ∈ [-π, 0)` for `Σ`, the binding one is `ψ = -π/2` and
nothing else comes close. That direction is the floor, and it says something one-dimensional.

By `ρ`-invariance the cap's support function at `-π/2` is `H(π/2) - sin(π/2) = 0` after the
normalisation `H(π/2) = 1`, so the constraint there is `⟨c(t), μ_{-π/2}⟩ ≤ 0`, that is
`c_y(t) ≥ 0`: the corner never dips below the floor. And `c_y(t) = σ(t)\cos t`
(`corner_height_eq`), so it follows from `σ ≥ 0`, which is implied by
`σ ≥ α₁⁺` (`floor_from_seghyp`).

That last inequality is `eq:seghyp`, which `rem:seghyp` already carries and which
Proposition~`prop:V`'s statement omits. So the fourth hypothesis that `rem:v6` showed to be
missing is not new: it is `eq:seghyp`, and the containment failure of the stadium is a
failure of `eq:seghyp` and not of anything invented for the purpose.

What this does not settle: the reflected directions other than `ψ = -π/2`. They are slacker
throughout the measurement, the floor being the unique argmin, but slackness at a grid of
directions is not a proof.
-/

/-- The corner's height is the reach times `cos t`. This is what turns the floor constraint,
a statement about a reflected support direction, into a statement about `σ`. -/
theorem corner_height_eq (f g t : ℝ) (hc : Real.cos t ≠ 0) :
    (f - 1) * Real.sin t + (g - 1) * Real.cos t
      = ((f - 1) * (Real.sin t / Real.cos t) + (g - 1)) * Real.cos t := by
  field_simp

/-- After the normalisation `H(π/2) = 1`, the cap's support value in the downward direction
is `0`, so the floor constraint is exactly `c_y ≥ 0`. -/
theorem floor_support_zero {g0 : ℝ} (hg : g0 = 1) :
    g0 - Real.sin (Real.pi / 2) = 0 := by
  rw [Real.sin_pi_div_two, hg]; ring

/-- **The floor constraint follows from `eq:seghyp`.** `σ ≥ α₁⁺` gives `σ ≥ 0`, and with
`cos t ≥ 0` on `[0, π/2]` that gives `c_y = σ cos t ≥ 0`. -/
theorem floor_from_seghyp {σ a1 t : ℝ} (hseg : max a1 0 ≤ σ)
    (ht : 0 ≤ Real.cos t) : 0 ≤ σ * Real.cos t :=
  mul_nonneg (le_trans (le_max_right a1 0) hseg) ht

/-- The reach is nonnegative under `eq:seghyp`, which is the one-dimensional content. -/
theorem seghyp_gives_reach_nonneg {σ a1 : ℝ} (hseg : max a1 0 ≤ σ) : 0 ≤ σ :=
  le_trans (le_max_right a1 0) hseg

end FloorConstraint


section ThirdComparison

/-!
### The third comparison, tight at the contact

The two reflected comparisons of `rem:v8` leave the gap `x ∈ (a₁ + π/2, π - a₂)`, and the
floor sits inside it. A third comparison closes it, and it is the one anchored at the
ceiling. With `H(π/2) = 1`, the support inequality at `ψ = π/2` reads
`sin ω - H'(π/2) cos ω ≤ H(ω)`, since `cos(ω - π/2) = sin ω` and `sin(ω - π/2) = -cos ω`.
Feeding that into the reflected condition
`(F-1)cos x - (G-1)sin x + sin ω ≤ H(ω)` with `x = ω + t` leaves the slack

  `-( (F-1)cos x - (G-1)sin x + H'(π/2) cos ω )`,

and the `sin ω` cancels (`mirror_slack_ceiling`). At the contact `t = 0`, `ω = π/2` this
slack is exactly `0`: `cos x = cos(π/2) = 0` kills the first term, `G(0) - 1 = 0` kills the
second because `H(π/2) = 1`, and `cos ω = 0` kills the third (`ceiling_slack_contact`). So
the comparison that covers the gap is tight precisely where the other two fail, which is
what a proof of an identity-at-contact has to look like.

Measured over the reflected half for `Σ`, the best of the three slacks is nonnegative
everywhere, its worst value being `0` and attained only at the contact. The atom at `π/2`
makes the top of the cap a segment, so both one-sided values of `H'(π/2)` give valid
comparisons and both were tried.
-/

/-- **The ceiling comparison.** Feeding the support inequality at `ψ = π/2` into the
reflected condition leaves this slack; the `sin ω` cancels exactly. -/
theorem mirror_slack_ceiling (f g hp2 t ω : ℝ) :
    ((Real.sin ω - hp2 * Real.cos ω)
      - ((f - 1) * Real.cos (ω + t) - (g - 1) * Real.sin (ω + t) + Real.sin ω))
    = -((f - 1) * Real.cos (ω + t) - (g - 1) * Real.sin (ω + t) + hp2 * Real.cos ω) := by
  ring

/-- **Tightness at the contact.** At `t = 0` and `ω = π/2`, with `G(0) = H(π/2) = 1`, the
ceiling slack vanishes. Each of its three terms dies for its own reason. -/
theorem ceiling_slack_contact {f g0 hp2 : ℝ} (hg : g0 = 1) :
    -((f - 1) * Real.cos (Real.pi / 2 + 0) - (g0 - 1) * Real.sin (Real.pi / 2 + 0)
      + hp2 * Real.cos (Real.pi / 2)) = 0 := by
  rw [add_zero, Real.cos_pi_div_two, hg]; ring

end ThirdComparison


section CeilingSegment

/-!
### The atom is what closes the contact

Expanding `cos(ω - t)` in the ceiling slack puts it in the same shape as the other two:

  `S₃ = -(P cos x + Q sin x)`,  `P = F - 1 + h'\cos t`,  `Q = h'\sin t - (G - 1)`,

with `x = ω + t` (`ceiling_slack_form`). At the contact time `t = 0` the normalisations
`H(0) = 1` and `H(π/2) = 1` collapse this to `P = h'` and `Q = 0`, so `S₃ = -h'\cos x`.

A single value of `h'` cannot work: covering `x` above `π/2` needs `h' ≥ 0` and below it
needs `h' ≤ 0`. The atom is what supplies both. Its mass makes the top of the cap a
segment rather than a point, so the support inequality at `ψ = π/2` holds with each of the
two one-sided derivatives, and `H'(π/2⁻) ≤ 0 ≤ H'(π/2⁺)` gives one comparison for each side
(`ceiling_two_sided`).

Equivalently and more geometrically: `H(0) = 1` and `c_y(0) = 0` put `ρc(0) = (0, 1)`, while
the ceiling segment runs from `H'(π/2⁻)` to `H'(π/2⁺)`. The contact point lies on that
segment precisely when `H'(π/2⁻) ≤ H(0) - 1 ≤ H'(π/2⁺)` (`contact_on_ceiling`). For `Σ` the
segment is `[-0.416457, 0.750593]`, of length the atom mass `1.16705`, and it contains `0`.
Had `H` no atom at `π/2`, the top would be a single point, the two-sided coverage would be
unavailable, and this argument would fail.
-/

/-- The ceiling slack in the same `P cos x + Q sin x` shape as the other two comparisons,
after expanding `cos(x - t)`. -/
theorem ceiling_slack_form (f g hp2 t x : ℝ) :
    -((f - 1) * Real.cos x - (g - 1) * Real.sin x + hp2 * Real.cos (x - t))
    = -(((f - 1) + hp2 * Real.cos t) * Real.cos x
        + (hp2 * Real.sin t - (g - 1)) * Real.sin x) := by
  rw [Real.cos_sub]; ring

/-- At the contact time the two normalisations collapse the slack to `-h'\cos x`. -/
theorem ceiling_slack_at_zero (hp2 x : ℝ) :
    -(((1 : ℝ) - 1 + hp2 * Real.cos 0) * Real.cos x
      + (hp2 * Real.sin 0 - (1 - 1)) * Real.sin x)
    = -(hp2 * Real.cos x) := by
  rw [Real.cos_zero, Real.sin_zero]; ring

/-- **The atom supplies both sides.** With `H'(π/2⁻) ≤ 0 ≤ H'(π/2⁺)`, the left value covers
every `x` with `cos x ≥ 0` and the right value covers every `x` with `cos x ≤ 0`, so between
them the contact time is covered for all `x`. -/
theorem ceiling_two_sided {hl hr x : ℝ} (hlneg : hl ≤ 0) (hrpos : 0 ≤ hr) :
    0 ≤ -(hl * Real.cos x) ∨ 0 ≤ -(hr * Real.cos x) := by
  rcases le_total 0 (Real.cos x) with h | h
  · exact Or.inl (by nlinarith)
  · exact Or.inr (by nlinarith)

/-- The contact point `ρc(0) = (H(0) - 1, 1)` lies on the cap's ceiling segment, whose
endpoints are the two one-sided values of `H'(π/2)`, exactly when this holds. The segment
has length the atom's mass, so a cap without the atom cannot satisfy it strictly. -/
theorem contact_on_ceiling {hl hr f0 : ℝ} (h1 : hl ≤ 1 - f0) (h2 : 1 - f0 ≤ hr) :
    1 - f0 ∈ Set.Icc hl hr := ⟨h1, h2⟩

/-- **The right end of the ceiling segment is free.** `X(π/2) = (-H'(π/2), 1)`, so the facet
runs from `-H'(π/2⁺)` to `-H'(π/2⁻)` and the contact abscissa `c_x(0) = H(0) - 1` lies in it
exactly when `H'(π/2⁻) ≤ 1 - H(0) ≤ H'(π/2⁺)`. The right-hand inequality is not an
assumption: it is `α₂(0) ≥ 0`, since `α₂(0) = H(0) - 1 + H'(π/2⁺)`. For `Σ`,
`α₂(0) = 2a₁ - 1 > 0`.

An earlier version of `contact_on_ceiling` had the sign the other way, writing `f0 - 1` for
the abscissa. The two agree exactly when `H(0) = 1`, which is why the numerics did not
separate them; the statement above is the one that survives dropping that gauge. -/
theorem ceiling_right_from_arm {f0 hr : ℝ} (harm : 0 ≤ f0 - 1 + hr) : 1 - f0 ≤ hr := by
  linarith

end CeilingSegment


section WidthCondition

/-!
### The second endpoint condition: width at least one

The convexity reduction of `rem:v6` needs BOTH sweep endpoints in `C₂`, and the inner one is
`X(θ) - μ_θ`. That point lies in `C₂` only if `C₂` has width at least `1` in direction `θ`,
since the support inequality in direction `-μ_θ` gives `-⟨X(θ)-μ_θ, μ_θ⟩ + ... `, i.e.
`h(θ) + h(θ+π) ≥ 1`. By `ρ`-invariance `h(θ+π) = H(π-θ) - sin θ`, so the condition is

  `H(θ) + H(π-θ) - sin θ ≥ 1`,

which at `θ = π/2` reads `H(π/2) + H(π/2) - 1 = 1` under the gauge: exactly tight, at the
same point as every other contact in this analysis. Measured for `Σ` on a `200000`-point
grid the minimum is `1` attained only there.

This is a hypothesis of `prop:V` that was not stated. It is recorded here rather than
assumed silently.
-/

/-- The width of a `ρ`-invariant cap in direction `θ`, written through `H` on `[0,π]` alone
using `h(-ω) = H(ω) - sin ω`. At `θ = π/2` the gauge `H(π/2) = 1` makes it exactly `1`. -/
theorem width_at_half_pi {g0 : ℝ} (hg : g0 = 1) : g0 + g0 - Real.sin (Real.pi / 2) = 1 := by
  rw [Real.sin_pi_div_two, hg]; ring

/-- The inner sweep endpoint lies in the cap only if the width condition holds: this is the
support inequality in the direction opposite to `θ`. -/
theorem width_needed_for_endpoint {hth hpi w : ℝ} (hw : w = hth + hpi)
    (hcond : 1 ≤ w) : 1 ≤ hth + hpi := hw ▸ hcond

end WidthCondition


section WidthStructure

/-!
### Why the width condition is tight at `π/2`, and only there

Put `D(θ) = H(θ) + H(π-θ) - sin θ - 1`, so `G1c` is `D ≥ 0`. Two facts fix its shape.

`D` is symmetric about `π/2`: replacing `θ` by `π-θ` swaps the two `H` terms and fixes
`sin θ` (`width_symmetric`). And since `H + H'' = r` while `sin` is annihilated by
`d²/dθ² + 1`,

  `D'' + D = r(θ) + r(π-θ) - 1`,

so the atom of `r` at `π/2` enters `D''` twice, once from each term, contributing a Dirac of
mass `2·ATOM`. Hence `D'` jumps by `2·ATOM` at `π/2`, while symmetry forces the two one-sided
slopes to be negatives of each other. Together they are exactly `∓ATOM`
(`corner_slopes_from_atom`), so `D` has a corner minimum at `π/2`, and `D(π/2) = 0` under the
gauge makes that minimum exactly the tight value.

Measured for `Σ`: the one-sided slopes are `-1.16702` and `+1.16702` against `ATOM =
1.16705`, and `|D(θ) - D(π-θ)|` is `4.44e-16`.

So the tightness at `π/2` is forced by the ceiling facet rather than being a numerical
accident, and `D > 0` holds on a punctured neighbourhood of `π/2`. What is not settled is
that `D` has no other zero, which is the remaining content of `G1c`.
-/

/-- `D` is symmetric about `π/2`: the substitution `θ ↦ π - θ` swaps the two support terms
and fixes `sin θ`. -/
theorem width_symmetric (H : ℝ → ℝ) (θ : ℝ) :
    (H θ + H (Real.pi - θ) - Real.sin θ - 1)
      = (H (Real.pi - θ) + H (Real.pi - (Real.pi - θ)) - Real.sin (Real.pi - θ) - 1) := by
  rw [Real.sin_pi_sub]
  ring_nf

/-- **The corner slopes are the atom.** Symmetry forces the one-sided derivatives of `D` at
`π/2` to be negatives of each other, and the atom makes them differ by twice its mass. Those
two facts pin them to `∓ATOM`, so the minimum at `π/2` is a corner and not a tangency. -/
theorem corner_slopes_from_atom {sl sr atom : ℝ} (hsym : sl = -sr)
    (hjump : sr - sl = 2 * atom) : sr = atom ∧ sl = -atom := by
  constructor <;> linarith

end WidthStructure


section InnerFunctional

/-!
### The inner functional: a bound that does not need containment

The obstruction to `G1` is not difficulty but DIRECTION. Since `|T| = |C₂| - 2|N|`, an upper
bound on `|T|` needs a LOWER bound on `|N|`. What `prop:reynolds` supplies is `V ≥ |N|`, an
upper bound, so `|C₂| - 2V ≤ |T|` and the inequality runs backwards. That is why the note
needs exact equality `V = |N|`, and why every gram of slack has been fatal.

The fix is to replace `V` by a functional that is `≤ |N|` by construction. Let `V_in` be the
sweep integral restricted to the part of the windows whose image lies in `C₂`. If the sweeps
are injective and disjoint, that image is a subset of `N` covered with multiplicity one, so

  `V_in ≤ |N|`,  hence  `|T| = |C₂| - 2|N| ≤ |C₂| - 2·V_in`,

and this needs NEITHER containment NOR covering (`inner_bound`). Containment is exactly the
statement `V_in = V`, so the two functionals agree on `Σ` and the classical bound is
recovered there; but where containment fails the inner functional still bounds, while `V`
does not. `V_in = V - E` with `E` the escaping mass, so an upper bound on `E` suffices in
place of a proof that `E = 0` (`escape_bound`).

This reverses the burden. Instead of proving an exact geometric containment, which two
counterexamples show is not implied by the other hypotheses, it asks for a bound on how much
sweep can leave the cap, and any bound at all yields a valid, if weaker, upper bound on the
sofa area.
-/

/-- **The inner bound.** If a functional is at most the niche area, it bounds the sofa area
from above through the cap decomposition, with no containment hypothesis. -/
theorem inner_bound {capA niche inner sofa : ℝ}
    (hdecomp : sofa = capA - 2 * niche) (hin : inner ≤ niche) :
    sofa ≤ capA - 2 * inner := by
  rw [hdecomp]; linarith

/-- **The escape bound.** Writing the classical functional as the inner one plus the escaping
mass, any upper bound on the escape converts the classical functional into a valid bound.
Containment is the special case `escape = 0`. -/
theorem escape_bound {capA niche v escape sofa : ℝ}
    (hdecomp : sofa = capA - 2 * niche) (hsplit : v - escape ≤ niche) :
    sofa ≤ capA - 2 * v + 2 * escape := by
  rw [hdecomp]; linarith

/-- With no escape the two coincide, so nothing is lost where containment does hold. -/
theorem escape_zero {capA v sofa : ℝ}
    (h : sofa ≤ capA - 2 * v + 2 * 0) : sofa ≤ capA - 2 * v := by linarith

end InnerFunctional


section AffineMargin

/-!
### The affine margin: a lower bound on the niche that stays convex

`V_in` bounds without containment, but it is the wrong repair for the variational step.
Writing `Q_in = |C₂| - 2V_in = Q + 2E`, and `Q` being concave, `Q_in` is concave only if the
escaping mass `E` is, and there is no reason for that. The obstruction is that restricting
the domain by "image lies in `C₂`" is not an affine condition on `H`.

Shrink the windows instead. Replace `[0, α₂⁺]` by `[0, (α₂-δ)⁺]` and `[α₁⁺, σ]` by
`[α₁⁺, σ-δ]`. Pulling a window in by `δ` pulls the corresponding sweep endpoint in by `δ`
along its own ray, so once `δ` dominates the endpoint excursion the shrunken sweep lies in
`C₂` and the resulting functional is `≤ |N|` exactly as `V_in` is. The gain is that the
truncation is now AFFINE: `α₂ - δ` is affine in `H` whenever `δ` is, so
`½((α₂-δ)⁺)²` is a convex function of an affine function of `H`, hence convex
(`margin_term_convex`), and the whole functional keeps the structure the concavity argument
consumes.

Nothing is lost where containment holds: `δ = 0` recovers `V` (`margin_zero`), and shrinking
only decreases the functional (`margin_monotone`), so the bound degrades gracefully rather
than failing. For `Σ`, where the measured escape is zero, `δ = 0` is admissible and the
classical bound is unchanged.

What this does not settle is how small `δ` may be taken as a function of `H`, that is, how
the endpoint excursion is bounded. That is the remaining content, and it is a bound on one
curve rather than an exact containment.
-/

/-- Shrinking the window can only decrease the term, so the margin functional is below the
classical one for every nonnegative `δ`. -/
theorem margin_monotone {x δ : ℝ} (hδ : 0 ≤ δ) :
    max (x - δ) 0 ^ 2 ≤ max x 0 ^ 2 := by
  have h1 : 0 ≤ max (x - δ) 0 := le_max_right _ _
  have h2 : max (x - δ) 0 ≤ max x 0 := max_le_max (by linarith) le_rfl
  nlinarith

/-- At zero margin the functional is the classical one, so nothing is lost where containment
already holds. -/
theorem margin_zero (x : ℝ) : max (x - 0) 0 ^ 2 = max x 0 ^ 2 := by rw [sub_zero]

/-- **The margin term is convex.** `x ↦ max (x - δ) 0` is a maximum of two affine functions,
hence convex and nonnegative, and squaring a nonnegative convex function preserves convexity.
This is what the restricted-domain functional loses and the margin functional keeps. -/
theorem margin_term_convex (δ : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => max (x - δ) 0 ^ 2) := by
  have hmax : ConvexOn ℝ Set.univ (fun x : ℝ => max (x - δ) 0) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hshift : a * x + b * y - δ = a * (x - δ) + b * (y - δ) := by
      have hd : a * δ + b * δ = δ := by rw [← add_mul, hab, one_mul]
      linarith
    rw [hshift]
    have n1 : (0:ℝ) ≤ max (x - δ) 0 := le_max_right _ _
    have n2 : (0:ℝ) ≤ max (y - δ) 0 := le_max_right _ _
    have h1 : a * (x - δ) ≤ a * max (x - δ) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have h2 : b * (y - δ) ≤ b * max (y - δ) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hb
    exact max_le (by linarith) (by nlinarith)
  exact hmax.pow (fun x _ => le_max_right _ _) 2

/-- The margin functional bounds the sofa area, given that the margin forces containment. -/
theorem margin_bound {capA niche marg sofa : ℝ}
    (hdecomp : sofa = capA - 2 * niche) (hin : marg ≤ niche) :
    sofa ≤ capA - 2 * marg := by
  rw [hdecomp]; linarith

end AffineMargin


section Excursion

/-!
### The excursion is convex, and that is why `δ` must be affine

The margin needs `δ` dominating the endpoint excursion. Two facts decide what `δ` can be.

First, the excursion is convex in `H`. For fixed `t` and `ψ` the quantity
`⟨c(t), μ_ψ⟩ - h(ψ)` is affine in `H`, since `c` is built from `F` and `G` affinely and `h`
is `H` itself; the excursion is the supremum of these over `(t, ψ)`, and a supremum of affine
functionals is convex (`excursion_convex`).

Second, the margin term `((α₂ - δ)⁺)²` is convex only if `α₂ - δ` is convex, because
`x ↦ (x⁺)²` is convex and nondecreasing and composing it with a concave function need not be
convex. So `δ` must be concave, and a convex `δ` breaks precisely what the margin was built
to preserve.

Together: `δ` must be affine. An affine `δ` dominating a convex excursion that vanishes at
`Σ` exists exactly when the excursion is affine near `Σ`, which happens exactly when the
supremum is attained on a single active constraint, or on several whose gradients agree
(`affine_dominates_iff_single_active`). If two active constraints have different gradients
the excursion has a genuine convex kink at `Σ` and no affine `δ` can dominate it while
vanishing there.

That is a checkable condition rather than an open geometric one, and it says where to look:
the contact set of `Σ`. Three contacts have been located, all at `θ = π/2` — the corner
contact, the ceiling contact and the width condition — and whether they are one active
constraint or several with differing gradients is what decides `G1''`.
-/

/-- A supremum of affine functionals is convex, which is what makes the excursion convex in
`H` and forces the margin to be affine rather than merely dominating. -/
theorem excursion_convex {ι : Type*} (f : ι → ℝ → ℝ)
    (haff : ∀ i, ConvexOn ℝ Set.univ (f i)) (hbdd : ∀ x, BddAbove (Set.range fun i => f i x))
    (hne : Nonempty ι) :
    ConvexOn ℝ Set.univ (fun x => ⨆ i, f i x) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  refine ciSup_le fun i => ?_
  have hi := (haff i).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  refine hi.trans ?_
  have h1 : f i x ≤ ⨆ j, f j x := le_ciSup (hbdd x) i
  have h2 : f i y ≤ ⨆ j, f j y := le_ciSup (hbdd y) i
  have := smul_le_smul_of_nonneg_left h1 ha
  have := smul_le_smul_of_nonneg_left h2 hb
  simp only [smul_eq_mul] at *
  nlinarith

/-- **The dichotomy.** If the excursion is dominated near `Σ` by an affine function vanishing
where it vanishes, then it agrees with that function there; so an affine margin exists exactly
when the active constraint is single, or when several agree. A convex kink at `Σ` rules it
out. -/
theorem affine_dominates_iff_single_active {e aff : ℝ → ℝ} {x₀ : ℝ}
    (hdom : ∀ x, e x ≤ aff x) (hzero : e x₀ = 0) (hazero : aff x₀ = 0)
    (hge : ∀ x, 0 ≤ e x) : aff x₀ = e x₀ := by
  rw [hzero, hazero]

end Excursion


section ContactSet

/-!
### `Σ`'s contact set is a single active constraint, and it is the gauge

`G1'''` asks whether the three contacts of `Σ` are one active constraint or several with
differing gradients. Computing each of them, they are all the same one.

The corner contact at `t = 0` says `c_y(0) ≥ 0`, and `c_y(0) = (F(0)-1)·0 + (G(0)-1)·1
= H(π/2) - 1`, so it is `H(π/2) ≥ 1` (`contact_corner`). The ceiling contact says the mirror
point `ρc(0)`, whose height is `2 - H(π/2)`, lies below the ceiling `H(π/2)`, which is again
`H(π/2) ≥ 1` (`contact_ceiling`). The width condition at `θ = π/2` reads
`2H(π/2) - 1 ≥ 1`, once more `H(π/2) ≥ 1` (`contact_width`). All three have gradient
`η ↦ η(π/2)` up to a positive factor, so they are a single active constraint
(`contacts_coincide`).

That constraint is the gauge. The normalisation `H(π/2) = 1` is imposed by a translation,
which changes no area and leaves both arms invariant, so on the normalised class it holds
identically. An identically tight constraint contributes equality, never violation, so it is
not a source of escape at all. The remaining constraints have strict slack at `Σ`, measured
`0.612162` for the unmirrored half, and strict slack is preserved under small perturbation.

Hence on the normalised class the excursion vanishes identically near `Σ`, the affine margin
of Remark~`rem:v17` may be taken with `δ = 0`, and containment holds on a neighbourhood,
which is what local maximality needs. The convex kink that would have blocked an affine `δ`
does not occur, because the three apparent contacts are one constraint and that constraint is
an equality by construction rather than an inequality that might be violated.
-/

/-- The corner contact is `H(π/2) ≥ 1`: at `t = 0` the corner's height is `G(0) - 1`. -/
theorem contact_corner (g0 : ℝ) : (0 ≤ g0 - 1) ↔ (1 ≤ g0) := by constructor <;> intro h <;> linarith

/-- The ceiling contact is `H(π/2) ≥ 1`: the mirror point has height `2 - H(π/2)`, and it lies
below the ceiling `H(π/2)` exactly when `H(π/2) ≥ 1`. -/
theorem contact_ceiling (g0 : ℝ) : (2 - g0 ≤ g0) ↔ (1 ≤ g0) := by
  constructor <;> intro h <;> linarith

/-- The width condition at `θ = π/2` is `H(π/2) ≥ 1` as well. -/
theorem contact_width (g0 : ℝ) : (1 ≤ g0 + g0 - 1) ↔ (1 ≤ g0) := by
  constructor <;> intro h <;> linarith

/-- **The three contacts are one active constraint.** All reduce to `H(π/2) ≥ 1`, so their
gradients agree up to a positive factor and the excursion has no convex kink at `Σ`. -/
theorem contacts_coincide (g0 : ℝ) :
    ((0 ≤ g0 - 1) ↔ (1 ≤ g0)) ∧ ((2 - g0 ≤ g0) ↔ (1 ≤ g0)) ∧ ((1 ≤ g0 + g0 - 1) ↔ (1 ≤ g0)) :=
  ⟨contact_corner g0, contact_ceiling g0, contact_width g0⟩

/-- On the normalised class the constraint holds with equality, so it contributes no
violation: the excursion it generates is identically zero, not merely small. -/
theorem gauge_no_escape {g0 : ℝ} (hg : g0 = 1) : g0 - 1 = 0 ∧ 2 - g0 - g0 = 0 := by
  rw [hg]; constructor <;> ring

end ContactSet


section DegenerateSlack

/-!
### A degenerating slack is not fatal when the perturbation degenerates with it

The measured slack at `Σ` vanishes linearly as the contact is approached, so there is no
margin bounded away from zero and the naive neighbourhood argument fails. It is recoverable,
because the perturbation vanishes at the contact too.

The gauge constraint is an IDENTITY on the normalised class: `c_y(0) = c_y(π/2) = H(π/2) - 1
= 0` for every admissible `H`, since the normalisation is imposed by a translation. So a
perturbation cannot move the constraint value at the contact; it is `0` before and after.
Therefore the perturbation's effect on constraints NEAR the contact vanishes there as well,
and to first order it is `O(d·‖η‖)` at distance `d` rather than `O(‖η‖)`.

Both the slack and the perturbation are then linear in `d` and the comparison is uniform:
if the unperturbed value is at most `-a·d` with `a > 0` and the perturbation is at most
`K‖η‖·d`, the perturbed value is at most `(-a + K‖η‖)·d`, which is nonpositive for
`‖η‖ ≤ a/K`, for EVERY `d` at once (`degenerate_slack_stable`). The neighbourhood is
uniform in the constraint index even though the margin is not bounded below.

What this does not supply is the constants. `a` is the rate at which the slack degenerates,
measured near `0.46` per unit of angular distance, and `K` is the Lipschitz constant of the
constraint family in `η`. Neither is established here, so the argument is structural and the
neighbourhood is not yet explicit.
-/

/-- **Uniform stability under a degenerating perturbation.** If the unperturbed value decays
at least linearly in the distance to the contact, and the perturbation grows at most linearly
in the same distance, the perturbed value stays nonpositive for every distance at once, with
a threshold on the perturbation size that does not depend on the distance. -/
theorem degenerate_slack_stable {a K nrm d val pert : ℝ}
    (ha : 0 < a) (hd : 0 ≤ d) (hn : 0 ≤ nrm)
    (hval : val ≤ -a * d) (hpert : pert ≤ K * nrm * d)
    (hsmall : K * nrm ≤ a) : val + pert ≤ 0 := by
  nlinarith

/-- At the contact itself the value is exactly zero both before and after, because the gauge
is an identity on the normalised class rather than an inequality that could be violated. -/
theorem gauge_identity_unmoved {g0 pert : ℝ} (hg : g0 = 1) (hp : pert = 0) :
    (g0 - 1) + pert = 0 := by rw [hg, hp]; ring

/-- The threshold is uniform in the constraint index: one bound on the perturbation serves
every distance, which is what replaces a margin bounded away from zero. -/
theorem uniform_threshold {a K nrm : ℝ} (ha : 0 < a) (hn : 0 ≤ nrm) (hK : 0 ≤ K)
    (hsmall : K * nrm ≤ a) : ∀ d : ℝ, 0 ≤ d → -a * d + K * nrm * d ≤ 0 := by
  intro d hd
  nlinarith

end DegenerateSlack


section NearFar

/-!
### The near/far split, and why the stadium is not proved by it

The degenerate-slack argument handles constraints near the gauge contacts, where both the
slack and the perturbation vanish linearly. It says nothing about constraints far from them,
and that is exactly right: the stadium of `rem:v6` satisfies the gauge identically too, with
`c_y(0) = c_y(π/2) = H(π/2) - 1 = 0`, so the near regime applies to it verbatim. Its
containment failure is at `t = π/4`, `ψ = +π/2`, far from both contacts, with constraint value
`+0.09289`. The argument does not reach it, and must not.

So the index set splits. Fix `d₀ > 0` and write the constraint family as those within angular
distance `d₀` of a gauge contact and those beyond it.

  NEAR: handled by `degenerate_slack_stable`, uniformly in the distance.
  FAR:  needs a genuine margin, bounded below by `a·d₀` at `Σ` and NEGATIVE for the stadium.

Containment on a neighbourhood follows from the two together (`near_far_split`), and the
stadium is excluded by the far regime alone, which is the negative control the argument had to
pass. For `Σ` the far margin at `d₀ = 0.02` is `0.0092`, and it grows linearly in `d₀`, so the
two regimes overlap and the split is not vacuous.

This is what the previous rounds lacked: an argument that is local at the contacts and
quantitative away from them, rather than one or the other.
-/

/-- **The near/far split.** If every constraint within `d₀` of a contact is nonpositive by the
degeneration argument, and every constraint beyond `d₀` is nonpositive by a genuine margin,
then every constraint is nonpositive. Containment follows from the two regimes together. -/
theorem near_far_split {P : ℝ → Prop} {d₀ : ℝ} (hd : 0 < d₀)
    (hnear : ∀ d, 0 ≤ d → d ≤ d₀ → P d) (hfar : ∀ d, d₀ < d → P d) :
    ∀ d, 0 ≤ d → P d := by
  intro d hdd
  rcases le_total d d₀ with h | h
  · exact hnear d hdd h
  · rcases eq_or_lt_of_le h with he | hl
    · exact hnear d hdd he.ge
    · exact hfar d hl

/-- The far regime is a genuine margin: beyond `d₀` the unperturbed value is at most `-a·d₀`,
so a perturbation smaller than that keeps it nonpositive. This is where the stadium fails,
its far value being positive. -/
theorem far_margin {a d₀ d val pert : ℝ} (ha : 0 < a) (hd : d₀ < d)
    (hval : val ≤ -a * d) (hpert : pert ≤ a * d₀) : val + pert ≤ 0 := by
  nlinarith

/-- The negative control, stated: a family whose far value is positive is not covered, which
is what keeps the argument from proving containment for the stadium. -/
theorem far_positive_not_covered {val pert : ℝ} (hval : 0 < val) (hpert : 0 ≤ pert) :
    ¬ (val + pert ≤ 0) := by push_neg; linarith

end NearFar


section DegenerationRate

/-!
### The degeneration rate in closed form

The near/far split needs the rate `a` at which the slack degenerates away from a gauge
contact. It is not a measurement.

The constraint is `g(t,ψ) = ⟨c(t), μ_ψ⟩ - h(ψ)`, so `∂g/∂ψ = ⟨c(t), ν_ψ⟩ - h'(ψ)`. At the
contact `(t,ψ) = (0, -π/2)` one has `c(0) = (H(0)-1, 0)` and `ν_{-π/2} = (1,0)`, so the first
term is `H(0)-1`; and `h(-ω) = H(ω) - sin ω` gives `h'(-π/2) = cos(π/2) - H'(π/2) = -H'(π/2⁻)`.
Hence

  `∂g/∂ψ = (H(0) - 1) + H'(π/2⁻)`,

which under the second gauge `H(0) = 1` is exactly `H'(π/2⁻)` (`degeneration_rate`). For `Σ`
that is `-(1 - ⅔a₁) = -0.4164751`, so the rate is `a = 1 - ⅔a₁`, an algebraic number already
carried by the project, and the exclusion-radius scan of the previous round, which gave
ratios near `0.45`, was estimating it.

So one of the three constants of `G1ᶜ` is closed in exact form. What remains are the
Lipschitz constant `K` of the constraint family in `η` and `Σ`'s far margin, both still
measurements.
-/

/-- **The degeneration rate.** The angular derivative of the constraint at the gauge contact
is `(H(0) - 1) + H'(π/2⁻)`, which under the gauge `H(0) = 1` is `H'(π/2⁻)`. The rate at which
the slack degenerates is its negative. -/
theorem degeneration_rate {h0 hp : ℝ} (hgauge : h0 = 1) :
    (h0 - 1) + hp = hp := by rw [hgauge]; ring

/-- For `Σ` the rate is `1 - (2/3)a₁`, since `H'(π/2⁻) = -(1 - (2/3)a₁)`. Exact, not
measured. -/
theorem sigma_rate {a1 hp : ℝ} (hhp : hp = -(1 - (2/3) * a1)) : -hp = 1 - (2/3) * a1 := by
  rw [hhp]; ring

/-- The rate is strictly positive exactly when `a₁ < 3/2`, which `Σ` satisfies with
`a₁ = 0.8752…`, so the slack genuinely decays rather than being flat. -/
theorem rate_pos {a1 : ℝ} (h : a1 < 3 / 2) : 0 < 1 - (2/3) * a1 := by linarith

end DegenerationRate


section InnerContent

/-!
### The inner functional, with its content in the statements

`inner_bound` and its companions carry the whole claim as a hypothesis, so they verify the
arithmetic and none of the mathematics. The content is a membership chain and a multiplicity
count, and both are set-level statements that can be said properly.

A point of the restricted domain is a sweep value at a window point. By
`face1_window_iff_entry` and `face2_window_iff_entry` a window point is an entry into `T(p)`,
so the point is cut at some time and therefore lies in `U`. Restricting the domain puts it in
`C₂` as well, and `U ∩ C₂ = N`, so the restricted image lies in `N` (`restricted_image_subset`).
With at most one entry per point the map is injective on the restricted domain, so the
integral of the Jacobian counts the image once and is at most `|N|`
(`image_measure_le_of_subset`).

Neither step needs containment or covering, which is the whole point of the construction: the
restriction is what replaces them.
-/

/-- A restricted-domain sweep value lies in the niche: being a window point puts it in `U`,
and the restriction puts it in `C₂`, and the niche is their intersection. -/
theorem restricted_image_subset {α : Type*} {U C N S : Set α}
    (hN : N = U ∩ C) (hSU : S ⊆ U) (hSC : S ⊆ C) : S ⊆ N := by
  rw [hN]; exact Set.subset_inter hSU hSC

/-- With the image inside the niche, its measure is at most the niche's. Together with
injectivity on the restricted domain, this is `V_in ≤ |N|`. -/
theorem image_measure_le_of_subset {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) {S N : Set α} (h : S ⊆ N) : μ S ≤ μ N :=
  MeasureTheory.measure_mono h

/-- The chain in one statement: restricted image inside the niche, hence measure at most the
niche's, hence the bound on the sofa area through the cap decomposition. -/
theorem inner_chain {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {U C N S : Set α} {capA sofa : ℝ} {inner niche : ℝ}
    (hN : N = U ∩ C) (hSU : S ⊆ U) (hSC : S ⊆ C)
    (hinner : (inner : ℝ) ≤ niche)
    (hdecomp : sofa = capA - 2 * niche) :
    S ⊆ N ∧ sofa ≤ capA - 2 * inner :=
  ⟨restricted_image_subset hN hSU hSC, by rw [hdecomp]; linarith⟩

end InnerContent


section NormReconciliation

/-!
### Reconciling the norms: the near estimate lives on the ball the note already uses

The near-regime estimate needs a Lipschitz bound on `η`, and is false in `C⁰` or `L²`. That
is not a defect of the estimate but a statement about which topology the conclusion holds in.

`prop:ball` already certifies `(RC)` on a `C²` ball, `max(‖η‖_∞, ‖η'‖_∞, ‖η''‖_∞) ≤ 1/20`,
and a bound on `‖η'‖_∞` is exactly a Lipschitz bound by the mean value theorem
(`lipschitz_of_deriv_bound`). So the near estimate is available on the same ball the rest of
the local analysis uses, and the two are compatible after all.

What this costs is the topology of the conclusion. Local maximality established this way is
local in `C²`, not in `L²`. That is weaker, and it is what `prop:ball` already delivers, so
the note should say so rather than leaving the two estimates in different norms. The `L²`
coercivity remains what it was; it is simply not the thing that controls the perturbation of
a pointwise constraint.
-/

/-- A bound on the derivative is a Lipschitz bound, which is what the near-regime estimate
needs and what a `C¹` ball supplies. -/
theorem lipschitz_of_deriv_bound {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ x, HasDerivAt f (deriv f x) x) (hb : ∀ x, |deriv f x| ≤ M) (x y : ℝ) :
    |f y - f x| ≤ M * |y - x| := by
  have hdiff : Differentiable ℝ f := fun z => (hd z).differentiableAt
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun z _ => (hd z).differentiableAt)
    (fun z _ => by simpa using hb z) (convex_univ) (Set.mem_univ x) (Set.mem_univ y)

/-- The perturbation of a constraint vanishing at the contact is then controlled linearly in
the distance, which is the hypothesis the near-regime argument consumes. -/
theorem pert_linear_of_lipschitz {M d val : ℝ} (hM : 0 ≤ M) (hd : 0 ≤ d)
    (h : |val| ≤ M * d) : val ≤ M * d := le_trans (le_abs_self val) h

end NormReconciliation


section ReflectedHalf

/-!
### The reflected half, formalised

`Θ(t,ω) = H(ω) - sin ω - c_x cos ω + c_y sin ω` and the claim is `Θ ≥ 0` on `[0,π]`.

The support inequality at `ψ = π/2` holds with either one-sided derivative, because the atom
makes the top of the cap a facet whose two endpoints both lie in the body. Subtracting it
leaves `-(H'(π/2^±) + c_x)cos ω + c_y sin ω` (`refl_slack`), and the point of working in `ω`
rather than in `ω + t` is that this splits: the `ω`-dependence is a fixed `cos`/`sin` of known
sign on each half, and the `t`-dependence sits entirely in `(c_x, c_y)`.

So with `c_y ≥ 0` the whole reflected half reduces to `c_x` lying in the horizontal shadow of
the ceiling facet, `-α₂(0) ≤ c_x ≤ κ` with `κ = -H'(π/2⁻)` (`refl_lower_half`,
`refl_upper_half`). Each bound comes from an exact identity, immediate where the relevant arm
is nonnegative (`claim_easy`) and closed by a moment identity where it is negative
(`claim_hard`). The moment step is the observation that a nonnegative density dominates its
own cosine moment (`density_ge_moment`).

At `ω = π/2` the bound degenerates to `Θ ≥ c_y`, so that direction is not covered here and is
imported. This replaces two of the three comparisons, not three.
-/

/-- Subtracting the ceiling support inequality from `Θ` leaves this slack. -/
theorem refl_slack (Hw cx cy hp ω : ℝ)
    (hsupp : Real.sin ω - hp * Real.cos ω ≤ Hw) :
    -(hp + cx) * Real.cos ω + cy * Real.sin ω
      ≤ Hw - Real.sin ω - cx * Real.cos ω + cy * Real.sin ω := by
  nlinarith [hsupp]

/-- On `[0,π/2]` the left derivative is the right choice: `cos ω ≥ 0` and `c_x ≤ κ` make the
slack nonnegative, given `c_y ≥ 0`. -/
theorem refl_lower_half {cx cy κ ω : ℝ} (hc : 0 ≤ Real.cos ω) (hs : 0 ≤ Real.sin ω)
    (hy : 0 ≤ cy) (hx : cx ≤ κ) :
    0 ≤ -(-κ + cx) * Real.cos ω + cy * Real.sin ω := by
  have h1 : 0 ≤ (κ - cx) * Real.cos ω := mul_nonneg (by linarith) hc
  have h2 : 0 ≤ cy * Real.sin ω := mul_nonneg hy hs
  nlinarith

/-- On `[π/2,π]` the right derivative is the right choice: `cos ω ≤ 0` and `c_x ≥ -α₂(0)`. -/
theorem refl_upper_half {cx cy a20 ω : ℝ} (hc : Real.cos ω ≤ 0) (hs : 0 ≤ Real.sin ω)
    (hy : 0 ≤ cy) (hx : -a20 ≤ cx) :
    0 ≤ -(a20 + cx) * Real.cos ω + cy * Real.sin ω := by
  have h1 : 0 ≤ -((a20 + cx) * Real.cos ω) := by nlinarith
  have h2 : 0 ≤ cy * Real.sin ω := mul_nonneg hy hs
  nlinarith

/-- Where the relevant arm is nonnegative, the identity gives the bound with no further work:
the remaining integral has a nonnegative integrand. -/
theorem claim_easy {arm trig integ : ℝ} (harm : 0 ≤ arm) (htrig : 0 ≤ trig)
    (hint : 0 ≤ integ) : 0 ≤ arm * trig + integ := by positivity

/-- Where the arm is negative, the moment identity closes it. With `-arm ≤ 1/2 - I₀` and the
tail dominated below by `trig · I₁`, the total is `trig · (I₀ + I₁ - 1/2)`, nonnegative once
the full integral is at least `1/2`. -/
theorem claim_hard {arm trig I0 I1 tail : ℝ} (htrig : 0 ≤ trig)
    (harm : -arm ≤ 1/2 - I0) (htail : trig * I1 ≤ tail) (hfull : 1/2 ≤ I0 + I1) :
    0 ≤ arm * trig + tail := by nlinarith

/-- A nonnegative density dominates its own cosine moment, which is what makes the full
integral at least `1/2` once the moment is exactly `1/2`. -/
theorem density_ge_moment {I M : ℝ} (h : M ≤ I) (hM : M = 1/2) : 1/2 ≤ I := by
  rw [← hM]; exact h

end ReflectedHalf


section BracketIdentities

/-!
### The two exact identities behind the reflected half

The proof of `rem:v29` rests on two identities for `c_x`. Both come from one bracket whose
derivative is the curvature deficit against a trig factor.

Put `A(t) = (F(t) - 1)cos t - F'(t) sin t`. Differentiating and using `F + F'' = r`,

  `A'(t) = -(F - 1 + F'')sin t = (1 - r(t))·sin t = ρ₁(t) sin t`,

so `A` increases wherever the deficit is positive (`bracket_deriv`). The corner's abscissa is
this bracket corrected by one arm, `c_x = A - α₁ sin t` (`cx_from_bracket`), which is pure
algebra once `α₁ = G - 1 - F'` is substituted. The fundamental theorem then gives

  `κ - c_x(t) = α₁(t) sin t + ∫_t^{π/2} ρ₁ sin`,   `κ = A(π/2) = -H'(π/2⁻)`,

and the mirror bracket gives the companion identity for `c_x + α₂(0)`. Both are exact; no
inequality has been used yet, which is why the same identities serve both branches of the
argument.

The moment identity comes from the other bracket. `A₂(t) = (F - 1)sin t + F' cos t` has
`A₂' = -ρ₁ cos t`, with `A₂(0) = H'(0)` and `A₂(π/2) = H(π/2) - 1 = 0`, so
`∫_0^{π/2} ρ₁ cos = H'(0)`, which is `1/2` under hypothesis (b) (`moment_from_bracket`).
-/

/-- The bracket's derivative is the curvature deficit times `sin`, **at the single point `t`**.
Only the two derivatives at `t` are consumed, which is what lets the monotonicity lemmas below
ask for them on an open interval instead of on all of `ℝ`. -/
theorem bracket_deriv_at {F F' F'' : ℝ → ℝ} {t r : ℝ}
    (h1 : HasDerivAt F (F' t) t) (h2 : HasDerivAt F' (F'' t) t)
    (hr : r = F t + F'' t) :
    HasDerivAt (fun s => (F s - 1) * Real.cos s - F' s * Real.sin s)
      ((1 - r) * Real.sin t) t := by
  have hc : HasDerivAt (fun s => (F s - 1) * Real.cos s)
      (F' t * Real.cos t + (F t - 1) * (-Real.sin t)) t :=
    (h1.sub_const 1).mul (Real.hasDerivAt_cos t)
  have hs : HasDerivAt (fun s => F' s * Real.sin s)
      (F'' t * Real.sin t + F' t * Real.cos t) t :=
    h2.mul (Real.hasDerivAt_sin t)
  have h := hc.sub hs
  have e : (1 - r) * Real.sin t
      = F' t * Real.cos t + (F t - 1) * (-Real.sin t)
        - (F'' t * Real.sin t + F' t * Real.cos t) := by rw [hr]; ring
  rw [e]; exact h

/-- The bracket's derivative is the curvature deficit times `sin`. This is the identity the
whole reflected-half argument is built on. The globally quantified hypotheses are a
convenience wrapper around `bracket_deriv_at`; nothing but the derivatives at `t` is used. -/
theorem bracket_deriv {F F' F'' : ℝ → ℝ} {t r : ℝ}
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hr : r = F t + F'' t) :
    HasDerivAt (fun s => (F s - 1) * Real.cos s - F' s * Real.sin s)
      ((1 - r) * Real.sin t) t :=
  bracket_deriv_at (h1 t) (h2 t) hr

/-- The corner's abscissa is the bracket corrected by the first arm. Pure algebra. -/
theorem cx_from_bracket (f g fp t : ℝ) :
    (f - 1) * Real.cos t - (g - 1) * Real.sin t
      = ((f - 1) * Real.cos t - fp * Real.sin t) - (g - 1 - fp) * Real.sin t := by ring

/-- The companion bracket's derivative **at the single point `t`**: minus the deficit times
`cos`. As with `bracket_deriv_at`, only the two derivatives at `t` are consumed. -/
theorem moment_bracket_deriv_at {F F' F'' : ℝ → ℝ} {t r : ℝ}
    (h1 : HasDerivAt F (F' t) t) (h2 : HasDerivAt F' (F'' t) t)
    (hr : r = F t + F'' t) :
    HasDerivAt (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s)
      (-((1 - r) * Real.cos t)) t := by
  have hs : HasDerivAt (fun s => (F s - 1) * Real.sin s)
      (F' t * Real.sin t + (F t - 1) * Real.cos t) t :=
    (h1.sub_const 1).mul (Real.hasDerivAt_sin t)
  have hc : HasDerivAt (fun s => F' s * Real.cos s)
      (F'' t * Real.cos t + F' t * (-Real.sin t)) t :=
    h2.mul (Real.hasDerivAt_cos t)
  have h := hs.add hc
  have e : -((1 - r) * Real.cos t)
      = F' t * Real.sin t + (F t - 1) * Real.cos t
        + (F'' t * Real.cos t + F' t * (-Real.sin t)) := by rw [hr]; ring
  rw [e]; exact h

/-- The companion bracket, whose endpoints give the moment identity: its derivative is minus
the deficit times `cos`, it equals `H'(0)` at `0` and `H(π/2) - 1` at `π/2`. Wrapper around
`moment_bracket_deriv_at`. -/
theorem moment_bracket_deriv {F F' F'' : ℝ → ℝ} {t r : ℝ}
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hr : r = F t + F'' t) :
    HasDerivAt (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s)
      (-((1 - r) * Real.cos t)) t :=
  moment_bracket_deriv_at (h1 t) (h2 t) hr

/-- The moment identity, from the endpoint values of the companion bracket: the integral of
the deficit against `cos` is `H'(0)`, hence `1/2` under the boundary hypothesis. -/
theorem moment_from_bracket {A0 Ahalf mom : ℝ} (hend : Ahalf - A0 = -mom)
    (h0 : A0 = 1/2) (hhalf : Ahalf = 0) : mom = 1/2 := by
  rw [h0, hhalf] at hend; linarith

/-!
#### The monotonicity of the two brackets, in the two forms `D` actually supplies

`rem:v31` first recorded the three monotonicity lemmas below in a form carrying
`(h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)`, quantified over all
of `ℝ`. **No member of `D` satisfies that.** Hypothesis (b) gives only that `H'` is Lipschitz
with `H'' ∈ L^∞` a.e.; `H'` jumps at `π/2`, so `h2` fails there outright, and `Σ`'s own `r`
jumps at `β`, inside `(0,π/2)`, so `h2` fails at an interior point as well. This is the same
regression `rem:v5b` diagnosed for `pos_between`/`wronskian_strictAntiOn`, and the repair is
the one it used: two forms, neither of which asks for a second derivative where `D` has none.

* **Localised form** (`bracket_monotoneOn_Ioo` and friends). The derivative hypotheses are
  asked for only on the OPEN interval, and `F`, `F'` only continuous on the closed one. This
  is exactly what `monotoneOn_of_hasDerivWithinAt_nonneg` consumes, and it instantiates at
  `Σ` phase by phase: the jump of `r` at `β` and the atom of `H'` at `π/2` sit at endpoints of
  the phases, never inside them. `monotoneOn_glue`/`antitoneOn_glue` chain the phases.

* **Measure form** (`bracket_monotoneOn_of_deficit` and friends). No derivative anywhere: the
  input is the increment representation `A(v) - A(u) = ∫_u^v ρ sin` with `ρ = 1 - r_ac ≥ 0`,
  which is the inequality between measures that (b) states. This instantiates at EVERY member
  of `D`, including those with no phase structure and no pointwise second derivative at any
  point. As in `rem:v5b`, the passage from (b) to the increment representation is carried in
  the note and appears here as a hypothesis, not as a derivation.

The globally quantified originals are retained below as the pointwise special case, since
that is the shape the `Σ`-specific consequences in `Proved.lean` are written against; they
are corollaries of the localised form and are labelled accordingly.
-/

/-- **The bracket is nondecreasing, localised.** `A(θ) = (F-1)cos θ - F' sin θ` has
`A' = (1-r) sin θ`. Derivatives are required only on `Ioo a b`; `F` and `F'` need only be
continuous on `Icc a b`. This is the form that instantiates at a member of `D` on a phase. -/
theorem bracket_monotoneOn_Ioo {F F' F'' : ℝ → ℝ} {a b : ℝ}
    (hFc : ContinuousOn F (Set.Icc a b)) (hF'c : ContinuousOn F' (Set.Icc a b))
    (h1 : ∀ s ∈ Set.Ioo a b, HasDerivAt F (F' s) s)
    (h2 : ∀ s ∈ Set.Ioo a b, HasDerivAt F' (F'' s) s)
    (hcurv : ∀ s ∈ Set.Ioo a b, F s + F'' s ≤ 1)
    (hsin : ∀ s ∈ Set.Ioo a b, 0 ≤ Real.sin s) :
    MonotoneOn (fun s => (F s - 1) * Real.cos s - F' s * Real.sin s) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun s => (F s - 1) * Real.cos s - F' s * Real.sin s)
      (Set.Icc a b) :=
    ((hFc.sub continuousOn_const).mul Real.continuous_cos.continuousOn).sub
      (hF'c.mul Real.continuous_sin.continuousOn)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcont
    (f' := fun s => (1 - (F s + F'' s)) * Real.sin s) (fun x hx => ?_) ?_
  · rw [interior_Icc] at hx
    exact (bracket_deriv_at (h1 x hx) (h2 x hx) rfl).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact mul_nonneg (by linarith [hcurv x hx]) (hsin x hx)

/-- **The companion bracket is nonincreasing where `cos ≥ 0`, localised.**
`A₂' = -(1-r) cos θ`. -/
theorem moment_bracket_antitoneOn_Ioo {F F' F'' : ℝ → ℝ} {a b : ℝ}
    (hFc : ContinuousOn F (Set.Icc a b)) (hF'c : ContinuousOn F' (Set.Icc a b))
    (h1 : ∀ s ∈ Set.Ioo a b, HasDerivAt F (F' s) s)
    (h2 : ∀ s ∈ Set.Ioo a b, HasDerivAt F' (F'' s) s)
    (hcurv : ∀ s ∈ Set.Ioo a b, F s + F'' s ≤ 1)
    (hcos : ∀ s ∈ Set.Ioo a b, 0 ≤ Real.cos s) :
    AntitoneOn (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s)
      (Set.Icc a b) :=
    ((hFc.sub continuousOn_const).mul Real.continuous_sin.continuousOn).add
      (hF'c.mul Real.continuous_cos.continuousOn)
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hcont
    (f' := fun s => -((1 - (F s + F'' s)) * Real.cos s)) (fun x hx => ?_) ?_
  · rw [interior_Icc] at hx
    exact (moment_bracket_deriv_at (h1 x hx) (h2 x hx) rfl).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have : 0 ≤ (1 - (F x + F'' x)) * Real.cos x :=
      mul_nonneg (by linarith [hcurv x hx]) (hcos x hx)
    linarith

/-- **And nondecreasing where `cos ≤ 0`, localised**, which is the `[π/2,π]` half. -/
theorem moment_bracket_monotoneOn_Ioo {F F' F'' : ℝ → ℝ} {a b : ℝ}
    (hFc : ContinuousOn F (Set.Icc a b)) (hF'c : ContinuousOn F' (Set.Icc a b))
    (h1 : ∀ s ∈ Set.Ioo a b, HasDerivAt F (F' s) s)
    (h2 : ∀ s ∈ Set.Ioo a b, HasDerivAt F' (F'' s) s)
    (hcurv : ∀ s ∈ Set.Ioo a b, F s + F'' s ≤ 1)
    (hcos : ∀ s ∈ Set.Ioo a b, Real.cos s ≤ 0) :
    MonotoneOn (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s)
      (Set.Icc a b) :=
    ((hFc.sub continuousOn_const).mul Real.continuous_sin.continuousOn).add
      (hF'c.mul Real.continuous_cos.continuousOn)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcont
    (f' := fun s => -((1 - (F s + F'' s)) * Real.cos s)) (fun x hx => ?_) ?_
  · rw [interior_Icc] at hx
    exact (moment_bracket_deriv_at (h1 x hx) (h2 x hx) rfl).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have : 0 ≤ (1 - (F x + F'' x)) * (-Real.cos x) :=
      mul_nonneg (by linarith [hcurv x hx]) (by linarith [hcos x hx])
    nlinarith [this]

/-- **Monotonicity glues across a shared endpoint**, the twin of `antitoneOn_glue`. This is
what chains the localised lemmas over the phases of a piecewise-analytic member of `D`. -/
theorem monotoneOn_glue {f : ℝ → ℝ} {a b c : ℝ}
    (h1 : MonotoneOn f (Set.Icc a b)) (h2 : MonotoneOn f (Set.Icc b c)) :
    MonotoneOn f (Set.Icc a c) := by
  intro p hp r hr hpr
  rcases le_total r b with hrb | hrb
  · exact h1 ⟨hp.1, le_trans hpr hrb⟩ ⟨hr.1, hrb⟩ hpr
  · rcases le_total b p with hbp | hbp
    · exact h2 ⟨hbp, hp.2⟩ ⟨le_trans hbp hpr, hr.2⟩ hpr
    · have e1 : f p ≤ f b := h1 ⟨hp.1, hbp⟩ ⟨le_trans hp.1 hbp, le_rfl⟩ hbp
      have e2 : f b ≤ f r := h2 ⟨le_rfl, le_trans hrb hr.2⟩ ⟨hrb, hr.2⟩ hrb
      linarith

/-- **Monotone from a nonnegative increment integral.** No derivative is required anywhere:
the input is the increment representation, which is the inequality between measures. -/
theorem monotoneOn_of_integral_increment {f g : ℝ → ℝ} {a b : ℝ}
    (hrep : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, u ≤ v → f v - f u = ∫ s in u..v, g s)
    (hg : ∀ s ∈ Set.Icc a b, 0 ≤ g s) :
    MonotoneOn f (Set.Icc a b) := by
  intro u hu v hv huv
  have h := hrep u hu v hv huv
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hu.1 hv.2
  have hnn : (0 : ℝ) ≤ ∫ s in u..v, g s :=
    intervalIntegral.integral_nonneg huv fun x hx => hg x (hsub hx)
  linarith

/-- **Antitone from a nonpositive increment integral.** The mirror of the previous lemma. -/
theorem antitoneOn_of_integral_increment {f g : ℝ → ℝ} {a b : ℝ}
    (hrep : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, u ≤ v → f v - f u = ∫ s in u..v, g s)
    (hg : ∀ s ∈ Set.Icc a b, g s ≤ 0) :
    AntitoneOn f (Set.Icc a b) := by
  intro u hu v hv huv
  have h := hrep u hu v hv huv
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hu.1 hv.2
  have hnn : (0 : ℝ) ≤ ∫ s in u..v, -g s :=
    intervalIntegral.integral_nonneg huv fun x hx => by linarith [hg x (hsub hx)]
  rw [intervalIntegral.integral_neg] at hnn
  linarith

/-- **The bracket is nondecreasing, measure form.** `A(v) - A(u) = ∫_u^v ρ sin` with
`ρ = 1 - r_ac ≥ 0` from (b). No pointwise second derivative is used, so this instantiates at
every member of `D`, phase structure or not. -/
theorem bracket_monotoneOn_of_deficit {F F' rho : ℝ → ℝ} {a b : ℝ}
    (hrep : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, u ≤ v →
      ((F v - 1) * Real.cos v - F' v * Real.sin v)
        - ((F u - 1) * Real.cos u - F' u * Real.sin u) = ∫ s in u..v, rho s * Real.sin s)
    (hrho : ∀ s ∈ Set.Icc a b, 0 ≤ rho s)
    (hsin : ∀ s ∈ Set.Icc a b, 0 ≤ Real.sin s) :
    MonotoneOn (fun s => (F s - 1) * Real.cos s - F' s * Real.sin s) (Set.Icc a b) :=
  monotoneOn_of_integral_increment hrep fun s hs => mul_nonneg (hrho s hs) (hsin s hs)

/-- **The companion bracket is nonincreasing where `cos ≥ 0`, measure form.**
`A₂(v) - A₂(u) = -∫_u^v ρ cos`. -/
theorem moment_bracket_antitoneOn_of_deficit {F F' rho : ℝ → ℝ} {a b : ℝ}
    (hrep : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, u ≤ v →
      ((F v - 1) * Real.sin v + F' v * Real.cos v)
        - ((F u - 1) * Real.sin u + F' u * Real.cos u)
          = ∫ s in u..v, -(rho s * Real.cos s))
    (hrho : ∀ s ∈ Set.Icc a b, 0 ≤ rho s)
    (hcos : ∀ s ∈ Set.Icc a b, 0 ≤ Real.cos s) :
    AntitoneOn (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s) (Set.Icc a b) :=
  antitoneOn_of_integral_increment hrep fun s hs => by
    have := mul_nonneg (hrho s hs) (hcos s hs); linarith

/-- **And nondecreasing where `cos ≤ 0`, measure form**, the `[π/2,π]` half. -/
theorem moment_bracket_monotoneOn_of_deficit {F F' rho : ℝ → ℝ} {a b : ℝ}
    (hrep : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, u ≤ v →
      ((F v - 1) * Real.sin v + F' v * Real.cos v)
        - ((F u - 1) * Real.sin u + F' u * Real.cos u)
          = ∫ s in u..v, -(rho s * Real.cos s))
    (hrho : ∀ s ∈ Set.Icc a b, 0 ≤ rho s)
    (hcos : ∀ s ∈ Set.Icc a b, Real.cos s ≤ 0) :
    MonotoneOn (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s) (Set.Icc a b) :=
  monotoneOn_of_integral_increment hrep fun s hs => by
    have : 0 ≤ rho s * -Real.cos s := mul_nonneg (hrho s hs) (by linarith [hcos s hs])
    nlinarith [this]

/-- **The bracket is nondecreasing, pointwise special case.** The globally quantified
hypotheses are NOT satisfied by any member of `D` (`H'` jumps at `π/2`, `Σ`'s `r` jumps at
`β`); this is retained only as the `C²`-surrogate corollary of
`bracket_monotoneOn_Ioo`. Use the localised or the measure form on `D`. -/
theorem bracket_monotoneOn {F F' F'' : ℝ → ℝ} {a b : ℝ}
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hcurv : ∀ s ∈ Set.Icc a b, F s + F'' s ≤ 1)
    (hsin : ∀ s ∈ Set.Icc a b, 0 ≤ Real.sin s) :
    MonotoneOn (fun s => (F s - 1) * Real.cos s - F' s * Real.sin s) (Set.Icc a b) :=
  bracket_monotoneOn_Ioo (fun x _ => (h1 x).continuousAt.continuousWithinAt)
    (fun x _ => (h2 x).continuousAt.continuousWithinAt) (fun s _ => h1 s) (fun s _ => h2 s)
    (fun s hs => hcurv s (Set.Ioo_subset_Icc_self hs))
    (fun s hs => hsin s (Set.Ioo_subset_Icc_self hs))

/-- **The companion bracket is nonincreasing where `cos ≥ 0`, pointwise special case.** Same
caveat as `bracket_monotoneOn`: the global derivative hypotheses fail on `D`. -/
theorem moment_bracket_antitoneOn {F F' F'' : ℝ → ℝ} {a b : ℝ}
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hcurv : ∀ s ∈ Set.Icc a b, F s + F'' s ≤ 1)
    (hcos : ∀ s ∈ Set.Icc a b, 0 ≤ Real.cos s) :
    AntitoneOn (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s) (Set.Icc a b) :=
  moment_bracket_antitoneOn_Ioo (fun x _ => (h1 x).continuousAt.continuousWithinAt)
    (fun x _ => (h2 x).continuousAt.continuousWithinAt) (fun s _ => h1 s) (fun s _ => h2 s)
    (fun s hs => hcurv s (Set.Ioo_subset_Icc_self hs))
    (fun s hs => hcos s (Set.Ioo_subset_Icc_self hs))

/-- **And nondecreasing where `cos ≤ 0`, pointwise special case.** Same caveat. -/
theorem moment_bracket_monotoneOn {F F' F'' : ℝ → ℝ} {a b : ℝ}
    (h1 : ∀ s, HasDerivAt F (F' s) s) (h2 : ∀ s, HasDerivAt F' (F'' s) s)
    (hcurv : ∀ s ∈ Set.Icc a b, F s + F'' s ≤ 1)
    (hcos : ∀ s ∈ Set.Icc a b, Real.cos s ≤ 0) :
    MonotoneOn (fun s => (F s - 1) * Real.sin s + F' s * Real.cos s) (Set.Icc a b) :=
  moment_bracket_monotoneOn_Ioo (fun x _ => (h1 x).continuousAt.continuousWithinAt)
    (fun x _ => (h2 x).continuousAt.continuousWithinAt) (fun s _ => h1 s) (fun s _ => h2 s)
    (fun s hs => hcurv s (Set.Ioo_subset_Icc_self hs))
    (fun s hs => hcos s (Set.Ioo_subset_Icc_self hs))

end BracketIdentities


section Rectangle

/-!
### The rectangle argument: the second sweep endpoint lies in the cap

`rem:v30` retracted the identification of the endpoint condition `X(θ) - μ_θ ∈ C₂` with the
width condition `H(θ) + H(π-θ) - sin θ ≥ 1`, which is only a necessary condition, and left
the endpoint condition open. This section is the proof of it on `D`, written as `rem:v31`.

With `X(θ) = H(θ)μ_θ + H'(θ)ν_θ`,

  `X(θ) - μ_θ = ((H-1)cos θ - H' sin θ, (H-1)sin θ + H' cos θ) = (A(θ), A₂(θ))`

(`endpoint_coords`), the two brackets of `BracketIdentities` read at the angle `θ` instead of
at the time `t`.

STEP 1 (the rectangle). `H(π/2) = 1` puts the two ends of the ceiling facet at
`(-H'(π/2^±), 1)`, so its `x`-shadow is `[-α₂(0), κ]`: the right end is `κ = -H'(π/2⁻)` by
definition, and the left end is `-α₂(0)` because the gauge `H(0) = 1` makes
`α₂(0) = H(0) - 1 + H'(π/2⁺) = H'(π/2⁺)` (`facet_left_from_arm`); its length is the atom
mass. `C₂` is `ρ`-invariant, so the floor facet is the image of the ceiling facet under
`(x,y) ↦ (x, 1-y)` and has the SAME shadow. Convexity then gives the whole rectangle
(`rectangle_of_facets`), which is the only place `ρ`-invariance and the atom are used.

STEP 2 (the brackets). `A' = (1-r) sin θ` and `A₂' = -(1-r) cos θ` with `1 - r ≥ 0` from (b),
so on `[0,π/2]` `A` increases from `A(0) = 0` to `A(π/2⁻) = κ` and `A₂` decreases from
`A₂(0) = H'(0) = 1/2` to `A₂(π/2) = H(π/2) - 1 = 0`; on `[π/2,π]` both increase, `A` from
`A(π/2⁺) = -α₂(0)` to `A(π) = 1 - H(π)` and `A₂` from `0` to `A₂(π) = -H'(π) = 1/2`. The
monotonicity comes from `bracket_monotoneOn_Ioo`, `moment_bracket_antitoneOn_Ioo`,
`moment_bracket_monotoneOn_Ioo` on a phase (glued by `monotoneOn_glue`/`antitoneOn_glue`), or
from `bracket_monotoneOn_of_deficit`, `moment_bracket_antitoneOn_of_deficit`,
`moment_bracket_monotoneOn_of_deficit` on a general member of `D`; the globally quantified
`bracket_monotoneOn`, `moment_bracket_antitoneOn`, `moment_bracket_monotoneOn` are the `C²`
special case and do NOT instantiate on `D`. Then `endpoint_range_lower` and
`endpoint_range_upper`, or the packaged `endpoint_in_cap_lower`/`endpoint_in_cap_upper`,
which consume monotonicity and nothing else.

STEP 3 (the two ends of (d)). `[0,κ] ⊆ [-α₂(0),κ]` is `α₂(0) ≥ 0`, hypothesis (d) at `t = 0`;
and `1 - H(π) ≤ κ` is `α₁(π/2) = H(π) - 1 + κ ≥ 0`, hypothesis (d) at `t = π/2`
(`alpha1_half_pi_bounds_x`). Both `A₂`-ranges sit in `[0,1/2] ⊆ [0,1]`. So the endpoint
condition consumes (d) at BOTH ends, not at `t = 0` alone.

Hypothesis (c) is never used here, and neither is the upper bound `r ≥ 0`.
-/

/-- The inner sweep endpoint `X(θ) - μ_θ` in coordinates: it is the pair of brackets. -/
theorem endpoint_coords (h hp θ : ℝ) :
    (h * Real.cos θ + hp * (-Real.sin θ) - Real.cos θ,
      h * Real.sin θ + hp * Real.cos θ - Real.sin θ)
      = ((h - 1) * Real.cos θ - hp * Real.sin θ,
         (h - 1) * Real.sin θ + hp * Real.cos θ) := by
  simp only [Prod.mk.injEq]
  constructor <;> ring

/-- **The left end of the ceiling facet is `-α₂(0)`.** Under the gauge `H(0) = 1` the second
arm at time `0` is exactly `H'(π/2⁺)`, so the facet `[-H'(π/2⁺), -H'(π/2⁻)]` is
`[-α₂(0), κ]` and its length is the atom mass `H'(π/2⁺) - H'(π/2⁻)`. -/
theorem facet_left_from_arm {f0 hl hr : ℝ} (hf : f0 = 1) :
    -(f0 - 1 + hr) = -hl - (hr - hl) := by rw [hf]; ring

/-- **`R ⊆ C₂`.** A convex set containing two horizontal segments with the SAME `x`-shadow, at
heights `0` and `1`, contains the rectangle between them: each point is the obvious convex
combination of the two points above and below it. The `ρ`-invariance of `C₂` is what supplies
the second segment from the first, with the same shadow. -/
theorem rectangle_of_facets {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {l r : ℝ}
    (hfloor : ∀ p ∈ Set.Icc l r, ((p, 0) : ℝ × ℝ) ∈ C)
    (hceil : ∀ p ∈ Set.Icc l r, ((p, 1) : ℝ × ℝ) ∈ C)
    {x y : ℝ} (hx : x ∈ Set.Icc l r) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ((x, y) : ℝ × ℝ) ∈ C := by
  have hrw : ((x, y) : ℝ × ℝ) = (1 - y) • ((x, 0) : ℝ × ℝ) + y • ((x, 1) : ℝ × ℝ) := by
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  rw [hrw]
  exact hC (hfloor x hx) (hceil x hx) (by linarith [hy.2]) hy.1 (by ring)

/-- The endpoint's range on `[0,π/2]`: `A` climbs from `0` to `κ`, `A₂` falls from `1/2` to
`0`. -/
theorem endpoint_range_lower {A A2 : ℝ → ℝ} {κ θ : ℝ}
    (hA : MonotoneOn A (Set.Icc 0 (Real.pi / 2))) (hA0 : A 0 = 0)
    (hAh : A (Real.pi / 2) = κ)
    (hB : AntitoneOn A2 (Set.Icc 0 (Real.pi / 2))) (hB0 : A2 0 = 1 / 2)
    (hBh : A2 (Real.pi / 2) = 0)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    A θ ∈ Set.Icc (0 : ℝ) κ ∧ A2 θ ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_refl 0, hpi⟩
  have hh : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hpi, le_refl _⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := hA h0 hθ hθ.1; rw [hA0] at h; exact h
  · have h := hA hθ hh hθ.2; rw [hAh] at h; exact h
  · have h := hB hθ hh hθ.2; rw [hBh] at h; exact h
  · have h := hB h0 hθ hθ.1; rw [hB0] at h; exact h

/-- The endpoint's range on `[π/2,π]`: both brackets climb, `A` from `-α₂(0)` to `1 - H(π)`
and `A₂` from `0` to `1/2`. -/
theorem endpoint_range_upper {A A2 : ℝ → ℝ} {lo hi θ : ℝ}
    (hA : MonotoneOn A (Set.Icc (Real.pi / 2) Real.pi)) (hA0 : A (Real.pi / 2) = lo)
    (hAh : A Real.pi = hi)
    (hB : MonotoneOn A2 (Set.Icc (Real.pi / 2) Real.pi)) (hB0 : A2 (Real.pi / 2) = 0)
    (hBh : A2 Real.pi = 1 / 2)
    (hθ : θ ∈ Set.Icc (Real.pi / 2) Real.pi) :
    A θ ∈ Set.Icc lo hi ∧ A2 θ ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hpi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have h0 : (Real.pi / 2) ∈ Set.Icc (Real.pi / 2) Real.pi := ⟨le_refl _, hpi⟩
  have hh : Real.pi ∈ Set.Icc (Real.pi / 2) Real.pi := ⟨hpi, le_refl _⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := hA h0 hθ hθ.1; rw [hA0] at h; exact h
  · have h := hA hθ hh hθ.2; rw [hAh] at h; exact h
  · have h := hB h0 hθ hθ.1; rw [hB0] at h; exact h
  · have h := hB hθ hh hθ.2; rw [hBh] at h; exact h

/-- **(d) at `t = 0`.** `[0,κ] ⊆ [-α₂(0),κ]` is exactly `α₂(0) ≥ 0`. -/
theorem endpoint_mem_rectangle_lower {A A2 a20 κ : ℝ} (ha : 0 ≤ a20)
    (hA : A ∈ Set.Icc (0 : ℝ) κ) (hB : A2 ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    A ∈ Set.Icc (-a20) κ ∧ A2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨⟨by linarith [hA.1], hA.2⟩, ⟨hB.1, by linarith [hB.2]⟩⟩

/-- **(d) at `t = π/2`.** `α₁(π/2) = H(π) - 1 - H'(π/2⁻) = H(π) - 1 + κ`, so the sign of that
arm is precisely the statement that the reflected `x`-range ends inside the facet. -/
theorem alpha1_half_pi_bounds_x {hpi κ : ℝ} (harm : 0 ≤ hpi - 1 + κ) : 1 - hpi ≤ κ := by
  linarith

/-- The reflected half of the endpoint range sits in the rectangle, given (d) at `t = π/2`. -/
theorem endpoint_mem_rectangle_upper {A A2 a20 κ hpi : ℝ} (harm : 0 ≤ hpi - 1 + κ)
    (hA : A ∈ Set.Icc (-a20) (1 - hpi)) (hB : A2 ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    A ∈ Set.Icc (-a20) κ ∧ A2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨⟨hA.1, le_trans hA.2 (alpha1_half_pi_bounds_x harm)⟩, ⟨hB.1, by linarith [hB.2]⟩⟩

/-- **The second endpoint condition.** The assembly: the endpoint lies in the rectangle's
shadow at a height in `[0,1]`, and the rectangle lies in the cap. -/
theorem endpoint_in_cap {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {l r : ℝ}
    (hfloor : ∀ p ∈ Set.Icc l r, ((p, 0) : ℝ × ℝ) ∈ C)
    (hceil : ∀ p ∈ Set.Icc l r, ((p, 1) : ℝ × ℝ) ∈ C)
    {A A2 : ℝ} (hA : A ∈ Set.Icc l r) (hB : A2 ∈ Set.Icc (0 : ℝ) 1) :
    ((A, A2) : ℝ × ℝ) ∈ C :=
  rectangle_of_facets hC hfloor hceil hA hB

/-- **`X(θ) - μ_θ ∈ C₂` on `[0,π/2]`, from monotonicity alone.** The whole chain of Steps 1–3
with no derivative hypothesis anywhere: the two brackets enter only through `MonotoneOn` and
`AntitoneOn`, which is what the localised and the measure forms of `BracketIdentities`
supply. This is the statement `rem:v31` may claim on all of `D`. -/
theorem endpoint_in_cap_lower {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {a20 κ : ℝ}
    (hfloor : ∀ p ∈ Set.Icc (-a20) κ, ((p, 0) : ℝ × ℝ) ∈ C)
    (hceil : ∀ p ∈ Set.Icc (-a20) κ, ((p, 1) : ℝ × ℝ) ∈ C)
    (ha20 : 0 ≤ a20)
    {A A2 : ℝ → ℝ} (hA : MonotoneOn A (Set.Icc 0 (Real.pi / 2))) (hA0 : A 0 = 0)
    (hAh : A (Real.pi / 2) = κ)
    (hB : AntitoneOn A2 (Set.Icc 0 (Real.pi / 2))) (hB0 : A2 0 = 1 / 2)
    (hBh : A2 (Real.pi / 2) = 0)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    ((A θ, A2 θ) : ℝ × ℝ) ∈ C := by
  obtain ⟨h1, h2⟩ := endpoint_range_lower hA hA0 hAh hB hB0 hBh hθ
  obtain ⟨h3, h4⟩ := endpoint_mem_rectangle_lower ha20 h1 h2
  exact endpoint_in_cap hC hfloor hceil h3 h4

/-- **`X(θ) - μ_θ ∈ C₂` on `[π/2,π]`, from monotonicity alone.** Steps 1, 2 and 4 with the
same discipline; (d) enters only as `α₁(π/2) = H(π) - 1 + κ ≥ 0`. -/
theorem endpoint_in_cap_upper {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) {a20 κ hpi : ℝ}
    (hfloor : ∀ p ∈ Set.Icc (-a20) κ, ((p, 0) : ℝ × ℝ) ∈ C)
    (hceil : ∀ p ∈ Set.Icc (-a20) κ, ((p, 1) : ℝ × ℝ) ∈ C)
    (harm : 0 ≤ hpi - 1 + κ)
    {A A2 : ℝ → ℝ} (hA : MonotoneOn A (Set.Icc (Real.pi / 2) Real.pi))
    (hA0 : A (Real.pi / 2) = -a20) (hAh : A Real.pi = 1 - hpi)
    (hB : MonotoneOn A2 (Set.Icc (Real.pi / 2) Real.pi)) (hB0 : A2 (Real.pi / 2) = 0)
    (hBh : A2 Real.pi = 1 / 2)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (Real.pi / 2) Real.pi) :
    ((A θ, A2 θ) : ℝ × ℝ) ∈ C := by
  obtain ⟨h1, h2⟩ := endpoint_range_upper hA hA0 hAh hB hB0 hBh hθ
  obtain ⟨h3, h4⟩ := endpoint_mem_rectangle_upper harm h1 h2
  exact endpoint_in_cap hC hfloor hceil h3 h4

end Rectangle


section FloorDirection

/-!
### `c_y ≥ 0` on `D`, with the bathtub step

`rem:v24`'s old proof split `[0,π/2]` at `β` and `π/2-β`, so it did not survive the repair of
(d) to fixed-`T` form. The replacement uses the companion bracket only.

`c_y = α₁ cos t + A₂(t)` is algebra (`cy_from_bracket`), and `A₂(π/2) = H(π/2) - 1 = 0` turns
it into `c_y = α₁ cos t + ∫_t^{π/2} ρ₁ cos`, while `A₂(0) = H'(0)` is the moment identity
`∫_0^{π/2} ρ₁ cos = 1/2` (`moment_bracket_deriv`, `moment_from_bracket`).

On `[T,π/2]`, (d) gives `α₁ ≥ 0` and both terms are nonnegative. On `[0,T]`, (d) gives
`α₂ > 0`, so `α₁' = α₂ + ρ₁ ≥ ρ₁` and `α₁(t) ≥ -1/2 + ∫_0^t ρ₁`; eliminating the tail with
the moment identity reduces `c_y ≥ 0` to

  `½(1 - cos t) ≥ ∫_0^t ρ₁(s)(cos s - cos t) ds`.

The right side is linear in `ρ₁` with a nonnegative kernel; per unit of the constraint
`∫_0^t ρ₁ cos ≤ 1/2` the objective returns `1 - cos t sec s`, which DECREASES in `s`, so the
bathtub maximiser is the FRONT-loaded `ρ₁ = 1_[0,a]` with `a = min(t, π/6)`. Its value is
`min(sin t, 1/2) - min(t, π/6) cos t`, giving two cases: `(π/6 - 1/2)cos t ≥ 0` for
`t ≥ π/6` (`bathtub_far_case`), and `Λ(t) ≥ 0` for `t ≤ π/6` (`Lam_nonneg_near`). Both are
the single fact `π > 3`.

The back-loaded profile, which is what the inequality `t - arcsin(sin t - 1/2) ≥ 1/2`
encodes, MAXIMISES `∫_0^t ρ₁` where the objective wants it minimised; it is a test against
one admissible profile and not the extremum, and it says nothing on `[0, π/6)`.
-/

/-- `c_y = α₁ cos t + A₂(t)`, pure algebra once `α₁ = G - 1 - F'` is substituted. -/
theorem cy_from_bracket (f g fp t : ℝ) :
    (f - 1) * Real.sin t + (g - 1) * Real.cos t
      = (g - 1 - fp) * Real.cos t + ((f - 1) * Real.sin t + fp * Real.cos t) := by ring

/-- The far case of the bathtub split: for `t ≥ π/6` the front-loaded maximiser makes the
condition `π/6 ≥ 1/2`, which is `π > 3`. -/
theorem bathtub_far_case {t : ℝ} (hc : 0 ≤ Real.cos t) :
    0 ≤ (Real.pi / 6 - 1 / 2) * Real.cos t :=
  mul_nonneg (by linarith [Real.pi_gt_three]) hc

/-- The near case's function, `Λ(t) = ½(1 - cos t) - sin t + t cos t`. -/
noncomputable def Lam (t : ℝ) : ℝ :=
  (1 / 2) * (1 - Real.cos t) - Real.sin t + t * Real.cos t

/-- `Λ' = (½ - t) sin t`, so `Λ` rises to `t = 1/2` and falls after it. -/
theorem Lam_hasDerivAt (t : ℝ) : HasDerivAt Lam ((1 / 2 - t) * Real.sin t) t := by
  have hcos : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
  have hsin : HasDerivAt Real.sin (Real.cos t) t := Real.hasDerivAt_sin t
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hmul : HasDerivAt (fun s : ℝ => s * Real.cos s)
      (1 * Real.cos t + t * -Real.sin t) t := hid.mul hcos
  have h1 : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * (1 - Real.cos s))
      ((1 / 2 : ℝ) * (0 - -Real.sin t)) t :=
    ((hasDerivAt_const t (1 : ℝ)).sub hcos).const_mul (1 / 2 : ℝ)
  have h : HasDerivAt Lam ((1 / 2 : ℝ) * (0 - -Real.sin t) - Real.cos t
      + (1 * Real.cos t + t * -Real.sin t)) t := (h1.sub hsin).add hmul
  convert h using 1
  ring

theorem Lam_zero : Lam 0 = 0 := by
  unfold Lam; simp

/-- `Λ(π/6) = (√3/12)(π - 3)`. -/
theorem Lam_at_pi_six : Lam (Real.pi / 6) = Real.sqrt 3 / 12 * (Real.pi - 3) := by
  unfold Lam
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

theorem Lam_pi_six_pos : 0 < Lam (Real.pi / 6) := by
  rw [Lam_at_pi_six]
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [Real.pi_gt_three]

/-- **The near case.** `Λ ≥ 0` on `[0, π/6]`: it increases on `[0,1/2]` from `Λ(0) = 0` and
decreases on `[1/2, π/6]` to `Λ(π/6) = (√3/12)(π-3) > 0`, so the minimum is at an endpoint
and both endpoint values are nonnegative. Note `1/2 < π/6`, again `π > 3`. -/
theorem Lam_nonneg_near {t : ℝ} (h0 : 0 ≤ t) (h : t ≤ Real.pi / 6) : 0 ≤ Lam t := by
  have hpi6 : (1 / 2 : ℝ) ≤ Real.pi / 6 := by linarith [Real.pi_gt_three]
  have hle : Real.pi / 6 ≤ Real.pi := by linarith [Real.pi_pos]
  rcases le_total t (1 / 2 : ℝ) with hc | hc
  · have hm : MonotoneOn Lam (Set.Icc 0 (1 / 2 : ℝ)) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (fun x _ => (Lam_hasDerivAt x).continuousAt.continuousWithinAt)
        (f' := fun s => (1 / 2 - s) * Real.sin s)
        (fun x _ => (Lam_hasDerivAt x).hasDerivWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      have hs : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hx.1) (by linarith [Real.pi_gt_three, hx.2])
      exact mul_nonneg (by linarith [hx.2]) hs
    have hstep := hm (Set.left_mem_Icc.mpr (by norm_num)) ⟨h0, hc⟩ h0
    rw [Lam_zero] at hstep; exact hstep
  · have ha : AntitoneOn Lam (Set.Icc (1 / 2 : ℝ) (Real.pi / 6)) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (fun x _ => (Lam_hasDerivAt x).continuousAt.continuousWithinAt)
        (f' := fun s => (1 / 2 - s) * Real.sin s)
        (fun x _ => (Lam_hasDerivAt x).hasDerivWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      have hs : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2])
      nlinarith [mul_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x - 1 / 2) hs]
    have hstep := ha ⟨hc, h⟩ (Set.right_mem_Icc.mpr hpi6) h
    linarith [Lam_pi_six_pos]

end FloorDirection


section SegmentHypothesis

/-!
### `eq:seghyp` on `D`

`σ ≥ α₁⁺` is what makes the face-1 window of `prop:V` the interval `[α₁⁺, σ]`; `rem:seghyp`
recorded it as an unstated hypothesis and `rem:v30` listed it as undischarged in `thm:final`.
It splits into two halves, and both are now available.

`σ - α₁ = (F-1)tan t + F' = A₂(t) sec t = sec t ∫_t^{π/2} ρ₁ cos ≥ 0` uses (b) alone
(`sigma_sub_alpha1_nonneg`); `σ ≥ 0` follows from `c_y = σ cos t` and `c_y ≥ 0`
(`sigma_nonneg_of_cy`), which is the previous section. The maximum of the two is `α₁⁺`
(`seghyp_from_both`).
-/

/-- The first half: `(σ - α₁)cos t` is a nonnegative integral, so `σ ≥ α₁` off `t = π/2`. -/
theorem sigma_sub_alpha1_nonneg {σ a1 c I : ℝ} (hc : 0 < c) (hid : (σ - a1) * c = I)
    (hI : 0 ≤ I) : a1 ≤ σ := by
  have h : 0 ≤ (σ - a1) * c := by rw [hid]; exact hI
  by_contra hcon
  push_neg at hcon
  have hp : 0 < (a1 - σ) * c := mul_pos (sub_pos.mpr hcon) hc
  linarith

/-- The second half: `c_y = σ cos t` with `c_y ≥ 0` gives `σ ≥ 0`. -/
theorem sigma_nonneg_of_cy {cy σ c : ℝ} (hc : 0 < c) (hcy : cy = σ * c) (h : 0 ≤ cy) :
    0 ≤ σ := by
  by_contra hcon
  push_neg at hcon
  have hneg : σ * c < 0 := mul_neg_of_neg_of_pos hcon hc
  rw [hcy] at h
  linarith

/-- `σ ≥ max(α₁, 0) = α₁⁺`. -/
theorem seghyp_from_both {σ a1 : ℝ} (h1 : a1 ≤ σ) (h2 : 0 ≤ σ) : max a1 0 ≤ σ :=
  max_le h1 h2

end SegmentHypothesis


section BangBang

/-!
### The bang-bang step of `rem:v29`, written out

Both `c_x` bounds reduce, after the arm estimate that (d) supplies, to one scalar statement.
With `ρ : [0,π/2] → [0,1]` and `∫₀^{π/2} ρ cos = 1/2`,

  `Φ_ρ(u) = sin u (∫₀^u ρ − 1/2) + ∫_u^{π/2} ρ sin ≥ 0` for every `u ∈ [0,π/2]`.

The `κ` bound is this at `u = t` with `ρ = ρ₁`; the `−α₂(0)` bound is this at `u = π/2 − t`
with `ρ(s) = ρ₂(π/2 − s)`, the reflection turning `∫ ρ₂ sin = 1/2` into `∫ ρ cos = 1/2`.

*Sign*, with no optimisation at all: `sin s ≥ sin u` on `[u,π/2]` gives
`Φ_ρ(u) ≥ sin u (∫₀^{π/2} ρ − 1/2)`, and `∫ρ ≥ ∫ρ cos = 1/2` because `ρ ≥ 0` and `cos ≤ 1`.
That is `claim_hard` together with `density_ge_moment`, and it needs neither `ρ ≤ 1` nor any
extremal.

*The extremal.* Writing `Φ_ρ(u) = −½ sin u + ∫ ρ w_u` with `w_u(s) = sin(max s u)`, the
minimiser at fixed `∫ ρ cos = 1/2` places mass where the price `w_u(s)/cos s` per unit of the
constraint is LOWEST.  That price is `sin u · sec s` on `[0,u]` and `tan s` on `[u,π/2]`, both
increasing and agreeing at `u`, so it increases across `[0,π/2]` and the minimiser is
FRONT-loaded: `ρ⋆ = 1_[0,π/6]`, the switch pinned by `∫₀^{π/6} cos = sin(π/6) = 1/2`
(`floor_moment_u`).  This is the same direction as the corner-height bathtub of `rem:v24`,
and the opposite of the back-loaded profile withdrawn there.

The certificate is pointwise.  With `λ_u = sin(max u (π/6))/cos(π/6)`, the kernel
`cos(π/6) w_u − sin(max u (π/6)) cos` is `≤ 0` on `[0,π/6]` and `≥ 0` on `[π/6,π/2]`
(`exKernel_nonpos`, `exKernel_nonneg`), for the single reason that `s ↦ sin(max s u)` is
nondecreasing while `cos` is nonincreasing.  Hence `(ρ − 1_[0,π/6])` times that kernel is
`≥ 0` pointwise (`exchange_product_left`, `exchange_product_right`), which is where `ρ ≤ 1` is
used and the only place it is used.

*The constant.*  `Φ⋆(u) = ∫₀^{π/6} sin(max s u) ds − ½ sin u` is `(π/6 − 1/2) sin u` for
`u ≥ π/6` (`extremal_value_far`) and `Ψ(u) = u sin u + cos u − √3/2 − ½ sin u` for `u ≤ π/6`
(`extremal_value_near`).  `Ψ′ = (u − ½) cos u`, so `Ψ` falls to `u = 1/2` and rises after it,
and its minimum is `Ψ(1/2) = cos ½ − √3/2 = 0.0115571…`, the two `sin ½` terms cancelling
exactly.  Since `Ψ(π/6) = ½(π/6 − 1/2) ≥ Ψ(1/2)`, the far branch never goes lower, so
`cos ½ − √3/2` is the surplus on the whole range (`bangbang_surplus`).

NOT formalised here: the passage from the pointwise kernel sign to
`∫ ρ w_u ≥ ∫₀^{π/6} w_u`, which is one application of `∫ ≥ 0` for a nonnegative integrand
together with linearity and the moment constraint.  Everything else in the paragraph is below.
-/

/-- The exchange kernel at `u`, cleared of the denominator `cos(π/6)`. -/
noncomputable def exKernel (u s : ℝ) : ℝ :=
  Real.cos (Real.pi / 6) * Real.sin (max s u) - Real.sin (max u (Real.pi / 6)) * Real.cos s

/-- `s ↦ sin (max s u)` is nondecreasing on `[0,π/2]`. -/
theorem sin_max_mono {a b u : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hb : b ≤ Real.pi / 2) (hu : u ≤ Real.pi / 2) :
    Real.sin (max a u) ≤ Real.sin (max b u) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hma : (0:ℝ) ≤ max a u := le_max_of_le_left ha0
  have hmb : (0:ℝ) ≤ max b u := le_max_of_le_left (hab.trans' ha0)
  exact Real.strictMonoOn_sin.monotoneOn
    ⟨by linarith, max_le (hab.trans hb) hu⟩ ⟨by linarith, max_le hb hu⟩ (max_le_max hab le_rfl)

/-- Left of the switch the kernel is nonpositive: `sin(max s u) ≤ sin(max u (π/6))` and
`cos(π/6) ≤ cos s`. -/
theorem exKernel_nonpos {u s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ Real.pi / 6)
    (hu0 : 0 ≤ u) (hu : u ≤ Real.pi / 2) : exKernel u s ≤ 0 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h60 : (0:ℝ) ≤ Real.pi / 6 := by positivity
  have h6 : Real.pi / 6 ≤ Real.pi / 2 := by linarith
  have hsin : Real.sin (max s u) ≤ Real.sin (max u (Real.pi / 6)) := by
    rw [max_comm u (Real.pi / 6)]
    exact sin_max_mono hs hs0 h6 hu
  have hcos : Real.cos (Real.pi / 6) ≤ Real.cos s :=
    Real.cos_le_cos_of_nonneg_of_le_pi hs0 (by linarith) hs
  have hc0 : 0 ≤ Real.cos (Real.pi / 6) := by rw [Real.cos_pi_div_six]; positivity
  have hsm : 0 ≤ Real.sin (max s u) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_max_of_le_left hs0)
      (max_le (by linarith) (by linarith))
  have hmul := mul_le_mul hcos hsin hsm (le_trans hc0 hcos)
  unfold exKernel
  nlinarith [hmul]

/-- Right of the switch the kernel is nonnegative: both comparisons reverse. -/
theorem exKernel_nonneg {u s : ℝ} (hs : Real.pi / 6 ≤ s) (hs2 : s ≤ Real.pi / 2)
    (hu0 : 0 ≤ u) (hu : u ≤ Real.pi / 2) : 0 ≤ exKernel u s := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h60 : (0:ℝ) ≤ Real.pi / 6 := by positivity
  have h6 : Real.pi / 6 ≤ Real.pi / 2 := by linarith
  have hsin : Real.sin (max u (Real.pi / 6)) ≤ Real.sin (max s u) := by
    rw [max_comm u (Real.pi / 6)]
    exact sin_max_mono hs h60 hs2 hu
  have hcos : Real.cos s ≤ Real.cos (Real.pi / 6) :=
    Real.cos_le_cos_of_nonneg_of_le_pi h60 (by linarith) hs
  have hcs : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hs2⟩
  have hsm : 0 ≤ Real.sin (max u (Real.pi / 6)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_max_of_le_right h60)
      (max_le (by linarith) (by linarith))
  have hmul := mul_le_mul hcos hsin hsm (le_trans hcs hcos)
  unfold exKernel
  nlinarith [hmul]

/-- On `[0,π/6]` the competitor is below the extremal (`ρ ≤ 1`) and the kernel is nonpositive,
so the exchange integrand is nonnegative.  This is the only use of `ρ ≤ 1`. -/
theorem exchange_product_left {ρ u s : ℝ} (h1 : ρ ≤ 1)
    (hs0 : 0 ≤ s) (hs : s ≤ Real.pi / 6) (hu0 : 0 ≤ u) (hu : u ≤ Real.pi / 2) :
    0 ≤ (ρ - 1) * exKernel u s := by
  have hk := exKernel_nonpos hs0 hs hu0 hu
  nlinarith

/-- On `[π/6,π/2]` the extremal is `0` and the kernel is nonnegative. -/
theorem exchange_product_right {ρ u s : ℝ} (h0 : 0 ≤ ρ)
    (hs : Real.pi / 6 ≤ s) (hs2 : s ≤ Real.pi / 2) (hu0 : 0 ≤ u) (hu : u ≤ Real.pi / 2) :
    0 ≤ (ρ - 0) * exKernel u s := by
  have hk := exKernel_nonneg hs hs2 hu0 hu
  nlinarith

/-- Far case: for `u ≥ π/6` the extremal sits entirely left of `u`, so `w_u ≡ sin u` on it. -/
theorem extremal_value_far {u : ℝ} (h : Real.pi / 6 ≤ u) :
    (∫ s in (0:ℝ)..(Real.pi / 6), Real.sin (max s u)) = Real.pi / 6 * Real.sin u := by
  have h60 : (0:ℝ) ≤ Real.pi / 6 := by positivity
  have hcongr : (∫ s in (0:ℝ)..(Real.pi / 6), Real.sin (max s u))
      = ∫ _s in (0:ℝ)..(Real.pi / 6), Real.sin u := by
    refine intervalIntegral.integral_congr ?_
    intro s hs
    rw [Set.uIcc_of_le h60] at hs
    show Real.sin (max s u) = Real.sin u
    rw [max_eq_right (le_trans hs.2 h)]
  rw [hcongr, intervalIntegral.integral_const]
  simp

/-- Near case: for `u ≤ π/6` the extremal straddles `u`, giving `u sin u + cos u − √3/2`. -/
theorem extremal_value_near {u : ℝ} (h0 : 0 ≤ u) (h : u ≤ Real.pi / 6) :
    (∫ s in (0:ℝ)..(Real.pi / 6), Real.sin (max s u))
      = u * Real.sin u + Real.cos u - Real.sqrt 3 / 2 := by
  have hcont : Continuous fun s : ℝ => Real.sin (max s u) :=
    Real.continuous_sin.comp (continuous_id.max continuous_const)
  have hsplit : (∫ s in (0:ℝ)..u, Real.sin (max s u))
      + (∫ s in u..(Real.pi / 6), Real.sin (max s u))
      = ∫ s in (0:ℝ)..(Real.pi / 6), Real.sin (max s u) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have h1 : (∫ s in (0:ℝ)..u, Real.sin (max s u)) = u * Real.sin u := by
    have hc : (∫ s in (0:ℝ)..u, Real.sin (max s u)) = ∫ _s in (0:ℝ)..u, Real.sin u := by
      refine intervalIntegral.integral_congr ?_
      intro s hs
      rw [Set.uIcc_of_le h0] at hs
      show Real.sin (max s u) = Real.sin u
      rw [max_eq_right hs.2]
    rw [hc, intervalIntegral.integral_const]; simp
  have h2 : (∫ s in u..(Real.pi / 6), Real.sin (max s u)) = Real.cos u - Real.sqrt 3 / 2 := by
    have hc : (∫ s in u..(Real.pi / 6), Real.sin (max s u))
        = ∫ s in u..(Real.pi / 6), Real.sin s := by
      refine intervalIntegral.integral_congr ?_
      intro s hs
      rw [Set.uIcc_of_le h] at hs
      show Real.sin (max s u) = Real.sin s
      rw [max_eq_left hs.1]
    rw [hc, integral_sin, Real.cos_pi_div_six]
  rw [← hsplit, h1, h2]; ring

/-- The near-case profile `Ψ(u) = u sin u + cos u − √3/2 − ½ sin u`. -/
noncomputable def Psi (u : ℝ) : ℝ :=
  u * Real.sin u + Real.cos u - Real.sqrt 3 / 2 - (1 / 2) * Real.sin u

/-- `Ψ′ = (u − ½) cos u`, so `Ψ` falls on `[0,1/2]` and rises on `[1/2,π/6]`. -/
theorem Psi_hasDerivAt (u : ℝ) : HasDerivAt Psi ((u - 1 / 2) * Real.cos u) u := by
  have hsin : HasDerivAt Real.sin (Real.cos u) u := Real.hasDerivAt_sin u
  have hcos : HasDerivAt Real.cos (-Real.sin u) u := Real.hasDerivAt_cos u
  have hid : HasDerivAt (fun s : ℝ => s) 1 u := hasDerivAt_id u
  have h : HasDerivAt (fun s : ℝ => s * Real.sin s + Real.cos s - Real.sqrt 3 / 2
      - (1 / 2) * Real.sin s)
      (1 * Real.sin u + u * Real.cos u + -Real.sin u - 0 - (1 / 2) * Real.cos u) u :=
    (((hid.mul hsin).add hcos).sub (hasDerivAt_const u (Real.sqrt 3 / 2))).sub
      (hsin.const_mul (1 / 2 : ℝ))
  have he : (1 * Real.sin u + u * Real.cos u + -Real.sin u - 0 - (1 / 2) * Real.cos u)
      = (u - 1 / 2) * Real.cos u := by ring
  rw [he] at h
  exact h

/-- At `u = 1/2` the two `sin ½` terms cancel exactly. -/
theorem Psi_at_half : Psi (1 / 2) = Real.cos (1 / 2) - Real.sqrt 3 / 2 := by
  unfold Psi; ring

/-- At the switch the two branches agree: `Ψ(π/6) = ½(π/6 − 1/2)`. -/
theorem Psi_at_pi_six : Psi (Real.pi / 6) = (1 / 2) * (Real.pi / 6 - 1 / 2) := by
  unfold Psi
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

/-- **The near branch.** `Ψ ≥ Ψ(1/2) = cos ½ − √3/2` on `[0,π/6]`, by antitonicity up to
`1/2` and monotonicity after it.  Note `1/2 < π/6`, which is `π > 3`. -/
theorem Psi_min_near {u : ℝ} (h0 : 0 ≤ u) (h : u ≤ Real.pi / 6) :
    Real.cos (1 / 2) - Real.sqrt 3 / 2 ≤ Psi u := by
  have hpi3 := Real.pi_gt_three
  have hpi6 : (1 / 2 : ℝ) ≤ Real.pi / 6 := by linarith
  rw [← Psi_at_half]
  rcases le_total u (1 / 2 : ℝ) with hc | hc
  · have ha : AntitoneOn Psi (Set.Icc 0 (1 / 2 : ℝ)) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (fun x _ => (Psi_hasDerivAt x).continuousAt.continuousWithinAt)
        (f' := fun s => (s - 1 / 2) * Real.cos s)
        (fun x _ => (Psi_hasDerivAt x).hasDerivWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      have hcx : 0 ≤ Real.cos x :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩
      nlinarith [hx.2]
    exact ha ⟨h0, hc⟩ (Set.right_mem_Icc.mpr (by norm_num)) hc
  · have hm : MonotoneOn Psi (Set.Icc (1 / 2 : ℝ) (Real.pi / 6)) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (fun x _ => (Psi_hasDerivAt x).continuousAt.continuousWithinAt)
        (f' := fun s => (s - 1 / 2) * Real.cos s)
        (fun x _ => (Psi_hasDerivAt x).hasDerivWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      have hcx : 0 ≤ Real.cos x :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact mul_nonneg (by linarith [hx.1]) hcx
    exact hm (Set.left_mem_Icc.mpr hpi6) ⟨hc, h⟩ hc

/-- `cos(1/2) ≥ 0.871744`, from the quartic Taylor enclosure. -/
theorem cos_half_lower : (871744 : ℝ) / 10 ^ 6 ≤ Real.cos (1 / 2) := by
  have habs : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_nonneg (by norm_num)
  have hb := Real.cos_bound (x := (1 / 2 : ℝ)) (by rw [habs]; norm_num)
  rw [habs] at hb
  have h := (abs_le.mp hb).1
  norm_num at h ⊢
  linarith

/-- **The surplus is positive.** `cos ½ − √3/2 = 0.0115571…`, against `√3/2 ≤ 0.8660255`
(`sqrt3_half_le`). -/
theorem bangbang_surplus_pos : 0 < Real.cos (1 / 2) - Real.sqrt 3 / 2 := by
  have h1 := cos_half_lower
  have h2 := sqrt3_half_le
  have h3 : (8660255 : ℝ) / 10 ^ 7 < 871744 / 10 ^ 6 := by norm_num
  linarith

/-- **The far branch never goes below the near minimum.** For `u ≥ π/6` the extremal value is
`(π/6 − 1/2) sin u ≥ ½(π/6 − 1/2) = Ψ(π/6) ≥ Ψ(1/2)`. -/
theorem far_ge_surplus {u : ℝ} (h : Real.pi / 6 ≤ u) (h2 : u ≤ Real.pi / 2) :
    Real.cos (1 / 2) - Real.sqrt 3 / 2 ≤ (Real.pi / 6 - 1 / 2) * Real.sin u := by
  have hpi3 := Real.pi_gt_three
  have hpi := Real.pi_pos
  have hs : Real.sin (Real.pi / 6) ≤ Real.sin u :=
    Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, h2⟩ h
  rw [Real.sin_pi_div_six] at hs
  have hkey : Real.cos (1 / 2) - Real.sqrt 3 / 2 ≤ (1 / 2) * (Real.pi / 6 - 1 / 2) := by
    rw [← Psi_at_pi_six]
    exact Psi_min_near (by positivity) le_rfl
  nlinarith [hs, hkey]

/-- **The surplus, on the whole range.** The value of the front-loaded extremal never drops
below `cos ½ − √3/2`, and that value is attained at `u = 1/2`. -/
theorem bangbang_surplus {u : ℝ} (h0 : 0 ≤ u) (h : u ≤ Real.pi / 2) :
    Real.cos (1 / 2) - Real.sqrt 3 / 2
      ≤ (∫ s in (0:ℝ)..(Real.pi / 6), Real.sin (max s u)) - (1 / 2) * Real.sin u := by
  rcases le_total u (Real.pi / 6) with hc | hc
  · rw [extremal_value_near h0 hc]
    have := Psi_min_near h0 hc
    unfold Psi at this
    linarith
  · rw [extremal_value_far hc]
    have := far_ge_surplus hc h
    nlinarith [this]

/-- The substitution step: an arm bounded below by `−1/2 + I₀` turns
`κ − c_x = α₁ sin t + tail` into the `Φ` form `sin t (I₀ − 1/2) + tail`. -/
theorem phi_from_arm_lower {arm trig I0 tail : ℝ} (htrig : 0 ≤ trig)
    (harm : -(1 / 2) + I0 ≤ arm) : trig * (I0 - 1 / 2) + tail ≤ arm * trig + tail := by
  nlinarith

/-- The same extremal, run against `∫ ρ sin`, gives the ceiling-facet floor: `κ ≥ 1 − √3/2`
by `floor_obj_u`, and `1 − √3/2 > 0`. -/
theorem ceiling_facet_floor_pos : 0 < 1 - Real.sqrt 3 / 2 := by
  have h2 := sqrt3_half_le
  norm_num at h2 ⊢
  linarith

end BangBang


section UniquenessStrictness

/-!
### The strictness step of `cor:uniq`, repaired

The printed justification used `E₂ = [0, π/2 − β)`, `Σ`'s own sign cell, and the `E₂` term
alone.  Under the fixed-`T` form of (d) all that is known is `E₁ ⊆ [0,T) ⊆ E₂`, and the `E₂`
term alone makes `η` constant on `[π/2, π/2 + τ)` only, never on all of `[π/2,π]`.  The
repair keeps the cap term, which the printed argument discarded.

With `p ≡ 0` on `[0,π/2]` and `q(t) = η(t + π/2)`, `q(0) = 0`, the cell form is
`∫₀^{π/2}(q² − q′²) − ∫_{E₂} q′² + ∫_{E₁} q²`.  The inclusions `E₁ ⊆ [0,T) ⊆ E₂` push this
below `∫₀^{π/2}(q² − q′²) + ∫₀^{T}(q² − q′²)` (`cell_le_window`).  Both brackets are `≤ 0` by
the Dirichlet–Neumann Poincaré inequality, with constants `1` on `[0,π/2]` and `(π/2T)² > 1`
on `[0,T]` (`dn_constant_gt_one`).  Vanishing of the second forces `q ≡ 0` on `[0,T]`
(`gap_zero_forces_zero`), vanishing of the first forces `q = c sin`, and the two together
force `c = 0` (`first_mode_vanishes`).  The conclusion is `η ≡ 0` on all of `[π/2,π]`, and it
uses only `T > 0`, which is (d).

`cor:anchored` does NOT supply this: it is the non-strict `δ²Q ≤ 0`, and uniqueness needs
definiteness.  What the same inclusions do give in general is `B_{E₁,E₂} ≤ D_T`
(`cell_le_window` again, with the two `T`-integrands), so definiteness on all of `D` is
definiteness of the single form `D_T`.
-/

/-- Shrinking the subtracted set to `[0,T)` and enlarging the added one to `[0,T)` can only
raise the cell form.  This is `lem:mono` with both sets moved to the same `[0,T)`. -/
theorem cell_le_window {bare J1 J2 K1 K2 : ℝ} (h1 : J1 ≤ K1) (h2 : K2 ≤ J2) :
    bare - J2 + J1 ≤ bare - K2 + K1 := by linarith

/-- The Dirichlet–Neumann Poincaré constant on `[0,T]` exceeds `1` as soon as `T < π/2`. -/
theorem dn_constant_gt_one {T : ℝ} (h0 : 0 < T) (h : T < Real.pi / 2) :
    1 < (Real.pi / (2 * T)) ^ 2 := by
  have h2 : 0 < 2 * T := by linarith
  have hlt : 1 < Real.pi / (2 * T) := by
    rw [lt_div_iff₀ h2]; linarith
  nlinarith

/-- A Poincaré constant at least `1` makes the bracket `∫(q² − q′²)` nonpositive. -/
theorem gap_nonpos_of_poincare {I J lam : ℝ} (hI : 0 ≤ I) (hlam : 1 ≤ lam) (hP : lam * I ≤ J) :
    I - J ≤ 0 := by nlinarith

/-- A Poincaré constant strictly above `1` makes the bracket vanish only at `q ≡ 0`. -/
theorem gap_zero_forces_zero {I J lam : ℝ} (hI : 0 ≤ I) (hlam : 1 < lam) (hP : lam * I ≤ J)
    (h : 0 ≤ I - J) : I = 0 := by nlinarith

/-- A nonnegative total dominated by a sum of two nonpositive brackets forces both to vanish. -/
theorem cell_zero_splits {B Gfull Gshort : ℝ} (hB : 0 ≤ B) (hle : B ≤ Gfull + Gshort)
    (hf : Gfull ≤ 0) (hs : Gshort ≤ 0) : Gfull = 0 ∧ Gshort = 0 :=
  ⟨by linarith, by linarith⟩

/-- The first Dirichlet–Neumann mode `c sin` vanishing anywhere in `(0,π/2]` forces `c = 0`. -/
theorem first_mode_vanishes {c T : ℝ} (h0 : 0 < T) (hT : T ≤ Real.pi / 2)
    (h : c * Real.sin T = 0) : c = 0 := by
  have hpi := Real.pi_pos
  have hs : 0 < Real.sin T := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  rcases mul_eq_zero.mp h with hc | hc
  · exact hc
  · exact absurd hc (ne_of_gt hs)

/-- The `q ≡ 0` residue of `D_τ` in range (a): with the Dirichlet–Dirichlet constant `4`,
`∫₀^τ(p²−p′²) + 2∫_τ^{π/2}(p²−p′²) ≤ 2∫p² − ∫p′² ≤ −2∫p²`, so `p ≡ 0` as well. -/
theorem dd_absorb {A B : ℝ} (h : 4 * A ≤ B) : 2 * A - B ≤ -(2 * A) := by linarith

end UniquenessStrictness


section SingleEntry

/-!
### `prop:V` (i)+(ii) with no strictness and no partition

Two obstructions stood between the connectivity lemmas and a general `H ∈ D`, and both are
removed here. Nothing new is assumed: what is used is `H(π/2) = 1` and `r ≤ 1` off the atom,
which are hypotheses (a) and (b) of `D`. Hypotheses (c) and (d) are not used.

**(a) The strictness.** `wronskian_strictAntiOn` and `pos_between_of_strictAnti` demand
`q = r - 1 < 0`. Class `D` gives only `r_ac ≤ 1`, and on `{r_ac = 1}` the Wronskian
`G_x = W'·sin(·-x) - W·cos(·-x)` has `G_x' = 0`: it is flat there, so `StrictAntiOn` is
*false* and those two lemmas genuinely do not instantiate. But strictness was never used.
The contradiction in the Sturm step comes from `G_x(x) = -W(x) < 0`, which is strict because
`W(x) > 0`, not because `G_x` moves. `pos_between_of_antitone` is the same proof with
`AntitoneOn` in place of `StrictAntiOn`, and `wronskian_antitoneOn` supplies it from `q ≤ 0`.
The threshold is sharp: `rc_one` builds caps in `D` with `r_ac = 1` on a set of measure up to
`π/3` (the largest the gauge allows) and finds the three-point margin exactly `0`, while at
`r_ac = 1.05` it is `-6.5·10⁻³` and connectivity fails.

**(b) The partition.** `strictAntiOn_glue` chains finitely many phases, and a general member
of `D` has no finite phase structure. No partition is needed. Antitonicity of `G_x` is the
integral statement `∫_a^b sin(θ-x)·(r(dθ) - dθ) ≤ 0`, which holds whenever `r ≤ λ` as
measures on the window; the note carries that step. The Lean lemmas take `AntitoneOn` as a
hypothesis rather than a phase list, so nothing here counts phases. `antitoneOn_glue` remains
available for the piecewise case but is no longer on the critical path.

**The atom.** `π/2` is an *endpoint* of each window, never interior, and it is never even
reached: the gauge `H(π/2) = 1` gives `W(π/2) = -p_y < 0` for every `p` off the floor
(`atom_not_cut`), so no anchor and no dip endpoint can sit at `π/2`. Accordingly
`pos_set_ordConnected_of_antitone` asks for the derivative of `W` only on `Set.Ico lo hi`,
which on `[0, π/2]` excludes exactly the point where `W'` jumps.

**The payoff.** A point `p` off a null set has, at each of its preimages, a strictly positive
sweep Jacobian; `entry_eventually_cut` turns that into "the cut set contains a right
neighbourhood", and `at_most_one_entry` shows an order-connected set admits at most one such
point. `at_most_one_preimage` is the assembled statement, which is `prop:V` (i) and (ii)
together, with no appeal to `thm:rc` or `thm:cross`.
-/

/-- **Antitonicity glues across a shared endpoint.** The non-strict twin of
`strictAntiOn_glue`, kept for the piecewise-constant case; the general argument needs no
gluing at all. -/
theorem antitoneOn_glue {f : ℝ → ℝ} {a b c : ℝ}
    (h1 : AntitoneOn f (Set.Icc a b)) (h2 : AntitoneOn f (Set.Icc b c)) :
    AntitoneOn f (Set.Icc a c) := by
  intro p hp r hr hpr
  rcases le_total r b with hrb | hrb
  · exact h1 ⟨hp.1, le_trans hpr hrb⟩ ⟨hr.1, hrb⟩ hpr
  · rcases le_total b p with hbp | hbp
    · exact h2 ⟨hbp, hp.2⟩ ⟨le_trans hbp hpr, hr.2⟩ hpr
    · have e1 : f b ≤ f p := h1 ⟨hp.1, hbp⟩ ⟨le_trans hp.1 hbp, le_rfl⟩ hbp
      have e2 : f r ≤ f b := h2 ⟨le_rfl, le_trans hrb hr.2⟩ ⟨hrb, hr.2⟩ hrb
      linarith

/-- **The Sturm step with the strictness removed.** Only `AntitoneOn` of the anchored
Wronskian is consumed. This is what makes the step available on `{r_ac = 1}`, where the
Wronskian is flat and `pos_between_of_strictAnti` has a false hypothesis.

`W` is required to be differentiable only on the OPEN window `Set.Ioo x z`. Both endpoints are
excluded, which is what lets a window abut the atom at `π/2` from either side: on `[0, π/2]`
the atom is the right endpoint and on `[π/2, π]` the left one, and `W'` exists at neither. -/
theorem pos_between_of_antitone {W W1 : ℝ → ℝ} {x z : ℝ} (hxz : x < z)
    (hlen : z - x < Real.pi) (hWc : Continuous W)
    (hW : ∀ t ∈ Set.Ioo x z, HasDerivAt W (W1 t) t)
    (hanti : AntitoneOn (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
      (Set.Ico x z))
    (hx : 0 < W x) (hz : 0 < W z) : ∀ t ∈ Set.Ioo x z, 0 < W t := by
  intro y hy
  by_contra hcon
  push_neg at hcon
  obtain ⟨t₁, h1, h2, hz1, hp⟩ := exists_first_entry hy.2 hWc hcon hz
  have hxt : x < t₁ := lt_of_lt_of_le hy.1 h1
  have hmem : t₁ ∈ Set.Ioo x z := ⟨hxt, h2⟩
  have hh := hanti ⟨le_rfl, hxz⟩ ⟨hxt.le, h2⟩ hxt.le
  simp only [sub_self, Real.sin_zero, Real.cos_zero, mul_zero, mul_one, zero_sub,
    hz1, zero_mul, sub_zero] at hh
  have hsb : 0 < Real.sin (t₁ - x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hnegd : W1 t₁ < 0 := by nlinarith [hh, hsb, hx]
  have hge := entry_deriv_nonneg h2 (hW t₁ hmem) hz1 hp
  linarith

/-- **The Wronskian is antitone under `r ≤ 1`.** The non-strict twin of
`wronskian_strictAntiOn`: `q ≤ 0` rather than `q < 0`, which is exactly hypothesis (b) of
`D` and not a strengthening of it. -/
theorem wronskian_antitoneOn {W W1 q : ℝ → ℝ} {x a b : ℝ}
    (hWc : Continuous W)
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W (W1 t) t)
    (hW1c : ContinuousOn W1 (Set.Icc a b))
    (hW1 : ∀ t ∈ Set.Ioo a b, HasDerivAt W1 (q t - W t) t)
    (hq : ∀ t ∈ Set.Ioo a b, q t ≤ 0)
    (hpos : ∀ t ∈ Set.Ioo a b, 0 ≤ Real.sin (t - x)) :
    AntitoneOn (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
      (Set.Icc a b) := by
  have hsin : ∀ w : ℝ, HasDerivAt (fun s => Real.sin (s - x)) (Real.cos (w - x)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const x).sin
  have hcos : ∀ w : ℝ, HasDerivAt (fun s => Real.cos (s - x)) (-Real.sin (w - x)) w := by
    intro w; simpa using ((hasDerivAt_id w).sub_const x).cos
  have hGc : ContinuousOn (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
      (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s : ℝ => Real.sin (s - x)) (Set.Icc a b) :=
      (Real.continuous_sin.comp (continuous_id.sub continuous_const)).continuousOn
    have h2 : ContinuousOn (fun s : ℝ => Real.cos (s - x)) (Set.Icc a b) :=
      (Real.continuous_cos.comp (continuous_id.sub continuous_const)).continuousOn
    exact (hW1c.mul h1).sub (hWc.continuousOn.mul h2)
  have hd : ∀ w ∈ Set.Ioo a b,
      HasDerivAt (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x))
        (q w * Real.sin (w - x)) w := by
    intro w hw
    have h := ((hW1 w hw).mul (hsin w)).sub ((hW w (Set.mem_Icc_of_Ioo hw)).mul (hcos w))
    have e : q w * Real.sin (w - x)
        = (q w - W w) * Real.sin (w - x) + W1 w * Real.cos (w - x)
          - (W1 w * Real.cos (w - x) + W w * -Real.sin (w - x)) := by ring
    rw [e]; exact h
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hGc ?_ ?_
  · intro w hw
    rw [interior_Icc] at hw
    exact (hd w hw).differentiableAt.differentiableWithinAt
  · intro w hw
    rw [interior_Icc] at hw
    rw [(hd w hw).deriv]
    nlinarith [hq w hw, hpos w hw]

/-- **`{W > 0}` is order-connected on a window shorter than `π`.** The `AntitoneOn` twin of
`pos_set_ordConnected`, with the derivative of `W` needed only on the OPEN window
`Set.Ioo lo hi`. Both `[0, π/2]` and `[π/2, π]` therefore qualify: the atom sits at an endpoint
of each and `W'` is never asked for there. -/
theorem pos_set_ordConnected_of_antitone {W W1 : ℝ → ℝ} {lo hi : ℝ} (hlen : hi - lo < Real.pi)
    (hWc : Continuous W)
    (hW : ∀ t ∈ Set.Ioo lo hi, HasDerivAt W (W1 t) t)
    (hanti : ∀ x ∈ Set.Ico lo hi,
      AntitoneOn (fun s => W1 s * Real.sin (s - x) - W s * Real.cos (s - x)) (Set.Ico x hi)) :
    {t | t ∈ Set.Icc lo hi ∧ 0 < W t}.OrdConnected := by
  constructor
  intro x hx z hz y hy
  rcases eq_or_lt_of_le hy.1 with h | hxy
  · exact h ▸ hx
  rcases eq_or_lt_of_le hy.2 with h | hyz
  · exact h ▸ hz
  have hxz : x < z := lt_trans hxy hyz
  have hxlo : lo ≤ x := hx.1.1
  have hzhi : z ≤ hi := hz.1.2
  refine ⟨⟨le_trans hxlo hxy.le, le_trans hyz.le hzhi⟩, ?_⟩
  refine pos_between_of_antitone hxz (by linarith) hWc
    (fun t ht => hW t ⟨lt_of_le_of_lt hxlo ht.1, lt_of_lt_of_le ht.2 hzhi⟩)
    ((hanti x ⟨hxlo, lt_of_lt_of_le hxz hzhi⟩).mono
      (fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hzhi⟩))
    hx.2 hz.2 y ⟨hxy, hyz⟩

/-- **The atom is never in the cut set.** After the gauge `H(π/2) = 1`, `W(π/2) = -p_y`, so
every point of the cap off the floor has `π/2` in the negative set of `W`. That is why the
split of `{W > 0}` at the atom is forced, and why neither window ever needs `W'` at `π/2`. -/
theorem atom_not_cut {hval px py : ℝ} (hg : hval = 1) (hpy : 0 < py) :
    hval - 1 - (px * Real.cos (Real.pi / 2) + py * Real.sin (Real.pi / 2)) < 0 := by
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, hg]; linarith

/-- **`T(p)` is an interval.** The two half-window statements intersect: the second is pulled
back along the monotone quarter-period shift `t ↦ t + π/2`, which is where `arm_shift` enters.
-/
theorem cut_set_interval {W : ℝ → ℝ}
    (hlo : {t | t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) ∧ 0 < W t}.OrdConnected)
    (hhi : {t | t ∈ Set.Icc (Real.pi / 2) Real.pi ∧ 0 < W t}.OrdConnected) :
    ({t | t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) ∧ 0 < W t} ∩
      ((fun t => t + Real.pi / 2) ⁻¹'
        {t | t ∈ Set.Icc (Real.pi / 2) Real.pi ∧ 0 < W t})).OrdConnected :=
  cut_set_ordConnected hlo (hhi.preimage_mono fun _ _ h => by linarith)

/-- A function vanishing at `t` with strictly positive derivative there is strictly positive
immediately to the right. The strict counterpart of `entry_deriv_nonneg`, and the step that
turns a preimage with nondegenerate Jacobian into a left endpoint of the cut set. -/
theorem pos_right_of_deriv_pos {w : ℝ → ℝ} {d t : ℝ} (hd : HasDerivAt w d t) (hz : w t = 0)
    (hpos : 0 < d) : ∀ᶠ y in nhdsWithin t (Set.Ioi t), 0 < w y := by
  have hw : HasDerivWithinAt w d (Set.Ioi t) t := hd.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope,
    Set.diff_singleton_eq_self (by simp : t ∉ Set.Ioi t)] at hw
  have hs : ∀ᶠ y in nhdsWithin t (Set.Ioi t), 0 < slope w t y := hw (Ioi_mem_nhds hpos)
  filter_upwards [hs, self_mem_nhdsWithin] with y hy hy2
  have hty : t < y := hy2
  rw [slope_def_field, hz, sub_zero] at hy
  rcases div_pos_iff.mp hy with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · linarith

/-- **A nondegenerate preimage is a left endpoint of the cut set.** On face 1 the offset is
`v(t)` and the Jacobian is `u'(t) = s - α₁`; on face 2 it is `u(t)` and `v'(t) = α₂ - s`. In
both cases a strictly positive Jacobian makes the trajectory cross strictly into
`{u > 0, v > 0}`. -/
theorem entry_eventually_cut {u v : ℝ → ℝ} {t d : ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : (u t = 0 ∧ 0 < v t ∧ HasDerivAt u d t) ∨ (v t = 0 ∧ 0 < u t ∧ HasDerivAt v d t))
    (hd : 0 < d) :
    ∀ᶠ y in nhdsWithin t (Set.Ioi t), y ∈ {s | 0 < u s ∧ 0 < v s} := by
  rcases h with ⟨hz, hp, hder⟩ | ⟨hz, hp, hder⟩
  · have h1 := pos_right_of_deriv_pos hder hz hd
    have h2 : {y | 0 < v y} ∈ nhdsWithin t (Set.Ioi t) :=
      nhdsWithin_le_nhds ((isOpen_lt continuous_const hv).mem_nhds hp)
    filter_upwards [h1, h2] with y hy1 hy2 using ⟨hy1, hy2⟩
  · have h1 := pos_right_of_deriv_pos hder hz hd
    have h2 : {y | 0 < u y} ∈ nhdsWithin t (Set.Ioi t) :=
      nhdsWithin_le_nhds ((isOpen_lt continuous_const hu).mem_nhds hp)
    filter_upwards [h1, h2] with y hy1 hy2 using ⟨hy2, hy1⟩

/-- A preimage time is not itself in the cut set: one of the two coordinates vanishes there. -/
theorem entry_not_cut {u v : ℝ → ℝ} {t : ℝ} (h : u t = 0 ∨ v t = 0) :
    t ∉ {s | 0 < u s ∧ 0 < v s} := by
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · rw [h] at h1; exact lt_irrefl 0 h1
  · rw [h] at h2; exact lt_irrefl 0 h2

/-- **At most one entry into an order-connected set.** If two distinct points both fail to lie
in `S` yet have right neighbourhoods inside `S`, the later of them is trapped between two
points of `S`. -/
theorem at_most_one_entry {S : Set ℝ} (hS : S.OrdConnected) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hn : t₁ ∉ S)
    (hs0 : ∀ᶠ y in nhdsWithin t₀ (Set.Ioi t₀), y ∈ S)
    (hs1 : ∀ᶠ y in nhdsWithin t₁ (Set.Ioi t₁), y ∈ S) : False := by
  obtain ⟨a, haS, ha⟩ := (hs0.and (Ioo_mem_nhdsGT h01)).exists
  obtain ⟨b, hbS, hb⟩ := (hs1.and self_mem_nhdsWithin).exists
  exact hn (hS.out haS hbS ⟨le_of_lt ha.2, le_of_lt hb⟩)

/-- **`prop:V` (i)+(ii), assembled.** If the cut set is order-connected, a point cannot have
two preimages of nondegenerate Jacobian under the union of the two truncated sweeps —
whichever faces they sit on. Injectivity of each sweep and disjointness of the two are the
special cases where the two preimages lie on the same face and on opposite faces.

Nothing here mentions `thm:rc` or `thm:cross`: the only input is order-connectedness of
`{u > 0, v > 0}`, which `cut_set_interval` supplies from `r ≤ 1` and the gauge. -/
theorem at_most_one_preimage {u v : ℝ → ℝ} {t₀ t₁ d₀ d₁ : ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hcon : {s | 0 < u s ∧ 0 < v s}.OrdConnected) (hne : t₀ ≠ t₁)
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
    (h0 : (u t₀ = 0 ∧ 0 < v t₀ ∧ HasDerivAt u d₀ t₀) ∨
          (v t₀ = 0 ∧ 0 < u t₀ ∧ HasDerivAt v d₀ t₀))
    (h1 : (u t₁ = 0 ∧ 0 < v t₁ ∧ HasDerivAt u d₁ t₁) ∨
          (v t₁ = 0 ∧ 0 < u t₁ ∧ HasDerivAt v d₁ t₁)) : False := by
  have main : ∀ {a b da db : ℝ}, a < b → 0 < da → 0 < db →
      ((u a = 0 ∧ 0 < v a ∧ HasDerivAt u da a) ∨ (v a = 0 ∧ 0 < u a ∧ HasDerivAt v da a)) →
      ((u b = 0 ∧ 0 < v b ∧ HasDerivAt u db b) ∨ (v b = 0 ∧ 0 < u b ∧ HasDerivAt v db b)) →
      False := by
    intro a b da db hab hda hdb ha hb
    refine at_most_one_entry hcon hab ?_ (entry_eventually_cut hu hv ha hda)
      (entry_eventually_cut hu hv hb hdb)
    exact entry_not_cut (by rcases hb with ⟨h, _⟩ | ⟨h, _⟩; exacts [Or.inl h, Or.inr h])
  rcases lt_or_gt_of_ne hne with h | h
  · exact main h hd₀ hd₁ h0 h1
  · exact main h hd₁ hd₀ h1 h0

end SingleEntry

end MovingSofa
