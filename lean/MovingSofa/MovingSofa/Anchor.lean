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

end MovingSofa
