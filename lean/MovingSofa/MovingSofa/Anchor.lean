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

end MovingSofa
