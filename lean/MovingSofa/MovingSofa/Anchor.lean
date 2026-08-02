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

end MovingSofa
