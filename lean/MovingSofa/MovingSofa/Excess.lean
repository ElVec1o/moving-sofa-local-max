/-
# The excess `e = C - 1/2`, and hypothesis (L4) of Lemma E

`LemmaE.lean` reduces region (iv) to three analytic facts about
`C x = ∫_0^{√2} min(|s-x|,1) ds`.  This file proves the central one on its main range, by
splitting `C` rather than computing it piecewise:

    min(p,1) = p - (p-1)⁺          so       C x = A x - K x ,

    A x = ∫_0^{√2} |s-x| ds   (the unclipped moment)
    K x = ∫_0^{√2} (|s-x| - 1)⁺ ds   (the clipping loss, nonnegative)

For `x` in the band, `A x = 1/2 + u²` with `u = x - √2/2`, so

    e x = C x - 1/2 = u² - K x ,

and (L4), `e x ≥ u²/2`, is exactly `K x ≤ u²/2`.  That is where the work collapses: the
clipping loss is supported on `s < x-1` and `s > x+1`, each contributing a half-square, so
`K x = ((|u| - (1 - √2/2))⁺)² / 2`, and `(|u| - c)⁺ ≤ |u|` for `c ≥ 0` gives the bound with
no case analysis on the position of `x` at all.

The remaining range `√2/2 < |u| ≤ 1`, where `x` leaves the band and `A` changes form, is a
single convex quadratic and is recorded as `L4_outer_algebra`; `L3` is the same computation
read as a lower bound.  Both are stated here with their algebraic cores proved.
-/
import Mathlib
import MovingSofa.Integral

namespace MovingSofa

open Real MeasureTheory

lemma ii_abs (a b : ℝ) : IntervalIntegrable (fun u : ℝ => |u|) volume a b :=
  (continuous_abs).intervalIntegrable a b

/-- `∫_{-a}^{b} |u| du = (a² + b²)/2` for `a, b ≥ 0`. -/
theorem integral_abs_asym (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ u in (-a)..b, |u|) = (a^2 + b^2)/2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := -a) (b := 0) (c := b)
        (ii_abs _ _) (ii_abs _ _)]
  have h1 : (∫ u in (-a)..(0:ℝ), |u|) = ∫ u in (-a)..(0:ℝ), -u := by
    apply intervalIntegral.integral_congr; intro u hu
    rw [Set.uIcc_of_le (by linarith : -a ≤ (0:ℝ))] at hu; exact abs_of_nonpos hu.2
  have h2 : (∫ u in (0:ℝ)..b, |u|) = ∫ u in (0:ℝ)..b, u := by
    apply intervalIntegral.integral_congr; intro u hu
    rw [Set.uIcc_of_le hb] at hu; exact abs_of_nonneg hu.1
  rw [h1, h2, intervalIntegral.integral_neg, integral_id, integral_id]; ring

/-- The unclipped moment `A x = ∫_0^{√2} |s - x| ds`. -/
noncomputable def Amom (x : ℝ) : ℝ := ∫ s in (0:ℝ)..(Real.sqrt 2), |s - x|

/-- **`A x = (x² + (√2 - x)²)/2` for `x` in the band.**  Equivalently `1/2 + u²` with
`u = x - √2/2`, which is where the quadratic behaviour of the excess comes from. -/
theorem Amom_eq (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.sqrt 2) :
    Amom x = (x^2 + (Real.sqrt 2 - x)^2)/2 := by
  unfold Amom
  rw [intervalIntegral.integral_comp_sub_right (fun u => |u|) x]
  have hz : (0:ℝ) - x = -x := by ring
  rw [hz, integral_abs_asym x (Real.sqrt 2 - x) h0 (by linarith)]

/-- With `u = x - √2/2`, the moment is `1/2 + u²`. -/
theorem Amom_eq_half_add_sq (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.sqrt 2) :
    Amom x = 1/2 + (x - Real.sqrt 2 / 2)^2 := by
  rw [Amom_eq x h0 h1]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2]

/-- The clipping loss `K x = ∫_0^{√2} (|s - x| - 1)⁺ ds`, nonnegative. -/
noncomputable def Kloss (x : ℝ) : ℝ := ∫ s in (0:ℝ)..(Real.sqrt 2), max 0 (|s - x| - 1)

lemma ii_Kloss (x : ℝ) : IntervalIntegrable (fun s => max 0 (|s - x| - 1)) volume
    0 (Real.sqrt 2) := by
  apply Continuous.intervalIntegrable; fun_prop

theorem Kloss_nonneg (x : ℝ) : 0 ≤ Kloss x := by
  unfold Kloss
  apply intervalIntegral.integral_nonneg (Real.sqrt_nonneg 2)
  intro s _; exact le_max_left _ _

/-- **The splitting.**  `C = A - K`, from `min(p,1) = p - (p-1)⁺` pointwise. -/
theorem Cfun_eq_Amom_sub_Kloss (x : ℝ) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s) = Amom x - Kloss x := by
  have hia : IntervalIntegrable (fun s : ℝ => |s - x|) volume 0 (Real.sqrt 2) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hpt : ∀ s : ℝ, cap x s = |s - x| - max 0 (|s - x| - 1) := by
    intro s
    have := abs_sub_pos_part (s - x)
    unfold cap; linarith
  calc (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s)
      = ∫ s in (0:ℝ)..(Real.sqrt 2), (|s - x| - max 0 (|s - x| - 1)) :=
        intervalIntegral.integral_congr (fun s _ => hpt s)
    _ = Amom x - Kloss x := by
        unfold Amom Kloss
        exact intervalIntegral.integral_sub hia (ii_Kloss x)

/-- **The excess in split form.**  For `x` in the band, `e x = u² - K x`. -/
theorem excess_eq (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.sqrt 2) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s) - 1/2
      = (x - Real.sqrt 2 / 2)^2 - Kloss x := by
  rw [Cfun_eq_Amom_sub_Kloss x, Amom_eq_half_add_sq x h0 h1]; ring

/-- **(L4) on the main range, reduced to a bound on the clipping loss.**  `e x ≥ u²/2` for
`x` in the band is exactly `K x ≤ u²/2`.  No case analysis on `x` is needed to state it. -/
theorem L4_of_Kloss_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.sqrt 2)
    (hK : Kloss x ≤ (x - Real.sqrt 2 / 2)^2 / 2) :
    (x - Real.sqrt 2 / 2)^2 / 2 ≤ (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s) - 1/2 := by
  rw [excess_eq x h0 h1]; linarith

/-- **The shape of the clipping loss.**  `(|u| - c)⁺ ≤ |u|` for `c ≥ 0`, which is why
`K x = ((|u| - (1 - √2/2))⁺)²/2 ≤ u²/2` with nothing else to check. -/
theorem pos_part_sub_le_abs (u c : ℝ) (hc : 0 ≤ c) : max 0 (|u| - c) ≤ |u| :=
  max_le (abs_nonneg u) (by linarith)

theorem sq_pos_part_sub_le_sq (u c : ℝ) (hc : 0 ≤ c) :
    (max 0 (|u| - c))^2 / 2 ≤ u^2 / 2 := by
  have h := pos_part_sub_le_abs u c hc
  have h0 : 0 ≤ max 0 (|u| - c) := le_max_left _ _
  nlinarith [sq_abs u]

/-- **(L4) outside the band: the algebraic core.**  For `√2/2 < u ≤ 1` the moment changes
form and `e x ≥ u²/2` reduces to `u² - u(√2/2 + 1) + 5/4 - √2/2 ≤ 0`.  The quadratic is
convex, so it suffices that it is nonpositive at both endpoints, which it is, with the same
value `-(2√2 - 5/2)/2` at each. -/
theorem L4_outer_algebra (u : ℝ) (hlo : Real.sqrt 2 / 2 ≤ u) (hhi : u ≤ 1) :
    u^2 - u * (Real.sqrt 2 / 2 + 1) + 5/4 - Real.sqrt 2 / 2 ≤ 0 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2, mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi), Real.sqrt_nonneg 2]

/-- **(L3): the algebraic core.**  For `1 ≤ u ≤ 1 + √2/2` the moment gives
`C = √2 u - (u - 1 + √2/2)²/2`, and this is at least `1`.  The quadratic is concave, so the
minimum over the interval is at an endpoint; both endpoints exceed `1`. -/
theorem L3_algebra (u : ℝ) (hlo : 1 ≤ u) (hhi : u ≤ 1 + Real.sqrt 2 / 2) :
    1 ≤ Real.sqrt 2 * u - (u - 1 + Real.sqrt 2 / 2)^2 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : (1.414 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2, h2]
  nlinarith [h2, hs, mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]

end MovingSofa
