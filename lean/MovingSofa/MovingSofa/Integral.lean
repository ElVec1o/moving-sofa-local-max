/-
# The profile integral, verified

`Bound.lean` verifies the combinatorial half of the unconditional bound: the four-piece
decomposition, and the fact that `2 sqrt 2 - x^2 - (sqrt 2 - x)^2 <= 2 sqrt 2 - 1`.  What
it did NOT verify is the step that actually produces the constant, namely

    g x  :=  ∫_0^{sqrt 2} (2 - 2|s - x|)^+ ds  ≤  2 sqrt 2 - 1 ,

because that is an integral and `Basic.lean` had no analysis available.  This file proves
it, and the proof is short once the right identity is used.

THE IDENTITY.  `max 0 y = y + max 0 (-y)`.  Applied to `y = 2 - 2|s-x|`,

    (2 - 2|s-x|)^+  =  2 - 2|s-x| + 2(|s-x| - 1)^+ ,

with NO case hypothesis: the truncation is not an obstruction, it is a correction term.
Integrating and using `|y| - (|y|-1)^+ = min(|y|, 1)`,

    g x  =  2 sqrt 2  -  2 ∫_0^{sqrt 2} min(|s - x|, 1) ds ,

so the bound `g x <= 2 sqrt 2 - 1` is EXACTLY the statement

    ∫_0^{sqrt 2} min(|s - x|, 1) ds  ≥  1/2                          (*)

for every real `x`.  This is where the `-1` in `2 sqrt 2 - 1` comes from, which is the same
`-1` that separates the constant from Hammersley's `2 sqrt 2`.

THE PAIRING.  (*) has a one-line proof.  Split `[0, sqrt 2]` at its midpoint and pair `s`
with `s + sqrt2/2`.  Since `|s - x| + |s + sqrt2/2 - x| ≥ sqrt2/2` by the triangle
inequality, and `min(a,1) + min(b,1) ≥ min(a+b,1)`,

    min(|s-x|,1) + min(|s + sqrt2/2 - x|, 1)  ≥  min(sqrt2/2, 1)  =  sqrt2/2 ,

because `sqrt2/2 < 1`.  Integrating that over `[0, sqrt2/2]` gives `(sqrt2/2)^2 = 1/2`.
Equality throughout at `x = sqrt2/2`, which is the extremal placement.

No case analysis on the position of `x` relative to the band is needed anywhere, which is
why this is short: the clipping cases that make the closed form for `g` awkward are all
absorbed by the identity.
-/
import Mathlib

namespace MovingSofa

open Real MeasureTheory

noncomputable def tent (x s : ℝ) : ℝ := max 0 (2 - 2*|s - x|)

lemma tent_nonneg (x s : ℝ) : 0 ≤ tent x s := le_max_left _ _

lemma continuous_tent (x : ℝ) : Continuous (tent x) := by unfold tent; fun_prop

lemma intervalIntegrable_tent (x a b : ℝ) : IntervalIntegrable (tent x) volume a b :=
  (continuous_tent x).intervalIntegrable a b

/-- **The truncation identity.**  `max 0 y = y + max 0 (-y)`, specialised.  Holds for every
`s` with no case hypothesis; the two branches agree at the kink. -/
lemma tent_eq (x s : ℝ) : tent x s = (2 - 2*|s - x|) + 2 * max 0 (|s - x| - 1) := by
  unfold tent
  rcases le_total (|s - x|) 1 with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

/-- `|y| - (|y| - 1)^+ = min |y| 1`. -/
lemma abs_sub_pos_part (y : ℝ) : |y| - max 0 (|y| - 1) = min |y| 1 := by
  rcases le_total (|y|) 1 with h | h
  · rw [max_eq_left (by linarith), min_eq_left h]; ring
  · rw [max_eq_right (by linarith), min_eq_right h]; ring

/-- The clipped distance, the function `(*)` is about. -/
noncomputable def cap (x s : ℝ) : ℝ := min |s - x| 1

lemma continuous_cap (x : ℝ) : Continuous (cap x) := by unfold cap; fun_prop

lemma intervalIntegrable_cap (x a b : ℝ) : IntervalIntegrable (cap x) volume a b :=
  (continuous_cap x).intervalIntegrable a b

/-- `tent x s = 2 - 2 * cap x s`, the form in which the integral is trivial. -/
lemma tent_eq_cap (x s : ℝ) : tent x s = 2 - 2 * cap x s := by
  have h := tent_eq x s
  have h2 := abs_sub_pos_part (s - x)
  unfold cap
  rw [h]; linarith [h2]

/-- **Subadditivity of the clip.**  `min(a+b,1) ≤ min a 1 + min b 1` for `a, b ≥ 0`. -/
lemma min_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (a + b) 1 ≤ min a 1 + min b 1 := by
  rcases le_total a 1 with h1 | h1 <;> rcases le_total b 1 with h2 | h2 <;>
    simp [min_def] <;> split_ifs <;> linarith

lemma sqrt2_half_lt_one : Real.sqrt 2 / 2 < 1 := by
  have h : Real.sqrt 2 < 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h2]
  linarith

lemma sqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- **The pairing bound.**  For every `s` and `x`, the clip at `s` plus the clip at
`s + sqrt2/2` is at least `sqrt2/2`.  Triangle inequality plus subadditivity. -/
lemma cap_pair (x s : ℝ) :
    Real.sqrt 2 / 2 ≤ cap x s + cap x (s + Real.sqrt 2 / 2) := by
  have htri : Real.sqrt 2 / 2 ≤ |s - x| + |s + Real.sqrt 2 / 2 - x| := by
    rcases abs_cases (s - x) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases abs_cases (s + Real.sqrt 2 / 2 - x) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rw [e1, e2] <;> linarith
  have hsub := min_add_le (|s - x|) (|s + Real.sqrt 2 / 2 - x|) (abs_nonneg _) (abs_nonneg _)
  have hm : min (Real.sqrt 2 / 2) 1 ≤ min (|s - x| + |s + Real.sqrt 2 / 2 - x|) 1 :=
    min_le_min htri (le_refl 1)
  rw [min_eq_left (le_of_lt sqrt2_half_lt_one)] at hm
  unfold cap; linarith

/-- **(*) The clipped-distance integral is at least one half**, for every `x`.  This is the
whole content of the constant: `2 sqrt 2 - 2 * (1/2) = 2 sqrt 2 - 1`. -/
theorem half_le_integral_cap (x : ℝ) :
    (1:ℝ)/2 ≤ ∫ s in (0:ℝ)..(Real.sqrt 2), cap x s := by
  have hc := Real.sqrt_nonneg 2
  have hhalf : Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = Real.sqrt 2 := by ring
  -- split at the midpoint
  have hsplit :
      (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s)
        = (∫ s in (0:ℝ)..(Real.sqrt 2 / 2), cap x s)
          + ∫ s in (Real.sqrt 2 / 2)..(Real.sqrt 2), cap x s := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cap x _ _) (intervalIntegrable_cap x _ _)]
  -- translate the second half back onto the first
  have hshift :
      (∫ s in (Real.sqrt 2 / 2)..(Real.sqrt 2), cap x s)
        = ∫ u in (0:ℝ)..(Real.sqrt 2 / 2), cap x (u + Real.sqrt 2 / 2) := by
    rw [intervalIntegral.integral_comp_add_right (fun s => cap x s) (Real.sqrt 2 / 2)]
    congr 1 <;> ring
  have hshift2 : IntervalIntegrable (fun u => cap x (u + Real.sqrt 2 / 2)) volume
      0 (Real.sqrt 2 / 2) :=
    ((continuous_cap x).comp (by fun_prop)).intervalIntegrable _ _
  have hadd : (∫ s in (0:ℝ)..(Real.sqrt 2 / 2), cap x s)
        + (∫ u in (0:ℝ)..(Real.sqrt 2 / 2), cap x (u + Real.sqrt 2 / 2))
      = ∫ s in (0:ℝ)..(Real.sqrt 2 / 2), (cap x s + cap x (s + Real.sqrt 2 / 2)) :=
    (intervalIntegral.integral_add (intervalIntegrable_cap x _ _) hshift2).symm
  rw [hsplit, hshift, hadd]
  have hmono :
      (∫ _s in (0:ℝ)..(Real.sqrt 2 / 2), Real.sqrt 2 / 2)
        ≤ ∫ s in (0:ℝ)..(Real.sqrt 2 / 2), (cap x s + cap x (s + Real.sqrt 2 / 2)) := by
    apply intervalIntegral.integral_mono_on (by positivity)
      (intervalIntegrable_const)
      ((intervalIntegrable_cap x _ _).add hshift2)
    intro s _
    exact cap_pair x s
  have hconst :
      (∫ _s in (0:ℝ)..(Real.sqrt 2 / 2), Real.sqrt 2 / 2) = (1:ℝ)/2 := by
    rw [intervalIntegral.integral_const]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    simp only [smul_eq_mul, sub_zero]
    nlinarith [h2]
  linarith [hconst ▸ hmono]

/-- **The profile integral is at most `2 sqrt 2 - 1`, for every `x`.**  This is
Proposition "the profile integral" of the note, and the step that had been PROVED but not
VERIFIED. -/
theorem integral_tent_le (x : ℝ) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), tent x s) ≤ 2 * Real.sqrt 2 - 1 := by
  have hrw : (∫ s in (0:ℝ)..(Real.sqrt 2), tent x s)
      = (∫ s in (0:ℝ)..(Real.sqrt 2), (2 - 2 * cap x s)) := by
    simp_rw [tent_eq_cap]
  have hlin : (∫ s in (0:ℝ)..(Real.sqrt 2), (2 - 2 * cap x s))
      = 2 * Real.sqrt 2 - 2 * ∫ s in (0:ℝ)..(Real.sqrt 2), cap x s := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegrable_cap x _ _).const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp; ring
  rw [hrw, hlin]
  linarith [half_le_integral_cap x]

/-- `∫_{-c}^{c} |u| du = c^2`, by splitting at `0`. -/
lemma integral_abs_symm (c : ℝ) (hc : 0 ≤ c) : (∫ u in (-c)..c, |u|) = c^2 := by
  have ii : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => |u|) volume a b :=
    fun a b => (continuous_abs).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := -c) (b := 0) (c := c)
        (ii _ _) (ii _ _)]
  have h1 : (∫ u in (-c)..(0:ℝ), |u|) = ∫ u in (-c)..(0:ℝ), -u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith : -c ≤ (0:ℝ))] at hu
    exact abs_of_nonpos hu.2
  have h2 : (∫ u in (0:ℝ)..c, |u|) = ∫ u in (0:ℝ)..c, u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hc] at hu
    exact abs_of_nonneg hu.1
  rw [h1, h2, intervalIntegral.integral_neg, integral_id, integral_id]
  ring

/-- **Sharpness.**  At `x = sqrt2/2` the tent is nonnegative throughout the band, so the
clip is inactive, the integral is exactly `2 sqrt 2 - 1`, and the bound of
`integral_tent_le` is attained.  Together they say `2 sqrt 2 - 1` IS the supremum, which is
Proposition "the extremal configuration" of the note. -/
theorem integral_tent_at_mid :
    (∫ s in (0:ℝ)..(Real.sqrt 2), tent (Real.sqrt 2 / 2) s) = 2 * Real.sqrt 2 - 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hcap : ∀ s ∈ Set.uIcc (0:ℝ) (Real.sqrt 2),
      cap (Real.sqrt 2 / 2) s = |s - Real.sqrt 2 / 2| := by
    intro s hs
    rw [Set.uIcc_of_le hnn] at hs
    obtain ⟨h0, h1⟩ := hs
    have hb : |s - Real.sqrt 2 / 2| ≤ Real.sqrt 2 / 2 := by
      rw [abs_le]; constructor <;> linarith
    exact min_eq_left (hb.trans (le_of_lt sqrt2_half_lt_one))
  have habs : (∫ s in (0:ℝ)..(Real.sqrt 2), |s - Real.sqrt 2 / 2|) = 1/2 := by
    rw [intervalIntegral.integral_comp_sub_right (fun u => |u|) (Real.sqrt 2 / 2)]
    have hz : (0:ℝ) - Real.sqrt 2 / 2 = -(Real.sqrt 2 / 2) := by ring
    have ho : Real.sqrt 2 - Real.sqrt 2 / 2 = Real.sqrt 2 / 2 := by ring
    rw [hz, ho, integral_abs_symm _ (by linarith)]
    nlinarith [h2]
  have hcapint : (∫ s in (0:ℝ)..(Real.sqrt 2), cap (Real.sqrt 2 / 2) s) = 1/2 := by
    rw [intervalIntegral.integral_congr hcap, habs]
  have hrw : (∫ s in (0:ℝ)..(Real.sqrt 2), tent (Real.sqrt 2 / 2) s)
      = ∫ s in (0:ℝ)..(Real.sqrt 2), (2 - 2 * cap (Real.sqrt 2 / 2) s) := by
    simp_rw [tent_eq_cap]
  rw [hrw, intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegrable_cap _ _ _).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hcapint]
  simp; ring

end MovingSofa
