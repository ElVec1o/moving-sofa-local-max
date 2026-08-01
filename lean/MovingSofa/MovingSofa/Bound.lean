/-
# The unconditional ambidextrous upper bound, over the reals

`Basic.lean` is Mathlib-free and carries the combinatorial skeleton over `Int`.  This file
uses Mathlib and states the same lemmas over `ℝ`, where they are the actual mathematical
statements rather than faithful models of them.

What is formalised here is the chain that produces `2 * sqrt 2 - 1`:

1. `four_piece` -- the decomposition of the kept set into four pieces.  This is the
   load-bearing combinatorial step of the whole bound and the one where a missed case
   would be fatal.
2. `low_end_le`, `high_end_le` -- the two ends of `I` are short, which is where the tent
   profiles `2 - 2|s - m|` come from.
3. `profile_ge_one`, `g_mid_le` -- the maximum of the profile integral, reduced to
   `x^2 + (sqrt 2 - x)^2 >= 1`, i.e. to `(2x - sqrt 2)^2 >= 0`.
4. `sq_eq_iff` and `g_max_unique` -- the maximiser is exactly `x = 1 / sqrt 2`, which is
   the extremal placement `a = a' = b = b' = sqrt 2 / 4`.
5. `wide_case_le` -- the `t >= 1` case, where the bound is `sqrt 2 < 2 sqrt 2 - 1`.
6. `both_positive_absorbed` -- the cancellation that makes the both-offsets-positive case
   need no new estimate.

What is NOT formalised: the passage from the fibrewise bound to the area, which is an
integral of a piecewise-linear function over the band, and the ball-arithmetic certificate
for region (iv) of the profile inequality.  Those remain PROVED, not VERIFIED, and the
note says so.
-/
import Mathlib

namespace MovingSofa

open Real

/-! ## The four-piece decomposition -/

/-- **The decomposition.**  A point avoids both removed open intervals `(p,q)` and `(r,w)`
exactly when it lies in one of four pieces: below both (`A`), in the cross piece `[q,r]`
(`B`), in the cross piece `[w,p]` (`C`), or above both (`D`).

Distributing the two complements is what produces four pieces rather than two, and the two
cross pieces are exactly what the sign-restricted form of the theorem had to assume away.
Stated for `ℝ`, but only the linear order is used. -/
theorem four_piece (p q r w x : ℝ) :
    (¬(p < x ∧ x < q) ∧ ¬(r < x ∧ x < w)) ↔
      ((x ≤ p ∧ x ≤ r) ∨ (q ≤ x ∧ x ≤ r) ∨ (w ≤ x ∧ x ≤ p) ∨ (q ≤ x ∧ w ≤ x)) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [not_and_or, not_lt, not_lt] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      refine ⟨?_, ?_⟩ <;> rintro ⟨a, b⟩ <;> linarith

/-- **The sign-restricted case.**  When both corner offsets are nonpositive the two cross
pieces are empty and only the two ends survive.  This is `thm:upper` of the note. -/
theorem four_piece_no_cross (p q r w x : ℝ) (hB : r < q) (hC : p < w) :
    (¬(p < x ∧ x < q) ∧ ¬(r < x ∧ x < w)) ↔ ((x ≤ p ∧ x ≤ r) ∨ (q ≤ x ∧ w ≤ x)) := by
  rw [four_piece]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h)
    · exact Or.inl h
    · linarith
    · linarith
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))

/-- **Case 2 of the unconditional theorem (`lem:bothpos`).**  When both offsets are
positive, `q ≤ r` and `w ≤ p`, the cross piece `B = [q,r]` is already contained in
`A ∪ C ∪ D`.  This is the containment that makes the both-positive case need no estimate
beyond the two tents. -/
theorem both_positive_absorbed (p q r w x : ℝ) (hqr : q ≤ r) (hwp : w ≤ p)
    (hx : q ≤ x ∧ x ≤ r) :
    (x ≤ p ∧ x ≤ r) ∨ (w ≤ x ∧ x ≤ p) ∨ (q ≤ x ∧ w ≤ x) := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_total x p with hp | hp
  · exact Or.inl ⟨hp, h2⟩
  · exact Or.inr (Or.inr ⟨h1, le_trans hwp hp⟩)

/-! ## The ends of `I` are short -/

/-- **The low end.**  `I` begins at `max p r - 2`, so the piece below both removed
intervals has length at most `2 - |p - r|`. -/
theorem low_end_le (p r : ℝ) : min p r - (max p r - 2) = 2 - |p - r| := by
  rcases le_total p r with h | h <;>
    simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h, abs_of_nonpos,
      abs_of_nonneg, sub_nonneg, sub_nonpos] <;> linarith

/-- **The high end.**  `I` ends at `min q w + 2`, so the piece above both removed
intervals has length at most `2 - |q - w|`. -/
theorem high_end_le (q w : ℝ) : (min q w + 2) - max q w = 2 - |q - w| := by
  rcases le_total q w with h | h <;>
    simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h, abs_of_nonpos,
      abs_of_nonneg, sub_nonneg, sub_nonpos] <;> linarith

/-! ## The profile maximum

On the range where the tent covers the whole band,
`g x = 2 * sqrt 2 - x ^ 2 - (sqrt 2 - x) ^ 2`, so `max g = 2 sqrt 2 - 1` is exactly the
statement `x ^ 2 + (sqrt 2 - x) ^ 2 >= 1`, which is `(2 x - sqrt 2) ^ 2 >= 0`. -/

/-- **The profile inequality.**  `x^2 + (sqrt 2 - x)^2 >= 1` for every real `x`. -/
theorem profile_ge_one (x : ℝ) : 1 ≤ x ^ 2 + (Real.sqrt 2 - x) ^ 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [sq_nonneg (2 * x - Real.sqrt 2), h2]

/-- The middle-range formula for the profile integral. -/
noncomputable def gMid (x : ℝ) : ℝ := 2 * Real.sqrt 2 - x ^ 2 - (Real.sqrt 2 - x) ^ 2

/-- **The maximum of the profile.**  `gMid x ≤ 2 sqrt 2 - 1` for every `x`. -/
theorem gMid_le (x : ℝ) : gMid x ≤ 2 * Real.sqrt 2 - 1 := by
  have := profile_ge_one x
  unfold gMid; linarith

/-- **The maximum is attained, at `1 / sqrt 2`.**  So the bound `2 sqrt 2 - 1` is sharp:
this is the placement `a = a' = b = b' = sqrt 2 / 4` of the note. -/
theorem gMid_at_half : gMid (1 / Real.sqrt 2) = 2 * Real.sqrt 2 - 1 := by
  have hs : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp; nlinarith [h2]
  rw [gMid, h]; field_simp; nlinarith [h2]

/-- **Uniqueness of the maximiser.**  Equality forces `2 x = sqrt 2`. -/
theorem gMid_eq_max_iff (x : ℝ) :
    gMid x = 2 * Real.sqrt 2 - 1 ↔ x = Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hsq : (2 * x - Real.sqrt 2) ^ 2 = 0 := by unfold gMid at h; nlinarith [h2]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  · rintro rfl; unfold gMid; nlinarith [h2]

/-! ## The wide case -/

/-- **Case 1 of the unconditional theorem (`lem:wide`).**  When the larger corner offset
`t` is at least `1`, the outer interval has length at most `4 - 2t ≤ 2` on the whole band,
so the area is at most `sqrt 2 * (2 - t)⁺ ≤ sqrt 2`, and `sqrt 2 < 2 sqrt 2 - 1`. -/
theorem wide_case_le (t : ℝ) (ht : 1 ≤ t) :
    Real.sqrt 2 * max (2 - t) 0 ≤ Real.sqrt 2 := by
  have hs : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have : max (2 - t) 0 ≤ 1 := max_le (by linarith) (by norm_num)
  nlinarith

/-- `sqrt 2 < 2 sqrt 2 - 1`, so the wide case is never the binding one. -/
theorem sqrt_two_lt_bound : Real.sqrt 2 < 2 * Real.sqrt 2 - 1 := by
  have : (1:ℝ) < Real.sqrt 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h2]
  linarith

/-! ## The constant -/

/-- `2 sqrt 2 - 1` is strictly between Romik's constant and Gerver's, which is the content
of the bracket in the note: `1.6449552 ≤ A_ambi ≤ 1.8284271 < 2.2195316`. -/
theorem bound_lt_gerver : 2 * Real.sqrt 2 - 1 < 2.2195316 := by
  have h : Real.sqrt 2 < 1.41421357 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h2]
  linarith

/-- and it is above Romik's lower bound, so the bracket is nonempty. -/
theorem romik_lt_bound : (1.6449552 : ℝ) < 2 * Real.sqrt 2 - 1 := by
  have h : (1.41421356 : ℝ) < Real.sqrt 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h2]
  linarith

end MovingSofa
