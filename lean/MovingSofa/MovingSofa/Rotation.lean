/-
# The hallways derived from an actual rotation

`Containment.lean` *defined* the hallways by their half-plane descriptions in the rotated
frame, which was faithful to the note but meant Lean took `lem:uv` on trust.  This file
removes that step: the hallway is defined intrinsically, as the union of the two arms of a
right-angled corridor with the corner at a given point and the arms along a given
orthonormal frame, and the half-plane description is *proved*.

The frame is `μ = (1,1)/√2`, `ν = (-1,1)/√2`, orthonormal because `μ·μ = ν·ν = 1` and
`μ·ν = 0` (`mu_dot_mu`, `nu_dot_nu`, `mu_dot_nu`).  A left-turning hallway at angle `π/4`
with inner corner `c` is

    { p : ⟨p-c, μ⟩ ≤ 1 and ⟨p-c, ν⟩ ≤ 1 } \ { p : ⟨p-c, μ⟩ < 0 and ⟨p-c, ν⟩ < 0 } ,

the L-shaped region of width one in each arm; `hallwayL_eq` shows this is exactly
`Containment.hallwayL a a'` in the coordinates `u = ⟨p, μ⟩`, `v = ⟨p, ν⟩`, with
`a = ⟨c, μ⟩` and `a' = ⟨c, ν⟩`.

The right-turning hallway is the mirror image.  Reflection in the line `u = v` (the
`x`-axis of the original frame, up to translation) carries `μ ↦ -ν` and `ν ↦ -μ`, so the
two inequalities reverse and the corner conditions swap sides; `hallwayR_eq` proves the
corresponding description.  `reflect_mu`, `reflect_nu` verify the action of the reflection
on the frame, which is where "since reflection carries `μ, ν` to `-ν, -μ`" in the note's
one-line proof becomes a checked statement.

With this file the upper-bound chain has no step where Lean takes the note's word.
-/
import Mathlib
import MovingSofa.Containment

namespace MovingSofa

open Real

/-! ## The frame -/

/-- `μ = (1,1)/√2`. -/
noncomputable def muV : ℝ × ℝ := (1/Real.sqrt 2, 1/Real.sqrt 2)

/-- `ν = (-1,1)/√2`. -/
noncomputable def nuV : ℝ × ℝ := (-(1/Real.sqrt 2), 1/Real.sqrt 2)

/-- The Euclidean inner product on `ℝ × ℝ`. -/
def dotp (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

lemma sq_inv_sqrt2 : (1/Real.sqrt 2) * (1/Real.sqrt 2) = 1/2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith [h]

theorem mu_dot_mu : dotp muV muV = 1 := by
  unfold dotp muV; simp only []; rw [sq_inv_sqrt2]; norm_num

theorem nu_dot_nu : dotp nuV nuV = 1 := by
  unfold dotp nuV; simp only [neg_mul_neg]; rw [sq_inv_sqrt2]; norm_num

theorem mu_dot_nu : dotp muV nuV = 0 := by
  unfold dotp muV nuV; ring

/-! ## The hallways, intrinsically -/

/-- **The left-turning hallway at angle `π/4`.**  The L-shaped region of unit width in
each arm, with inner corner at `c`: both arm conditions hold, and the inner quadrant
beyond the corner is removed. -/
def hallL (c : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | dotp (p.1 - c.1, p.2 - c.2) muV ≤ 1 ∧ dotp (p.1 - c.1, p.2 - c.2) nuV ≤ 1}
    \ {p | dotp (p.1 - c.1, p.2 - c.2) muV < 0 ∧ dotp (p.1 - c.1, p.2 - c.2) nuV < 0}

/-- **The right-turning hallway**: the mirror image, with the inequalities reversed. -/
def hallR (d : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | -1 ≤ dotp (p.1 - d.1, p.2 - d.2) muV ∧ -1 ≤ dotp (p.1 - d.1, p.2 - d.2) nuV}
    \ {p | 0 < dotp (p.1 - d.1, p.2 - d.2) muV ∧ 0 < dotp (p.1 - d.1, p.2 - d.2) nuV}

/-- Rotated coordinates: `u = ⟨p, μ⟩`, `v = ⟨p, ν⟩`. -/
noncomputable def toUV (p : ℝ × ℝ) : ℝ × ℝ := (dotp p muV, dotp p nuV)

/-- The inner product is additive in its first argument, so `⟨p - c, ·⟩ = ⟨p, ·⟩ - ⟨c, ·⟩`
and the coordinates of `p - c` are the differences of the coordinates. -/
lemma dotp_sub (p c q : ℝ × ℝ) :
    dotp (p.1 - c.1, p.2 - c.2) q = dotp p q - dotp c q := by
  unfold dotp; ring

/-! ## The half-plane descriptions, proved -/

/-- **`lem:uv`, left half.**  In rotated coordinates the intrinsic hallway is exactly the
half-plane description used by `Containment.lean`, with `a = ⟨c, μ⟩`, `a' = ⟨c, ν⟩`. -/
theorem hallwayL_eq (c : ℝ × ℝ) :
    toUV '' hallL c = hallwayL (dotp c muV) (dotp c nuV) ∩ Set.range toUV := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨⟨h1, h2⟩, hq⟩ := hp
    rw [dotp_sub] at h1 h2
    simp only [Set.mem_setOf_eq, not_and, not_lt] at hq
    refine ⟨⟨⟨by simpa [toUV] using (by linarith : dotp p muV ≤ dotp c muV + 1),
              by simpa [toUV] using (by linarith : dotp p nuV ≤ dotp c nuV + 1)⟩, ?_⟩,
            ⟨p, rfl⟩⟩
    simp only [Set.mem_setOf_eq, not_and, not_lt, toUV]
    intro hlt
    have := hq (by rw [dotp_sub]; linarith)
    rw [dotp_sub] at this
    linarith
  · rintro ⟨⟨⟨h1, h2⟩, hq⟩, ⟨p, rfl⟩⟩
    refine ⟨p, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
    · rw [dotp_sub]; simp only [toUV] at h1; linarith
    · rw [dotp_sub]; simp only [toUV] at h2; linarith
    · simp only [Set.mem_setOf_eq, not_and, not_lt] at hq ⊢
      intro hlt
      rw [dotp_sub] at hlt ⊢
      have := hq (by simp only [toUV]; linarith)
      simp only [toUV] at this
      linarith

/-- **`lem:uv`, right half.**  Same for the mirror image, with `b = ⟨d, μ⟩`,
`b' = ⟨d, ν⟩`. -/
theorem hallwayR_eq (d : ℝ × ℝ) :
    toUV '' hallR d = hallwayR (dotp d muV) (dotp d nuV) ∩ Set.range toUV := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨⟨h1, h2⟩, hq⟩ := hp
    rw [dotp_sub] at h1 h2
    simp only [Set.mem_setOf_eq, not_and, not_lt] at hq
    refine ⟨⟨⟨by simpa [toUV] using (by linarith : dotp d muV - 1 ≤ dotp p muV),
              by simpa [toUV] using (by linarith : dotp d nuV - 1 ≤ dotp p nuV)⟩, ?_⟩,
            ⟨p, rfl⟩⟩
    simp only [Set.mem_setOf_eq, not_and, not_lt, toUV]
    intro hlt
    have := hq (by rw [dotp_sub]; linarith)
    rw [dotp_sub] at this
    linarith
  · rintro ⟨⟨⟨h1, h2⟩, hq⟩, ⟨p, rfl⟩⟩
    refine ⟨p, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
    · rw [dotp_sub]; simp only [toUV] at h1; linarith
    · rw [dotp_sub]; simp only [toUV] at h2; linarith
    · simp only [Set.mem_setOf_eq, not_and, not_lt] at hq ⊢
      intro hlt
      rw [dotp_sub] at hlt ⊢
      have := hq (by simp only [toUV]; linarith)
      simp only [toUV] at this
      linarith

/-! ## The reflection

"Reflection carries `μ, ν` to `-ν, -μ`" is the sentence the note's proof of `lem:uv`
rests on for the right-turning hallway.  Here it is checked. -/

/-- Reflection in the horizontal axis, `ρ(x, y) = (x, -y)`, the linear part of the map
that exchanges the two handednesses. -/
def reflect (p : ℝ × ℝ) : ℝ × ℝ := (p.1, -p.2)

theorem reflect_mu : reflect muV = (1/Real.sqrt 2, -(1/Real.sqrt 2)) := by
  unfold reflect muV; rfl

/-- `⟨ρ p, μ⟩ = ⟨p, -ν⟩` and `⟨ρ p, ν⟩ = ⟨p, -μ⟩`: the reflection swaps and negates the
frame, which is exactly the sentence the note uses. -/
theorem reflect_dot_mu (p : ℝ × ℝ) : dotp (reflect p) muV = - dotp p nuV := by
  unfold dotp reflect muV nuV; ring

theorem reflect_dot_nu (p : ℝ × ℝ) : dotp (reflect p) nuV = - dotp p muV := by
  unfold dotp reflect muV nuV; ring

end MovingSofa
