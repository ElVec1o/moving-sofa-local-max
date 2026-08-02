/-
# Hallways, ambidextrous sofas, and the containment

The last obligation of the upper-bound chain was `hplace : S ⊆ placedRegion …`.  This file
supplies it, by defining the objects the note works with and observing that the
containment is then definitional.  Two things happen here, and it is worth separating
them because only the second is mathematics.

**The definition.**  An ambidextrous moving sofa is a set together with two motions, and
"the sofa lies in the hallway at every instant" is part of what that means, not something
proved about it.  `AmbiSofa` records exactly that, and `sofa_subset_pair` is a one-line
consequence: `S` lies in the intersection of any one left-hallway placement with any one
right-hallway placement.  This is Proposition "finite-angle relaxation" of the note at two
angles, and its proof there is also one line.

**The coordinate identification.**  In the rotated coordinates `u = ⟨p, μ⟩`, `v = ⟨p, ν⟩`
the note's Lemma "uv" computes the two hallways at angle `π/4` as a rectangle less two
opposite quadrants, and the corridor as the band.  `hallwayL_eq` and `hallwayR_eq` state
those descriptions, and `pair_eq_placedRegion` assembles them into `placedRegion` in the
fibre coordinates `(s, t) = (u + v, u - v)`.  These are affine computations with no
analysis in them; they are the content of `lem:uv`.

What this file does NOT do is derive the half-plane description of a rotated hallway from
a definition of rotation — the hallways are *defined* here by those half-planes, which is
faithful to the note (its Lemma "uv" proves the equivalence, and reflection carries `μ, ν`
to `-ν, -μ`) but means the identification is recorded rather than re-derived.  That is the
single remaining gap in the chain, and it is a modelling step, not an estimate.
-/
import Mathlib
import MovingSofa.Reduction

namespace MovingSofa

open Set

/-! ## Hallways in rotated coordinates -/

/-- The left-turning hallway at angle `π/4` with inner corner at `(a, a')` in the rotated
frame: the quadrant `{u ≤ a+1, v ≤ a'+1}` less the open inner quadrant `{u < a, v < a'}`.
This is the description established by Lemma "uv" of the note. -/
def hallwayL (a a' : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ≤ a + 1 ∧ z.2 ≤ a' + 1} \ {z | z.1 < a ∧ z.2 < a'}

/-- The right-turning hallway at angle `π/4` with inner corner at `(b, b')`.  Reflection
carries `μ, ν` to `-ν, -μ`, so the inequalities reverse. -/
def hallwayR (b b' : ℝ) : Set (ℝ × ℝ) :=
  {z | b - 1 ≤ z.1 ∧ b' - 1 ≤ z.2} \ {z | b < z.1 ∧ b' < z.2}

/-! ## Ambidextrous sofas

A sofa carries two motions; membership in the hallway at every instant is part of the
structure.  Only the two instants at angle `π/4` are recorded, which is all the
two-hallway relaxation uses. -/

/-- An ambidextrous moving sofa, as far as the relaxation needs: a set contained in some
left-turning and some right-turning hallway placement at angle `π/4`. -/
structure AmbiSofa where
  /-- the sofa -/
  carrier : Set (ℝ × ℝ)
  /-- the left-hallway corner at angle `π/4`, in rotated coordinates -/
  a : ℝ
  a' : ℝ
  /-- the right-hallway corner at angle `π/4` -/
  b : ℝ
  b' : ℝ
  /-- the sofa is inside the left hallway at that instant -/
  inL : carrier ⊆ hallwayL a a'
  /-- and inside the right hallway at that instant -/
  inR : carrier ⊆ hallwayR b b'

/-- **The relaxation at two angles.**  Definitional. -/
theorem sofa_subset_pair (S : AmbiSofa) :
    S.carrier ⊆ hallwayL S.a S.a' ∩ hallwayR S.b S.b' :=
  subset_inter S.inL S.inR

/-! ## The fibre coordinates

`placedRegion` is written in `(s, t)` with `s = u + v` the band coordinate and `t = u - v`
the fibre coordinate; the map `(u, v) ↦ (u + v, u - v)` is the change of variables whose
Jacobian is the factor `2` recorded in `Reduction.lean`. -/

/-- The change of variables to fibre coordinates. -/
def toFibre (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + z.2, z.1 - z.2)

/-- **The identification.**  A point of the two-hallway intersection that also lies in the
band maps into `placedRegion`.  Pure affine arithmetic: the four inequalities of the
rectangle become the two outer bounds, and the two removed quadrants become the two
excluded open intervals. -/
theorem toFibre_mem_placedRegion (a a' b b' : ℝ) (z : ℝ × ℝ)
    (hL : z ∈ hallwayL a a') (hR : z ∈ hallwayR b b')
    (hband : 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ Real.sqrt 2) :
    toFibre z ∈ placedRegion a a' b b' := by
  obtain ⟨⟨hu1, hv1⟩, hLq⟩ := hL
  obtain ⟨⟨hu2, hv2⟩, hRq⟩ := hR
  simp only [mem_setOf_eq, not_and, not_lt] at hLq hRq
  refine ⟨hband.1, hband.2, ?_, ?_, ?_, ?_⟩
  · -- max (s - 2a') (2b - s) - 2 ≤ t
    simp only [toFibre]
    have hmax : max (z.1 + z.2 - 2*a') (2*b - (z.1 + z.2)) ≤ z.1 - z.2 + 2 :=
      max_le (by linarith) (by linarith)
    linarith
  · -- t ≤ min (2a - s) (s - 2b') + 2
    simp only [toFibre]
    have hmin : z.1 - z.2 - 2 ≤ min (2*a - (z.1 + z.2)) ((z.1 + z.2) - 2*b') :=
      le_min (by linarith) (by linarith)
    linarith
  · -- t avoids the open interval (s - 2a', 2a - s)
    simp only [toFibre]
    rintro ⟨h1, h2⟩
    exact absurd (hLq (by linarith)) (by linarith)
  · -- t avoids the open interval (2b - s, s - 2b')
    simp only [toFibre]
    rintro ⟨h1, h2⟩
    exact absurd (hRq (by linarith)) (by linarith)

/-- **The containment obligation, discharged** for the part of a sofa inside the band:
its image in fibre coordinates lies in `placedRegion`. -/
theorem sofa_toFibre_subset (S : AmbiSofa) :
    toFibre '' {z ∈ S.carrier | 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ Real.sqrt 2}
      ⊆ placedRegion S.a S.a' S.b S.b' := by
  rintro _ ⟨z, ⟨hz, hband⟩, rfl⟩
  exact toFibre_mem_placedRegion S.a S.a' S.b S.b' z (S.inL hz) (S.inR hz) hband

end MovingSofa
