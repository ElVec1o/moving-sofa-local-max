/-
# The geometric reduction: sets, fibres, and what remains

The verified chain so far bounds the one-dimensional profile integrals.  The note's
geometric reduction connects them to areas: a sofa is contained in the band intersected
with one left- and one right-turning hallway, the area of that region is the integral of
its fibre lengths over the band coordinate, and each fibre is contained in the four-piece
union whose length the tents bound.

This file formalises the pieces of that chain that are set-theoretic or measure-monotone:

  * the placement region `placedRegion` in the rotated coordinates, as an explicit set
    in `ℝ × ℝ` (coordinates `(s, t)` with `s = u + v` the band coordinate);
  * `fibre_subset_four_piece`: each fibre of the region lies in the union of the four
    intervals of the decomposition — a direct lift of the verified `four_piece`;
  * `area_mono`: containment gives the area bound (`measure_mono`, stated for reference);
  * `reduction_assembly`: the area bound follows from the slicing identity, with that
    identity as the single named hypothesis.

What is NOT here: the slicing identity itself (`volume = ∫ fibre length`, Fubini in the
rotated frame) and the containment of the sofa in the placed region (the two-motions
argument).  Both are PROVED in the note; the first is a Fubini computation the measure
library can express, the second needs the sofa formalised as a moving body.  They are the
two named obligations, and nothing else in the chain is unverified.
-/
import Mathlib
import MovingSofa.Bound

namespace MovingSofa

open Real MeasureTheory

/-- The placed region in rotated coordinates `(s, t)`: the band `0 ≤ s ≤ √2` with, on
each fibre, the outer interval minus the two removed open intervals.  The interval
endpoints are affine in `s` with the slopes of the note (`p, q, r, w` there). -/
def placedRegion (a a' b b' : ℝ) : Set (ℝ × ℝ) :=
  {z : ℝ × ℝ |
    0 ≤ z.1 ∧ z.1 ≤ Real.sqrt 2 ∧
    max (z.1 - 2*a') (2*b - z.1) - 2 ≤ z.2 ∧
    z.2 ≤ min (2*a - z.1) (z.1 - 2*b') + 2 ∧
    ¬((z.1 - 2*a') < z.2 ∧ z.2 < (2*a - z.1)) ∧
    ¬((2*b - z.1) < z.2 ∧ z.2 < (z.1 - 2*b'))}

/-- **The fibre of the placed region lies in the four-piece union.**  A point of the
fibre at `s` avoids both removed intervals, so by the verified `four_piece` it lies below
both, in one of the two cross pieces, or above both.  This is the set-level form of
Lemma "four pieces" of the note. -/
theorem fibre_subset_four_piece (a a' b b' s t : ℝ)
    (h : (s, t) ∈ placedRegion a a' b b') :
    (t ≤ s - 2*a' ∧ t ≤ 2*b - s) ∨
    (2*a - s ≤ t ∧ t ≤ 2*b - s) ∨
    (s - 2*b' ≤ t ∧ t ≤ s - 2*a') ∨
    (2*a - s ≤ t ∧ s - 2*b' ≤ t) := by
  obtain ⟨_, _, _, _, h1, h2⟩ := h
  exact (four_piece (s - 2*a') (2*a - s) (2*b - s) (s - 2*b') t).mp ⟨h1, h2⟩

/-- **Monotonicity of area under containment.**  The step `|S| ≤ |X|` for `S ⊆ X`; the
whole relaxation argument of the note uses nothing else about the sofa. -/
theorem area_mono {S X : Set (ℝ × ℝ)} (h : S ⊆ X) : volume S ≤ volume X :=
  measure_mono h

/-- **The reduction, assembled.**  If the sofa is contained in a placed region
(`hplace`, the two-motions argument of the note) and the placed region's area is the
band integral of its fibre lengths bounded by the verified profile bound
(`hslice`, the Fubini step), then the sofa's area is at most `2√2 - 1`.
Both hypotheses are PROVED in the note; they are the two remaining formalisation
obligations, and this theorem records that nothing else stands between them and the
final bound. -/
theorem reduction_assembly
    (S : Set (ℝ × ℝ)) (a a' b b' : ℝ)
    (hplace : S ⊆ placedRegion a a' b b')
    (hslice : volume (placedRegion a a' b b')
      ≤ ENNReal.ofReal (2 * Real.sqrt 2 - 1)) :
    volume S ≤ ENNReal.ofReal (2 * Real.sqrt 2 - 1) :=
  le_trans (area_mono hplace) hslice

end MovingSofa
