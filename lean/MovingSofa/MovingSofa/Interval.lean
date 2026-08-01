/-
# Verified interval arithmetic over the rationals

The unconditional bound has exactly two steps still certified outside Lean: the second
variation, and region (iv) of the profile inequality.  Both are adaptive coverings in `arb`
ball arithmetic.  Porting them needs an interval layer whose SOUNDNESS is proved, not
assumed, which is what this file is: rational endpoints, real membership, and one soundness
theorem per operation.

Rational endpoints rather than floating point, so that no rounding argument is needed
anywhere: `ℚ` is exact, and the only approximation is the width of the interval, which is
carried explicitly.  Irrational constants enter through `Iv` values that provably contain
them (`sqrt2I` below), never as literals.

WHAT IS AND IS NOT HERE.  This is the arithmetic layer only.  It makes an enclosure of a
piecewise-linear expression checkable inside Lean, which is the prerequisite for a verified
covering.  The covering itself, and the reduction of region (iv) to it, are NOT in this
file and are still `PROVED` rather than `VERIFIED`; see the note.
-/
import Mathlib

namespace MovingSofa

/-- A closed interval with rational endpoints.  Empty when `lo > hi`; every soundness
theorem below is a one-directional containment, so emptiness is harmless. -/
structure Iv where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

namespace Iv

/-- `x` lies in the interval, as a statement about a real number. -/
def Mem (I : Iv) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

instance : Membership ℝ Iv := ⟨fun I x => I.Mem x⟩

theorem mem_def {I : Iv} {x : ℝ} : x ∈ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) := Iff.rfl

/-- The exact interval around a rational. -/
def pt (q : ℚ) : Iv := ⟨q, q⟩

theorem pt_sound (q : ℚ) : ((q : ℝ)) ∈ pt q := ⟨le_refl _, le_refl _⟩

def add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩

theorem add_sound {I J : Iv} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ I.add J := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> · simp only [add, Rat.cast_add]; linarith

def neg (I : Iv) : Iv := ⟨-I.hi, -I.lo⟩

theorem neg_sound {I : Iv} {x : ℝ} (hx : x ∈ I) : -x ∈ I.neg := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> · simp only [neg, Rat.cast_neg]; linarith

def sub (I J : Iv) : Iv := I.add J.neg

theorem sub_sound {I J : Iv} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) : x - y ∈ I.sub J := by
  have := add_sound hx (neg_sound hy)
  simpa [sub, sub_eq_add_neg] using this

/-- Scaling by a nonnegative rational.  Kept separate from general multiplication because
every use in the profile inequality is by an explicit positive constant. -/
def smulNonneg (c : ℚ) (I : Iv) : Iv := ⟨c * I.lo, c * I.hi⟩

theorem smulNonneg_sound {c : ℚ} (hc : 0 ≤ c) {I : Iv} {x : ℝ} (hx : x ∈ I) :
    (c : ℝ) * x ∈ smulNonneg c I := by
  obtain ⟨h1, h2⟩ := hx
  have hc' : (0:ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  constructor <;> · simp only [smulNonneg, Rat.cast_mul]; nlinarith

/-- Interval `min`, endpoint-wise, which is exact because `min` is monotone in both
arguments. -/
def min' (I J : Iv) : Iv := ⟨Min.min I.lo J.lo, Min.min I.hi J.hi⟩

theorem min_sound {I J : Iv} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) :
    Min.min x y ∈ I.min' J := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  refine ⟨?_, ?_⟩
  · simp only [min', Rat.cast_min]; exact min_le_min h1 h3
  · simp only [min', Rat.cast_min]; exact min_le_min h2 h4

/-- Interval `max`, endpoint-wise. -/
def max' (I J : Iv) : Iv := ⟨Max.max I.lo J.lo, Max.max I.hi J.hi⟩

theorem max_sound {I J : Iv} {x y : ℝ} (hx : x ∈ I) (hy : y ∈ J) :
    Max.max x y ∈ I.max' J := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  refine ⟨?_, ?_⟩
  · simp only [max', Rat.cast_max]; exact max_le_max h1 h3
  · simp only [max', Rat.cast_max]; exact max_le_max h2 h4

/-- `|x|`, via `max x (-x)`. -/
def abs' (I : Iv) : Iv := I.max' I.neg

theorem abs_sound {I : Iv} {x : ℝ} (hx : x ∈ I) : |x| ∈ I.abs' := by
  have h := max_sound hx (neg_sound hx)
  simpa [abs', abs_eq_max_neg] using h

/-- The decidable test that certifies a strict lower bound on everything in the interval. -/
def posBelow (I : Iv) (c : ℚ) : Bool := decide (c < I.lo)

theorem posBelow_sound {I : Iv} {c : ℚ} {x : ℝ} (hx : x ∈ I) (h : I.posBelow c = true) :
    (c : ℝ) < x := by
  have : c < I.lo := by simpa [posBelow] using h
  have : (c : ℝ) < (I.lo : ℝ) := by exact_mod_cast this
  exact lt_of_lt_of_le this hx.1

/-- An enclosure of `sqrt 2`, with rational endpoints, verified against `sqrt 2 ^ 2 = 2`.
Irrational constants enter the arithmetic only this way. -/
def sqrt2I : Iv := ⟨14142135 / 10000000, 14142136 / 10000000⟩

theorem sqrt2I_sound : Real.sqrt 2 ∈ sqrt2I := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · show ((14142135 / 10000000 : ℚ) : ℝ) ≤ Real.sqrt 2
    push_cast
    nlinarith [h2, hnn]
  · show Real.sqrt 2 ≤ ((14142136 / 10000000 : ℚ) : ℝ)
    push_cast
    nlinarith [h2, hnn]

end Iv

end MovingSofa
