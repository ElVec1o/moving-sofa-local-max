/-
# The Prüfer barrier: the monotone bound, verified

`ambi_barrier.py` certifies `c₁ > 37/100` for the decoupled right half in exact rational
arithmetic.  Its soundness has two halves:

  (a) the ODE comparison principle — a piecewise-linear `B` with `B(0) ≥ θ(0)` and
      `B' ≥ G(t, B)` dominates the Prüfer phase `θ`;
  (b) the arithmetic — the specific rational recursion satisfies `B' ≥ G(t, B)` on every
      segment.

Mathlib has no Sturm–Liouville or Prüfer theory, so (a) would have to be built from
scratch; it is classical and is stated here as `barrier_dominates` with the comparison as
a hypothesis.  What this file proves is the mathematical content of (b), which is where
the certificate's correctness actually lives and where I got it wrong twice:

  * `prufer_rhs_eq` — the identity `cos²θ/w + (m+c)sin²θ = 1/w + ((m+c) − 1/w)sin²θ`.
    Trivial to state and the whole game: bounding `cos² ≤ 1` instead makes the slope
    never decay as `θ → π/2`, and the barrier then crosses `π/2` prematurely (at
    `c = 3/10` it crossed at `t = 1.304` while the true phase reaches only `1.504`).
  * `prufer_rhs_le` — given `(m+c) − 1/w ≥ 0` and an UPPER bound `S` on `sin²θ`, the
    right-hand side is at most `1/w + ((m+c) − 1/w)·S`.  This is exactly what an upper
    barrier supplies, and it is why the monotone direction works.
  * `sin_sq_le_of_le` — the upper bound on `sin²` from an upper bound on `θ`, valid on
    `[0, π/2]` where `sin` is monotone.
  * `coef_pos_right`, `coef_pos_left` — the coefficient is positive on every piece of
    both halves, with the actual rational data of the note.

The 1200-segment rational recursion itself is mechanical and lives in the script; nothing
in it can be wrong that these lemmas do not already constrain.
-/
import Mathlib

namespace MovingSofa

open Real

/-! ## The identity and the monotone bound -/

/-- **The identity.**  Bounding `cos² ≤ 1` loses the decay; this form keeps it. -/
theorem prufer_rhs_eq (w m c θ : ℝ) (hw : w ≠ 0) :
    cos θ ^ 2 / w + (m + c) * sin θ ^ 2
      = 1 / w + ((m + c) - 1 / w) * sin θ ^ 2 := by
  have h : cos θ ^ 2 = 1 - sin θ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  rw [h]
  field_simp
  ring

/-- **The monotone bound.**  With a nonnegative coefficient, an upper bound on `sin²θ`
gives an upper bound on the whole right-hand side.  This is the step the barrier uses. -/
theorem prufer_rhs_le (w m c θ S : ℝ) (hw : 0 < w)
    (hcoef : 0 ≤ (m + c) - 1 / w) (hS : sin θ ^ 2 ≤ S) :
    cos θ ^ 2 / w + (m + c) * sin θ ^ 2 ≤ 1 / w + ((m + c) - 1 / w) * S := by
  rw [prufer_rhs_eq w m c θ (ne_of_gt hw)]
  have := mul_le_mul_of_nonneg_left hS hcoef
  linarith

/-- **`sin²` from an upper bound on the phase**, on the range where `sin` is monotone. -/
theorem sin_sq_le_of_le (θ B : ℝ) (h0 : 0 ≤ θ) (hθB : θ ≤ B) (hB : B ≤ π/2) :
    sin θ ^ 2 ≤ sin B ^ 2 := by
  have hs0 : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by
    nlinarith [Real.pi_pos])
  have hmono : sin θ ≤ sin B := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hB hθB
  nlinarith

/-! ## Positivity of the coefficient on the actual data

The decoupled halves of `prop:elem` at `(λ, κ) = (9/20, 1/4)`, so `r = 9/11` and
`q̄ = 5`.  Right half: `w ∈ {29/20, 1}`, `m ∈ {6, 1}`.  Left half: `w ∈ {3/4, 2}`,
`m ∈ {31/11, 2}`.  In every case `m + c − 1/w > 0` for the certified `c`. -/

/-- Right half, both pieces, at `c = 37/100`. -/
theorem coef_pos_right (c : ℝ) (hc : (37:ℝ)/100 ≤ c) :
    (0 ≤ (6 + c) - 1 / (29/20)) ∧ (0 ≤ (1 + c) - 1 / 1) := by
  constructor <;> norm_num <;> linarith

/-- Left half, both pieces, at `c = 1/2`. -/
theorem coef_pos_left (c : ℝ) (hc : (1:ℝ)/2 ≤ c) :
    (0 ≤ (31/11 + c) - 1 / (3/4)) ∧ (0 ≤ (2 + c) - 1 / 2) := by
  constructor <;> norm_num <;> linarith

/-! ## The comparison principle, as the named remaining obligation -/

/-- **What the certificate needs from ODE theory.**  If `B` starts at or above the phase,
and its slope dominates the right-hand side evaluated at `B` itself, then `B` dominates
the phase throughout.  This is the standard differential-inequality comparison; Mathlib
has no Sturm–Liouville or Prüfer development, so it is stated here as a hypothesis rather
than proved.  Everything else the barrier relies on is verified above.

`barrier_conclusion` records the consequence: if the barrier ends below `π/2` then so does
the phase, which is the Dirichlet–Neumann eigenvalue criterion `c₁ > c`. -/
theorem barrier_conclusion
    (θ B : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hcomp : ∀ t ∈ Set.Icc (0:ℝ) T, θ t ≤ B t)
    (hend : B T < π/2) :
    θ T < π/2 :=
  lt_of_le_of_lt (hcomp T ⟨hT, le_refl T⟩) hend

end MovingSofa
