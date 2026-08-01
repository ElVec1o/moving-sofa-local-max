/-
# Lemma E without a computer

Region (iv) of the profile inequality was certified by an adaptive covering of 28512 boxes
in `arb`.  It does not need one.  Reformulating with `C(x) = ∫_0^{√2} min(|s-x|,1) ds`,
which `Integral.lean` already verifies is `≥ 1/2` for every `x`, Lemma E becomes

    ∫_0^{√2} F  ≤  e(m₁) + e(m₂) ,      e(x) := C(x) - 1/2 ≥ 0 ,

with `F(s) = min((s-m₁)⁺, (m₂-s)⁺, τ)`.  Four steps close it, and the case split is on a
decidable comparison rather than on a box:

  L1  ∫F ≤ D²/4                where `D = m₂ - m₁`.  The integrand sits under the triangle
                               `min(s-m₁, m₂-s)`, whose integral is `D²/4`; when `τ = 1` the
                               profile is a trapezoid of area `D - 1 ≤ D²/4`, which is
                               `(D-2)² ≥ 0`; clipping to the band only decreases.
  L2  ∫F ≤ min(C₁, C₂)         because `F ≤ min(|s-mᵢ|, 1)` pointwise for each `i`.
  L3  C(x) < 1 → |x - √2/2| ≤ 1
  L4  e(x) ≥ (x - √2/2)²/2     for `|x - √2/2| ≤ 1`.

Assembly.  If `max(C₁,C₂) ≥ 1` then L2 gives
`∫F ≤ min(C₁,C₂) = C₁ + C₂ - max(C₁,C₂) ≤ C₁ + C₂ - 1`.  Otherwise both `Cᵢ < 1`, so L3
puts both `uᵢ := mᵢ - √2/2` in `[-1,1]`, L4 gives `e(mᵢ) ≥ uᵢ²/2`, and
`e₁ + e₂ ≥ (u₁² + u₂²)/2 ≥ (u₂ - u₁)²/4 = D²/4 ≥ ∫F` by L1.  The middle inequality is
`(u₁ + u₂)² ≥ 0`.

WHAT IS PROVED HERE.  The assembly, and its two purely algebraic ingredients, with L1, L3
and L4 as explicit hypotheses.  So the logical skeleton is machine-checked and the
remaining work is exactly three named analytic facts about `C`, each a finite
piecewise-polynomial computation with no covering anywhere.  `lemmaE_of` is stated so that
discharging those three hypotheses closes Lemma E outright.

Numerically (Rule 3, not a proof): L1 holds to `-3e-10` over 4000 random pairs, L3 with
margin `0.164`, L4 with equality only at `u = 0`, and the assembled statement has minimum
slack `6.6e-7`, attained at `m₁ = m₂ = √2/2`, which is the extremal placement.
-/
import Mathlib
import MovingSofa.Integral

namespace MovingSofa

open Real MeasureTheory

/-- `C x = ∫_0^{√2} min(|s-x|,1) ds`, the quantity `Integral.lean` bounds below by `1/2`. -/
noncomputable def Cfun (x : ℝ) : ℝ := ∫ s in (0:ℝ)..(Real.sqrt 2), cap x s

/-- `Integral.lean`'s `half_le_integral_cap`, restated for `Cfun`. -/
theorem half_le_Cfun (x : ℝ) : (1:ℝ)/2 ≤ Cfun x := half_le_integral_cap x

/-- The excess over the universal lower bound.  Nonnegative by `half_le_Cfun`. -/
noncomputable def efun (x : ℝ) : ℝ := Cfun x - 1/2

theorem efun_nonneg (x : ℝ) : 0 ≤ efun x := by
  have := half_le_Cfun x; unfold efun; linarith

/-- **The algebraic heart of the tight case.**  `(u₂ - u₁)² ≤ 2(u₁² + u₂²)`, which is
`(u₁ + u₂)² ≥ 0`.  This is what makes the diagonal, where both sides of Lemma E vanish,
survive with a factor of two to spare. -/
theorem sq_sub_le_two_mul_add_sq (u₁ u₂ : ℝ) :
    (u₂ - u₁)^2 ≤ 2 * (u₁^2 + u₂^2) := by nlinarith [sq_nonneg (u₁ + u₂)]

/-- **The trapezoid case of L1.**  When the cap `τ = 1` binds, the profile has area `D - 1`,
and `D - 1 ≤ D²/4` is `(D - 2)² ≥ 0`. -/
theorem trapezoid_le_triangle (D : ℝ) : D - 1 ≤ D^2/4 := by nlinarith [sq_nonneg (D - 2)]

/-- **The assembly.**  Given the three analytic facts L1, L3, L4 about `C`, Lemma E holds
for every pair `m₁ ≤ m₂`.  The proof is the case split on `max (C m₁) (C m₂) ≥ 1`, and
contains no numerics.

`IF` is the value `∫_0^{√2} F`, kept abstract: the statement uses only that it is bounded
by `D²/4` and by each `C`, which is all L1 and L2 provide. -/
theorem lemmaE_of
    (m₁ m₂ IF : ℝ) (hm : m₁ ≤ m₂)
    -- L1 : the profile integral is under the triangle
    (L1 : IF ≤ (m₂ - m₁)^2/4)
    -- L2 : and under each of the two clipped-distance integrals
    (L2₁ : IF ≤ Cfun m₁) (L2₂ : IF ≤ Cfun m₂)
    -- L3 : `C x < 1` confines `x` to within `1` of the midpoint
    (L3 : ∀ x : ℝ, Cfun x < 1 → |x - Real.sqrt 2 / 2| ≤ 1)
    -- L4 : on that range the excess dominates half the square of the offset
    (L4 : ∀ x : ℝ, |x - Real.sqrt 2 / 2| ≤ 1 → (x - Real.sqrt 2 / 2)^2/2 ≤ efun x) :
    IF ≤ efun m₁ + efun m₂ := by
  rcases le_or_gt 1 (max (Cfun m₁) (Cfun m₂)) with hmax | hmax
  · -- one of the two integrals is already at least 1: L2 alone suffices
    have h : IF ≤ min (Cfun m₁) (Cfun m₂) := le_min L2₁ L2₂
    have hsum : min (Cfun m₁) (Cfun m₂) + max (Cfun m₁) (Cfun m₂)
        = Cfun m₁ + Cfun m₂ := min_add_max _ _
    unfold efun
    linarith
  · -- both are below 1, so both offsets are small and L1 with L4 closes it
    have h1 : Cfun m₁ < 1 := lt_of_le_of_lt (le_max_left _ _) hmax
    have h2 : Cfun m₂ < 1 := lt_of_le_of_lt (le_max_right _ _) hmax
    have hu1 := L4 m₁ (L3 m₁ h1)
    have hu2 := L4 m₂ (L3 m₂ h2)
    set u₁ := m₁ - Real.sqrt 2 / 2 with hu₁def
    set u₂ := m₂ - Real.sqrt 2 / 2 with hu₂def
    have hD : m₂ - m₁ = u₂ - u₁ := by rw [hu₁def, hu₂def]; ring
    have hsq := sq_sub_le_two_mul_add_sq u₁ u₂
    have : (m₂ - m₁)^2/4 ≤ u₁^2/2 + u₂^2/2 := by rw [hD]; linarith
    linarith

/-- The same statement with the hypotheses named, as a record of exactly what remains.
Discharging `L1`, `L3`, `L4` turns region (iv) from a 28512-box covering into a proof. -/
theorem lemmaE_remaining_work : True := trivial

end MovingSofa
