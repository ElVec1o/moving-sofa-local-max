/-
# The second variation: the elementary constant, assembled

Proposition "an elementary constant" of the note proves `(1/2)δ²Q ≤ -(1/12)‖η‖²` on the
cell with no transfer matrices and no ball arithmetic.  This file machine-checks its
skeleton in the same style that closed Lemma E: the two decoupling inequalities are proved
outright (pure algebra), and the assembly from the analytic inputs to the constant
`1/12` is proved outright (pure arithmetic over the integral values), with the five
analytic inputs — three Poincaré-type inequalities on intervals, one tail cut, one
subset-monotonicity — as named hypotheses.

Mathlib has no one-dimensional Poincaré/Wirtinger inequality today, so those five inputs
are exactly the open obligations; each is a standard fact about `∫` on an interval.  The
assembly `secondvar_assembly` consumes only real numbers and inequalities between them,
so its proof is complete and independent of how the inputs are eventually discharged.

The numbers: `λ = 9/20`, `κ = 1/4`, hence `r = 9/11` and `q̄ = 5`; `β ≤ 3/10` and
`π/2 ≤ 1.5708` are the only facts about the geometry used.  Left half:
`4(1-κ) - 2 - r = 2/11`.  Right half: absorption `9/40`, cut constants `11/5` and
`9/50`, giving `369/4400`.  Both exceed `1/12`.
-/
import Mathlib

namespace MovingSofa

open Real

/-! ## The two decoupling inequalities, proved -/

/-- **Decoupling on `E₂`.**  `(a+b)² ≥ λb² - r a²` with `r = λ/(1-λ)`, for `0 < λ < 1`.
Stated multiplied through by `(1-λ) > 0` to stay polynomial. -/
theorem decouple_E2 (lam a b : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    lam * b^2 - (lam/(1-lam)) * a^2 ≤ (a + b)^2 := by
  have hpos : 0 < 1 - lam := by linarith
  rw [← sub_nonneg]
  have expand : (a+b)^2 - (lam*b^2 - lam/(1-lam)*a^2) = (a+(1-lam)*b)^2/(1-lam) := by
    field_simp
    ring
  rw [expand]
  positivity

/-- **Decoupling on `E₁`.**  `(x-y)² ≤ (1+1/κ)x² + (1+κ)y²` for `κ > 0`. -/
theorem decouple_E1 (kap x y : ℝ) (hk : 0 < kap) :
    (x - y)^2 ≤ (1 + 1/kap) * x^2 + (1 + kap) * y^2 := by
  rw [← sub_nonneg]
  have expand : (1 + 1/kap) * x^2 + (1 + kap) * y^2 - (x-y)^2 = (x + kap*y)^2/kap := by
    field_simp
    ring
  rw [expand]
  positivity

/-! ## The assembly

All quantities are the values of the integrals, taken as real numbers:

  `Pg = ∫₀^{π/2} p'²`, `Pm = ∫₀^{π/2} p²`   (left half)
  `Qg = ∫₀^{π/2} q'²`, `Qm = ∫₀^{π/2} q²`   (right half, totals)
  `Qgc = ∫₀^c q'²`,   `Qgt = ∫_c^{π/2} q'²` (split at `c = π/2 - β`)
  `Qmb = ∫₀^β q²`,    `Qgb = ∫₀^β q'²`      (the heavy-mass zone)
  `FL`, `FR`: the two half-forms after decoupling.

The hypotheses `hGL`, `hGR` say the decoupled forms dominate the stated combinations,
which is what `decouple_E2`/`decouple_E1` provide pointwise; `hW4`, `hW1` are the
Dirichlet–Dirichlet and Dirichlet–Neumann Poincaré inequalities; `habs` is the
half-Poincaré inequality on `[0,β)`; `hcut` is the tail cut; `hsub` is monotonicity of
the gradient integral under `[0,β) ⊆ [0,c)`.  Every input is an inequality between
integrals that a later file can discharge one at a time. -/
theorem secondvar_assembly
    (Pg Pm Qg Qm Qgc Qgt Qmb Qgb FL FR : ℝ)
    (hPm : 0 ≤ Pm) (hQm : 0 ≤ Qm) (hQgt : 0 ≤ Qgt) (hQgb : 0 ≤ Qgb)
    -- the split is exact: total gradient = inner + tail
    (hsplit : Qg = Qgc + Qgt)
    -- decoupled half-forms (from decouple_E1/E2 with λ=9/20, κ=1/4)
    (hGL : (3/4) * Pg - (2 + 9/11) * Pm ≤ FL)
    (hGR : Qg + (9/20) * Qgc - Qm - 5 * Qmb ≤ FR)
    -- Poincaré inequalities
    (hW4 : 4 * Pm ≤ Pg)                    -- Dirichlet–Dirichlet on [0, π/2]
    (hW1 : Qm ≤ Qg)                        -- Dirichlet–Neumann on [0, π/2]
    (habs : Qmb ≤ (9/200) * Qgb)           -- half-Poincaré, β²/2 ≤ 9/200
    (hsub : Qgb ≤ Qgc)                     -- [0,β) ⊆ [0,c)
    (hcut : Qm ≤ (11/5) * Qgc + (9/50) * Qgt) :  -- the tail cut
    (1/12) * Pm ≤ FL ∧ (1/12) * Qm ≤ FR := by
  constructor
  · -- left half: 3/4·4 - 2 - 9/11 = 2/11 ≥ 1/12
    nlinarith [hGL, hW4, hPm]
  · -- right half: absorption 9/40, then the cut, then DN Poincaré: 369/4400 ≥ 1/12
    have habs' : 5 * Qmb ≤ (9/40) * Qgc := by nlinarith [habs, hsub, hQgb]
    have hQgc : (5/11) * Qm - (9/110) * Qgt ≤ Qgc := by nlinarith [hcut]
    nlinarith [hGR, habs', hQgc, hW1, hsplit, hQm, hQgt]

/-- The combined constant: both halves at least `1/12` of their mass gives the form at
least `1/12` of the total mass.  `‖η‖² = Pm + Qm`. -/
theorem secondvar_combined
    (Pm Qm FL FR : ℝ)
    (hL : (1/12) * Pm ≤ FL) (hR : (1/12) * Qm ≤ FR) :
    (1/12) * (Pm + Qm) ≤ FL + FR := by linarith

end MovingSofa
