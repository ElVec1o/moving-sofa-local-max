/-
Moving sofa — formalization track (paper/PROGRAM.md, Part VI)

This file contains MACHINE-VERIFIED lemmas: every `theorem` below carries a
real proof term — no `sorry`, no placeholder `True := trivial`.

Formalized here:
  • F1  — the superset principle N1 (set-theoretic core + monotone-area
          corollary + the certified-upper-envelope form used by the global
          machine).  This is the load-bearing one-sidedness that makes every
          reconstruction bound in the project an upper bound.
  • F3a — the stationary-contact mechanism (corollary of the rotating-frame
          identities N4), on the coefficient module of trigonometric arcs:
          v + v'' collapses to the constant term, so the envelope speeds
          λ_A = v₁ + v₁'' + 1 and λ_D = −(v₂ + v₂'') are IDENTICALLY constant
          on trigonometric phases, and λ_A ≡ 0 iff the arc is in SOL1 normal
          form (constant −1) — Gerver phase 1 and Σ's first arc.  This is the
          exact source of every cap degeneracy met in the project.
  • F3b — the ambidextrous frame-pair mechanism (N9 core): the identity
          (cu+sv)² + (cu−sv)² = 2c²u² + 2s²v² and the coercivity bound
          2m(u²+v²) ≤ 2c²u² + 2s²v² for any common lower bound m of c², s² —
          instantiated at (c,s) = (cos θ, sin θ) this is the exact modulus
          2·min(sin²θ, cos²θ) by which the two hallway families' ν-frames
          (an angle 2θ apart) jointly control the full gradient on Σ's cap
          phases: the origin of the weight w_μ.

Deliberately NOT yet formalized (tracked in PROGRAM.md):
  • F1b — the plane-topology inclusion "the chord-closed frozen reconstruction
          contains the true body" (needs interior/frontier: Mathlib).
  • F2  — exact-degree reduction N2 (polynomial algebra over arc integrals).
  • F3  — the full rotating-frame identities N4 (needs a Fourier-module
          product API or Mathlib `deriv`), and the analytic bridge
          eval ∘ D = d/dt ∘ eval for the formal derivative below.
  • F5  — the arb-enclosure import interface.

The former Float-based demo skeleton was removed: Float carries no proofs,
and placeholder theorems misrepresent the state of verification.
-/

namespace MovingSofa

/-! ## F1 — the superset principle (N1)

Sets are predicates; no imports needed.  `famInter H P` is the intersection
of the subfamily {H t : P t} of a constraint family H : ι → Set α.  The
moving-sofa instance: α = ℝ², ι = rotation angles (plus wall labels),
H t = the hallway constraint set at angle t, `fullInter H` = the sofa body.
A frozen reconstruction keeps only finitely many constraints — a subfamily. -/

def SetP (α : Type _) := α → Prop

/-- Subset relation for predicate-sets. -/
def SetP.Subset {α : Type _} (S R : SetP α) : Prop := ∀ ⦃x⦄, S x → R x

/-- Intersection of the subfamily of `H` selected by `P`. -/
def famInter {α ι : Type _} (H : ι → SetP α) (P : ι → Prop) : SetP α :=
  fun x => ∀ t, P t → H t x

/-- The full intersection (the true body). -/
def fullInter {α ι : Type _} (H : ι → SetP α) : SetP α :=
  famInter H (fun _ => True)

/-- **N1a.** Keeping fewer constraints can only enlarge the intersection. -/
theorem famInter_antitone {α ι : Type _} (H : ι → SetP α) {P Q : ι → Prop}
    (hPQ : ∀ t, P t → Q t) :
    SetP.Subset (famInter H Q) (famInter H P) :=
  fun _ hx t hPt => hx t (hPQ t hPt)

/-- **N1b (superset principle).** Every subfamily reconstruction contains
    the true body. -/
theorem superset_principle {α ι : Type _} (H : ι → SetP α) (P : ι → Prop) :
    SetP.Subset (fullInter H) (famInter H P) :=
  famInter_antitone H (fun _ _ => True.intro)

/-- **N1c.** Monotone-area corollary: for any area functional `μ` that is
    monotone under inclusion (Lebesgue measure is), the reconstruction area
    bounds the true area.  `β` is any ordered value type (ℝ in the paper). -/
theorem area_bound {α ι β : Type _} [LE β]
    (μ : SetP α → β)
    (mono : ∀ {S R : SetP α}, SetP.Subset S R → μ S ≤ μ R)
    (H : ι → SetP α) (P : ι → Prop) :
    μ (fullInter H) ≤ μ (famInter H P) :=
  mono (superset_principle H P)

/-- **N1d (certified upper envelope).**  Along ANY deformation ε ↦ H ε of the
    constraint family, a per-ε subfamily choice gives an upper bound for the
    true area at EVERY deformation parameter simultaneously — the exact
    statement consumed by the frozen-reconstruction ray/cell certificates
    (the frozen area being a polynomial in ε is N2/F2, separate). -/
theorem certified_upper_envelope {α ι E β : Type _} [LE β]
    (μ : SetP α → β)
    (mono : ∀ {S R : SetP α}, SetP.Subset S R → μ S ≤ μ R)
    (H : E → ι → SetP α) (P : E → ι → Prop) :
    ∀ ε, μ (fullInter (H ε)) ≤ μ (famInter (H ε) (P ε)) :=
  fun ε => area_bound μ (fun h => mono h) (H ε) (P ε)

/-! ## F3a — the stationary-contact mechanism (N4 corollary)

Trigonometric arcs  v(t) = a·cos t + b·sin t + c  as coefficient triples
over ℤ (the identity is coefficient-linear; ℤ suffices to exhibit it and
keeps every proof decidable).  Formal derivative:
  v' = −a·sin t + b·cos t   ⟹   D(a, b, c) = (b, −a, 0).
The rotating-frame envelope speeds proved in the manuscript are
  λ_A = v₁ + v₁'' + 1,   λ_B = λ_A − 1,   λ_D = −(v₂ + v₂''),   λ_C = λ_D − 1,
so the operator  v ↦ v + D(D v)  is the whole story: on trigonometric
phases it collapses to the constant term, making every envelope speed
identically constant there — and identically ZERO exactly on SOL1-form
arcs.  A stationary contact contributes no mask measure to the second
variation: this is the cap-degeneracy mechanism (Gerver phases 1/5,
Σ phases 1/3) and the origin of the Σ weight w_μ. -/

/-- Trigonometric arc `a·cos t + b·sin t + c` as a coefficient triple. -/
structure Trig where
  a : Int
  b : Int
  c : Int
deriving Repr, DecidableEq

namespace Trig

/-- Formal derivative:  (a·cos + b·sin + c)' = b·cos − a·sin. -/
def D (v : Trig) : Trig := ⟨v.b, -v.a, 0⟩

/-- Constant arc. -/
def const (c : Int) : Trig := ⟨0, 0, c⟩

instance : Add Trig := ⟨fun u v => ⟨u.a + v.a, u.b + v.b, u.c + v.c⟩⟩

/-- The rotating-frame speed operator  L v = v + v''. -/
def L (v : Trig) : Trig := v + D (D v)

/-- **Stationary-contact mechanism.**  On every trigonometric arc the speed
    operator collapses to the constant term:  v + v'' = const c. -/
theorem stationary_contact (v : Trig) : L v = const v.c := by
  cases v with
  | mk a b c =>
    show Trig.mk (a + -a) (b + -b) (c + 0) = Trig.mk 0 0 c
    rw [Int.add_right_neg a, Int.add_right_neg b, Int.add_zero c]

/-- Envelope speed of the A-contact:  λ_A = v₁ + v₁'' + 1  (as an arc). -/
def lamA (v : Trig) : Trig := L v + const 1

/-- λ_A is identically constant on trigonometric phases. -/
theorem lamA_const (v : Trig) : lamA v = const (v.c + 1) := by
  rw [lamA, stationary_contact]
  show Trig.mk (0 + 0) (0 + 0) (v.c + 1) = Trig.mk 0 0 (v.c + 1)
  rw [Int.add_zero]

/-- **The cap law.**  λ_A vanishes identically iff the arc is in SOL1 normal
    form (constant term −1) — Gerver's phase 1 and Σ's first arc both are. -/
theorem lamA_zero_iff (v : Trig) : lamA v = const 0 ↔ v.c = -1 := by
  rw [lamA_const]
  constructor
  · intro h
    have hc := congrArg Trig.c h
    simp only [const] at hc
    omega
  · intro h
    rw [h]
    rfl

/-- Envelope speed of the D-contact:  λ_D = −(v₂ + v₂''). -/
def lamD (v : Trig) : Trig := ⟨-(L v).a, -(L v).b, -(L v).c⟩

/-- λ_D is identically constant on trigonometric phases. -/
theorem lamD_const (v : Trig) : lamD v = const (-v.c) := by
  rw [lamD, stationary_contact]
  show Trig.mk (-(0:Int)) (-(0:Int)) (-v.c) = Trig.mk 0 0 (-v.c)
  rw [Int.neg_zero]

end Trig

/-! ## F3b — the ambidextrous frame-pair mechanism (N9 core)

On Σ's cap phases, each hallway family's only MOVING contacts are its two
ν-slot arcs, and the two families' ν-frames at parameter θ point in
directions ν_{±θ}, an angle 2θ apart.  The pair of masked Wirtinger forms
therefore controls the full gradient with modulus 2·min(sin²θ, cos²θ):
writing (u,v) for the components of η′ in the bisector frame and
(c,s) = (cos θ, sin θ), the coverage is

    ⟨η′, ν_θ⟩² + ⟨η′, ν_{−θ}⟩²  =  (c·u + s·v)² + (c·u − s·v)²
                                =  2c²u² + 2s²v²  ≥  2·min(c²,s²)·(u²+v²).

This is the exact origin of the Σ weight w_μ = min(1, sin²θ/sin²β,
cos²θ/sin²β): the ambidextrous structure repairs its own cap degeneracy at
rate sin²θ.  Machine-verified below over ℤ (the identity and the bound are
coefficient-algebra; the instantiation c = cos θ, s = sin θ is analytic
bridging, tracked as F3). -/

/-- **Frame-pair identity.**  (cu+sv)² + (cu−sv)² = 2(cu)² + 2(sv)². -/
theorem frame_pair_identity (c s u v : Int) :
    (c*u + s*v)*(c*u + s*v) + (c*u - s*v)*(c*u - s*v)
      = 2*((c*u)*(c*u)) + 2*((s*v)*(s*v)) := by
  have h1 : (c*u + s*v)*(c*u + s*v)
      = (c*u)*(c*u) + (c*u)*(s*v) + ((s*v)*(c*u) + (s*v)*(s*v)) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
  have h2 : (c*u - s*v)*(c*u - s*v)
      = (c*u)*(c*u) - (c*u)*(s*v) - ((s*v)*(c*u) - (s*v)*(s*v)) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  rw [h1, h2]
  omega

/-- **Frame-pair coercivity** (hypothesis form: `m` any common lower bound of
    c² and s²; instantiate m = min(c², s²) = min(cos²θ, sin²θ)):
    2m(u² + v²) ≤ 2c²u² + 2s²v² — the weighted-modulus bound. -/
theorem frame_pair_coercive (c s u v m : Int)
    (hmc : m ≤ c*c) (hms : m ≤ s*s) :
    2*m*(u*u + v*v) ≤ 2*((c*u)*(c*u)) + 2*((s*v)*(s*v)) := by
  have hcu : (c*u)*(c*u) = (c*c)*(u*u) := by
    rw [Int.mul_assoc, Int.mul_comm u (c*u), Int.mul_assoc c u u,
        ← Int.mul_assoc c c (u*u)]
  have hsv : (s*v)*(s*v) = (s*s)*(v*v) := by
    rw [Int.mul_assoc, Int.mul_comm v (s*v), Int.mul_assoc s v v,
        ← Int.mul_assoc s s (v*v)]
  rw [hcu, hsv]
  have sq_nonneg : ∀ w : Int, (0:Int) ≤ w*w := by
    intro w
    rw [← Int.natAbs_mul_self]
    exact Int.natCast_nonneg _
  have hu2 : (0:Int) ≤ u*u := sq_nonneg u
  have hv2 : (0:Int) ≤ v*v := sq_nonneg v
  -- (c²−m)·u² ≥ 0 and (s²−m)·v² ≥ 0, expanded, then linear arithmetic
  have t1 : (0:Int) ≤ (c*c - m)*(u*u) :=
    Int.mul_nonneg (Int.sub_nonneg.mpr hmc) hu2
  have t2 : (0:Int) ≤ (s*s - m)*(v*v) :=
    Int.mul_nonneg (Int.sub_nonneg.mpr hms) hv2
  have e0 : 2*m*(u*u + v*v) = 2*(m*(u*u + v*v)) := Int.mul_assoc _ _ _
  have e1 : (c*c - m)*(u*u) = (c*c)*(u*u) - m*(u*u) := Int.sub_mul _ _ _
  have e2 : (s*s - m)*(v*v) = (s*s)*(v*v) - m*(v*v) := Int.sub_mul _ _ _
  have e3 : m*(u*u + v*v) = m*(u*u) + m*(v*v) := Int.mul_add _ _ _
  omega

end MovingSofa
