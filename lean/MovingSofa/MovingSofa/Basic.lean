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
  • F2a — exact-degree reduction (N2 core): bilinear ∘ affine = exact
          quadratic, with the three coefficients explicit — the algebraic
          reason no Taylor remainder exists anywhere in the frozen bounds.
  • F4a — soundness core of the monotone-chain simplicity certificate
          (N10): positive projected steps ⟹ strictly monotone partial sums
          ⟹ path injectivity.
  • F4b — the fan-combination identity (S7″/Lemma 5 core):
          sin(b−a)·μ_t = sin(b−t)·μ_a + sin(t−a)·μ_b as a polynomial
          identity in the six sine/cosine symbols — every interior fan
          normal is a combination of the extremes, the algebraic heart of
          the fan-release theorem that removes the cap kink from the
          certified Σ objective.
  • F4c — the ν-slot collapse identity (Lemma 7a): q² − q′² + s²η′²
          + (scη²)′ = 0 as a polynomial identity — the zeroth-order bulk
          of the ν-slot Wirtinger form cancels exactly; with Hardy's
          inequality this closes the cap tail sector of the Σ-local
          theorem at structural constant 1.
  • F4d — exact homogeneity of a stationary fan (N12 core): the perturbed
          constraints at a frozen fan have no constant term, so the local
          body satisfies K(ε) = ε·K(1) exactly and the fan bite is exactly
          ε²·N — the reason the cap loss is quadratic with a
          non-quadratic-form coefficient.
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

/-! ## F4a — soundness core of the monotone-chain certificate (N10)

The simplicity certificate for frozen reconstructions
(`ray_graph_cert.py`) exempts consecutive traversal pieces whose
velocity enclosures share a positive direction d: the projection onto d
then advances strictly, so the concatenated path is injective.  The
discrete soundness skeleton — positive steps ⟹ strictly monotone
partial sums ⟹ injectivity — machine-verified: -/

/-- Partial sums of a step sequence. -/
def psum (step : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => psum step n + step n

/-- Positive steps give strictly increasing partial sums. -/
theorem psum_strict_mono (step : Nat → Int) (hpos : ∀ n, 0 < step n) :
    ∀ i j, i < j → psum step i < psum step j := by
  intro i j hij
  induction j with
  | zero => omega
  | succ k ih =>
    have hk : psum step (k+1) = psum step k + step k := rfl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · have := ih h
      have := hpos k
      omega
    · subst h
      have := hpos i
      omega

/-- **Chain injectivity.** A path whose d-projection has positive steps
    visits no position twice. -/
theorem chain_injective (step : Nat → Int) (hpos : ∀ n, 0 < step n) :
    ∀ i j, psum step i = psum step j → i = j := by
  intro i j h
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd h (Int.ne_of_lt (psum_strict_mono step hpos i j hij))
  · exact hij
  · exact absurd h.symm (Int.ne_of_lt (psum_strict_mono step hpos j i hij))

/-! ## F4b — the fan-combination identity (S7″ / Lemma 5 core)

The fan-release theorem rests on: every interior normal of a wall fan is
a nonnegative combination of the two extreme normals,
  sin(b−a)·μ_t = sin(b−t)·μ_a + sin(t−a)·μ_b.
Writing (sa,ca), (sb,cb), (st,ct) for the sine/cosine symbols and
expanding the subtraction formulas, this is a POLYNOMIAL identity in six
variables, machine-verified componentwise below (the analytic bridge —
that these symbols are the actual sines/cosines — is Mathlib-track F3). -/

/-- x-component: (sb·ct − cb·st)·ca + (st·ca − ct·sa)·cb
                 = (sb·ca − cb·sa)·ct. -/
theorem fan_combination_x (sa ca sb cb st ct : Int) :
    (sb*ct - cb*st)*ca + (st*ca - ct*sa)*cb
      = (sb*ca - cb*sa)*ct := by
  have e1 : (sb*ct - cb*st)*ca = sb*ct*ca - cb*st*ca := Int.sub_mul _ _ _
  have e2 : (st*ca - ct*sa)*cb = st*ca*cb - ct*sa*cb := Int.sub_mul _ _ _
  have e3 : (sb*ca - cb*sa)*ct = sb*ca*ct - cb*sa*ct := Int.sub_mul _ _ _
  rw [e1, e2, e3]
  have c1 : sb*ct*ca = sb*ca*ct := by
    rw [Int.mul_assoc, Int.mul_comm ct ca, ← Int.mul_assoc]
  have c2 : cb*st*ca = st*ca*cb := by
    rw [Int.mul_comm cb st, Int.mul_assoc, Int.mul_comm cb ca, ← Int.mul_assoc]
  have c3 : ct*sa*cb = cb*sa*ct := by
    rw [Int.mul_comm ct sa, Int.mul_comm (sa*ct) cb, ← Int.mul_assoc]
  omega

/-- y-component: (sb·ct − cb·st)·sa + (st·ca − ct·sa)·sb
                 = (sb·ca − cb·sa)·st. -/
theorem fan_combination_y (sa ca sb cb st ct : Int) :
    (sb*ct - cb*st)*sa + (st*ca - ct*sa)*sb
      = (sb*ca - cb*sa)*st := by
  have e1 : (sb*ct - cb*st)*sa = sb*ct*sa - cb*st*sa := Int.sub_mul _ _ _
  have e2 : (st*ca - ct*sa)*sb = st*ca*sb - ct*sa*sb := Int.sub_mul _ _ _
  have e3 : (sb*ca - cb*sa)*st = sb*ca*st - cb*sa*st := Int.sub_mul _ _ _
  rw [e1, e2, e3]
  have c1 : sb*ct*sa = ct*sa*sb := by
    rw [Int.mul_comm sb ct, Int.mul_assoc, Int.mul_comm sb sa, ← Int.mul_assoc]
  have c2 : st*ca*sb = sb*ca*st := by
    rw [Int.mul_comm (st*ca) sb, Int.mul_comm st ca, ← Int.mul_assoc]
  have c3 : cb*st*sa = cb*sa*st := by
    rw [Int.mul_assoc, Int.mul_comm st sa, ← Int.mul_assoc]
  omega

/-! ## F4c — the ν-slot collapse identity (Lemma 7a core)

The tail-closing identity of the Σ-local theorem: for q = −η·s (the
ν-projection of an x-polarized perturbation), with D(s) = c, D(c) = −s,
D(η) = η′ (symbols; the analytic bridge is F3):

    q² − q′² + s²·η′² + (s·c·η²)′ = 0

identically as a POLYNOMIAL in (η, η′, s, c) — the zeroth-order bulk of
the ν-slot Wirtinger form cancels exactly, leaving −∫s²η′² plus pure
boundary terms. Expanding q′ = −η′s − ηc and (scη²)′ =
(c² − s²)η² + 2scηη′, the claim is: -/

/-- **ν-slot collapse.**  (ηs)² − (η′s + ηc)² + s²η′²
    + ((c² − s²)η² + 2scηη′) = 0. -/
theorem nu_slot_collapse (η η' s c : Int) :
    (η*s)*(η*s) - (η'*s + η*c)*(η'*s + η*c) + (s*s)*(η'*η')
      + ((c*c - s*s)*(η*η) + 2*((s*c)*(η*η'))) = 0 := by
  have h1 : (η*s)*(η*s) = (s*s)*(η*η) := by
    rw [Int.mul_assoc, Int.mul_comm s (η*s), Int.mul_assoc η s s,
        ← Int.mul_assoc η η (s*s), Int.mul_comm (η*η) (s*s)]
  have h2 : (η'*s + η*c)*(η'*s + η*c)
      = (η'*s)*(η'*s) + (η'*s)*(η*c) + ((η*c)*(η'*s) + (η*c)*(η*c)) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
  have h3 : (η'*s)*(η'*s) = (s*s)*(η'*η') := by
    rw [Int.mul_assoc, Int.mul_comm s (η'*s), Int.mul_assoc η' s s,
        ← Int.mul_assoc η' η' (s*s), Int.mul_comm (η'*η') (s*s)]
  have h4 : (η*c)*(η*c) = (c*c)*(η*η) := by
    rw [Int.mul_assoc, Int.mul_comm c (η*c), Int.mul_assoc η c c,
        ← Int.mul_assoc η η (c*c), Int.mul_comm (η*η) (c*c)]
  have h5 : (η'*s)*(η*c) = (s*c)*(η*η') := by
    rw [Int.mul_assoc η' s (η*c), ← Int.mul_assoc s η c,
        Int.mul_comm s η, Int.mul_assoc η s c,
        ← Int.mul_assoc η' η (s*c), Int.mul_comm η' η,
        Int.mul_comm (η*η') (s*c)]
  have h6 : (η*c)*(η'*s) = (s*c)*(η*η') := by
    rw [Int.mul_assoc η c (η'*s), ← Int.mul_assoc c η' s,
        Int.mul_comm c η', Int.mul_assoc η' c s,
        ← Int.mul_assoc η η' (c*s), Int.mul_comm c s,
        Int.mul_comm (η*η') (s*c)]
  have h7 : (c*c - s*s)*(η*η) = (c*c)*(η*η) - (s*s)*(η*η) :=
    Int.sub_mul _ _ _
  omega

/-! ## F4d — exact homogeneity of a stationary fan (N12 core)

At a stationary wall fan every constraint line passes through one point P.
In u = x − P the perturbed constraints read ⟨u, n_i⟩ ≤ ε·φ_i, with NO
constant term — so the whole local configuration is exactly ε times a
fixed one, and the area lost to the interior lines is exactly ε² times a
fixed functional (the fan-bite N).  The scaling covariance that makes this
exact, for any linear functional and any ε > 0: -/

/-- **Fan homogeneity.**  ⟨ε·v, n⟩ ≤ ε·c  ⟺  ⟨v, n⟩ ≤ c  for ε > 0.
    Hence K(ε) = ε·K(1) exactly, and |W(ε) \ K(ε)| = ε²·|W(1) \ K(1)|. -/
theorem fan_homogeneity {V : Type _} (L : V → Int) (smul : Int → V → V)
    (hL : ∀ (e : Int) (v : V), L (smul e v) = e * L v)
    (e c : Int) (v : V) (he : 0 < e) :
    L (smul e v) ≤ e * c ↔ L v ≤ c := by
  rw [hL]
  constructor
  · intro h
    exact Int.le_of_mul_le_mul_left h he
  · intro h
    exact Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt he)

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

/-! ## F2a — exact-degree reduction (N2 core)

The Green functional of a reconstruction is BILINEAR in the boundary jet,
and a frozen reconstruction's jet is AFFINE in the deformation parameter;
hence the frozen area is EXACTLY a quadratic polynomial — no Taylor
remainder exists.  The algebraic engine, machine-verified over an abstract
carrier with hypothesis-packaged bilinearity (instantiated in the paper by
the Green form on boundary jets and by Int/ℝ-scaling): -/

/-- **Exact-degree identity.**  For B bilinear (additive in each slot,
    scalar-homogeneous) and the affine family x(ε) = x₀ + ε·d:
    B(x(ε), x(ε)) = B(x₀,x₀) + ε·(B(x₀,d) + B(d,x₀)) + ε²·B(d,d). -/
theorem exact_degree {M : Type _} (B : M → M → Int)
    (add : M → M → M) (smul : Int → M → M)
    (hL : ∀ u v w, B (add u v) w = B u w + B v w)
    (hR : ∀ u v w, B u (add v w) = B u v + B u w)
    (hLs : ∀ (n : Int) u w, B (smul n u) w = n * B u w)
    (hRs : ∀ (n : Int) u w, B u (smul n w) = n * B u w)
    (x0 d : M) (e : Int) :
    B (add x0 (smul e d)) (add x0 (smul e d))
      = B x0 x0 + e * (B x0 d + B d x0) + e * e * B d d := by
  rw [hL, hR, hR, hRs, hLs, hRs, hLs]
  have h : e * (B x0 d + B d x0) = e * B x0 d + e * B d x0 :=
    Int.mul_add _ _ _
  have h2 : e * (e * B d d) = e * e * B d d :=
    (Int.mul_assoc e e (B d d)).symm
  rw [h, h2]
  simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]

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
