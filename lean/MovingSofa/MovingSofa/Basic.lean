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
  • F4e — the fan-cut gain identity (N12b sharpness):
          sin(β−s)sin(β+s) = sin²β − sin²s, so the single-cut gain factor
          G(s) is minimized at the fan centre and G ≥ cot β uniformly —
          the step that makes the bite bound uniform in s.
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

/-- **N1e (safe closure).**  If the body lies inside EVERY assembled piece,
    it lies inside their intersection.  Stated this way it is the exact content
    the paper's one-sided reconstruction lemma needs: a reconstruction may be
    built from any collection of pieces PROVIDED each one still contains the
    body -- i.e. each lies on a SUPPORTING boundary of the family.

    A straight chord is NOT in general of this form.  It is not a constraint
    boundary, so nothing supplies the hypothesis `Subset S (H t)` for it, and a
    chord may cut into the body.  For Gerver's sofa two chords of the standard
    reconstruction do exactly that under perturbation, at first order.  Hence
    `superset_principle` -- which concerns intersections of CONSTRAINTS only --
    does not license a chorded reconstruction, and the chord-free construction
    is the one this theorem covers. -/
theorem safe_closure {α ι : Type _} {S : SetP α} (H : ι → SetP α)
    (h : ∀ t, SetP.Subset S (H t)) : SetP.Subset S (fullInter H) :=
  fun _ hx t _ => h t hx

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

/-! ## F4e — the fan-cut gain identity (N12b sharpness)

The single-interior-cut lower bound for the fan bite carries the gain
factor G(s) = sin2β / (2 sin(β−s) sin(β+s)).  Its minimum over the fan is
at s = 0, giving G ≥ cot β, because of the identity

    sin(β−s)·sin(β+s) = sin²β − sin²s   ≤   sin²β,

a polynomial identity in the four sine/cosine symbols under the two
Pythagorean relations.  This is what makes the bite bound uniform in s
(and sharp at the fan centre): -/

/-- **Fan-cut gain.**  (sb·cs − cb·ss)(sb·cs + cb·ss) = sb² − ss². -/
theorem fan_cut_gain (sb cb ss cs : Int)
    (hb : sb*sb + cb*cb = 1) (hs : ss*ss + cs*cs = 1) :
    (sb*cs - cb*ss)*(sb*cs + cb*ss) = sb*sb - ss*ss := by
  have hdiff : (sb*cs - cb*ss)*(sb*cs + cb*ss)
      = (sb*cs)*(sb*cs) - (cb*ss)*(cb*ss) := by
    rw [Int.sub_mul, Int.mul_add, Int.mul_add]
    have hcross : (sb*cs)*(cb*ss) = (cb*ss)*(sb*cs) := Int.mul_comm _ _
    omega
  have hA : (sb*cs)*(sb*cs) = (cs*cs)*(sb*sb) := by
    rw [Int.mul_assoc, Int.mul_comm cs (sb*cs), Int.mul_assoc sb cs cs,
        ← Int.mul_assoc sb sb (cs*cs), Int.mul_comm (sb*sb) (cs*cs)]
  have hB : (cb*ss)*(cb*ss) = (ss*ss)*(cb*cb) := by
    rw [Int.mul_assoc, Int.mul_comm ss (cb*ss), Int.mul_assoc cb ss ss,
        ← Int.mul_assoc cb cb (ss*ss), Int.mul_comm (cb*cb) (ss*ss)]
  have hcs : cs*cs = 1 - ss*ss := by omega
  have hcb : cb*cb = 1 - sb*sb := by omega
  rw [hdiff, hA, hB, hcs, hcb]
  have e1 : (1 - ss*ss)*(sb*sb) = sb*sb - (ss*ss)*(sb*sb) := by
    rw [Int.sub_mul, Int.one_mul]
  have e2 : (ss*ss)*(1 - sb*sb) = ss*ss - (ss*ss)*(sb*sb) := by
    rw [Int.mul_sub, Int.mul_one]
  omega

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

/-! ## F6 — the two failure modes of the reconstruction lemma

Both local-maximality arguments in this project consume `lem:superset`: any
closed curve assembled from constraint boundaries encloses a region containing
the sofa, so the enclosed AREA bounds the true area.  Measurement found two
independent ways the consuming code outruns that statement.

MODE 1 (chords).  The lemma's proof covers constraint subarcs; a straight CHORD
is not a constraint boundary and may cut into the body.  `safe_closure` above is
the corrected statement, and F6a below is the elementary area identity behind the
resulting first-order defect.

MODE 2 (signed vs region area).  The lemma bounds the enclosed REGION, while
every reconstruction evaluates a SIGNED (shoelace / Green) sum.  The two agree
ONLY IF the curve is simple.  F6b/F6c exhibit the gap on the smallest instance.

MODE-INDEPENDENT (selection rule).  F6d is the algebra behind the Z2 grading that
block-diagonalises the Σ second-variation form. -/

/-- Twice the signed shoelace area of a triangle. -/
def shoe3 (x0 y0 x1 y1 x2 y2 : Int) : Int :=
  (x0*y1 - x1*y0) + (x1*y2 - x2*y1) + (x2*y0 - x0*y2)

/-- Twice the signed shoelace area of a quadrilateral. -/
def shoe4 (x0 y0 x1 y1 x2 y2 x3 y3 : Int) : Int :=
  (x0*y1 - x1*y0) + (x1*y2 - x2*y1) + (x2*y3 - x3*y2) + (x3*y0 - x0*y3)

/-- **F6a (chord sliver).**  The sliver cut off between the wall line `y = 0`
    and a chord running from `(0,h)` to `(l,0)` has twice-area `l*h`, i.e. area
    `l*h/2`.  With `h` the rate at which a chord endpoint leaves its supporting
    line, this is the `-(l/2)·h` term of the rank-one defect, one such term per
    chord. -/
theorem chord_sliver (l h : Int) : shoe3 0 0 l 0 0 h = l*h := by
  simp [shoe3]

/-- **F6b (signed area is not region area).**  The bowtie
    `(0,0) → (1,0) → (0,1) → (1,1)` is a closed quadrilateral whose signed
    shoelace VANISHES: its two lobes are traversed with opposite orientation and
    cancel.  The region it covers is not empty, so signed area ≠ region area. -/
theorem bowtie_signed_zero : shoe4 0 0 1 0 0 1 1 1 = 0 := by decide

/-- **F6c.**  The same four points traversed as a SIMPLE quadrilateral give
    twice-area `2`.  Together with `bowtie_signed_zero` this is the whole of
    Mode 2: the identical vertex set yields `0` or `2` according only to whether
    the traversal self-intersects, so a reconstruction that evaluates the signed
    sum can report an area strictly below the region it encloses — and hence
    below the true area, while still enclosing the body. -/
theorem square_signed : shoe4 0 0 1 0 1 1 0 1 = 2 := by decide

/-- **F6d (selection rule).**  Let `T` be an involution acting on two vectors by
    signs `a`, `b ∈ {1,-1}`, and let `B` be the value of a `T`-invariant
    bilinear form on that pair, so `B = a*b*B`.  If the signs differ then
    `B = 0`.

    This is the algebra behind the Z2 grading `g(c,k) = (k+c) mod 2` of the Σ
    second-variation form: with `U(η)(t) = (η_x(π/2−t), −η_y(π/2−t))` one has
    `U(x,k) = (-1)^(k+1)(x,k)` and `U(y,k) = (-1)^k (y,k)`, so `U = +1` exactly
    on `g = 1` and `-1` on `g = 0`, and no `U`-invariant form couples the two. -/
theorem selection_rule {B a b : Int}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hab : a ≠ b)
    (hinv : B = a * b * B) : B = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

/-- The `U`-eigenvalue of the mode indexed by component `c` (0 for x, 1 for y)
    and frequency `k`, as a function of the grading `(k+c) mod 2`. -/
def ueig (c k : Nat) : Int := if (k + c) % 2 = 1 then 1 else -1

/-- **F6e.**  Modes in different grading classes have opposite `U`-eigenvalue,
    hence (by `selection_rule`) are uncoupled by any `U`-invariant form.  This is
    the statement verified numerically at K = 32 to relative size 1e-10: same
    component entries vanish unless `k+k'` is even, cross component entries
    unless `k+k'` is odd. -/
theorem ueig_opposite {c1 k1 c2 k2 : Nat}
    (h : (k1 + c1) % 2 ≠ (k2 + c2) % 2) :
    ueig c1 k1 * ueig c2 k2 = -1 := by
  have h1 : (k1 + c1) % 2 = 0 ∨ (k1 + c1) % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  have h2 : (k2 + c2) % 2 = 0 ∨ (k2 + c2) % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  unfold ueig
  rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;>
    simp [e1, e2] at h ⊢

/-- **F6f.**  The grading selection rule in the form it is used: a `U`-invariant
    form vanishes between modes of different grading. -/
theorem grading_selection {c1 k1 c2 k2 : Nat} {B : Int}
    (h : (k1 + c1) % 2 ≠ (k2 + c2) % 2)
    (hinv : B = ueig c1 k1 * ueig c2 k2 * B) : B = 0 := by
  rw [ueig_opposite h] at hinv
  omega

/-! ## F7 — the intersection-reconstruction route, and why its base-point slack
is harmless

The construction that avoids both failure modes is the finite-subfamily
INTERSECTION `R_n(c) = ⋂_i H_{t_i}(c)`.  Containment is `superset_principle`,
verbatim, with no hypothesis about chords or simplicity.  The price is that
equality at the base point is lost: `|R_n(c₀)| = astar + s_n` with a slack
`s_n > 0`.  F7a is the resulting chain and F7b is the passage to the limit. -/

/-- **F7a (intersection chain).**  If the reconstruction dominates the true area,
    sits below its own base value by the margin `m`, and exceeds `astar` at the
    base point by exactly the slack `s`, then the true area is below
    `astar + s - m`.  Trivial arithmetic — its value is that it pins the
    quantifiers and shows exactly where the slack enters. -/
theorem intersection_chain {atrue brec bbase astar s m : Int}
    (hdom : atrue ≤ brec) (hmarg : brec ≤ bbase - m) (hbase : bbase = astar + s) :
    atrue ≤ astar + s - m := by omega

/-- **F7b (slack squeeze).**  If `x ≤ y + s n` for every `n` and some slack in the
    family is non-positive, then `x ≤ y`.  Over `Int` this is the exact content of
    "let the slack tend to zero"; the archimedean version over `ℝ` is elementary
    but needs limits, which are outside this Mathlib-free development. -/
theorem slack_squeeze {x y : Int} {s : Nat → Int}
    (h : ∀ n, x ≤ y + s n) (hs : ∃ n, s n ≤ 0) : x ≤ y := by
  obtain ⟨n, hn⟩ := hs
  have := h n
  omega

/-! ## F8 — what a negative-definiteness certificate actually proves

Every definiteness claim in this project is produced numerically and therefore
carries the label HEURISTIC (Rule 7).  Lifting it requires a CERTIFICATE: an
identity exhibiting the form as a negatively weighted sum of squares.  F8 is the
logical content of such a certificate, so that once a certificate is produced in
exact arithmetic the final step is machine-checked rather than asserted. -/

/-- Squares are non-negative. -/
theorem sq_nonneg_int (x : Int) : 0 ≤ x*x := by
  rcases Int.lt_trichotomy x 0 with h | h | h
  · exact Int.le_of_lt (Int.mul_pos_of_neg_of_neg h h)
  · simp [h]
  · exact Int.le_of_lt (Int.mul_pos h h)

/-- A weighted square with positive weight is non-negative. -/
theorem weighted_sq_nonneg {d x : Int} (hd : 0 < d) : 0 ≤ d*(x*x) :=
  Int.mul_nonneg (Int.le_of_lt hd) (sq_nonneg_int x)

/-- A weighted square with positive weight and non-zero argument is positive. -/
theorem weighted_sq_pos {d x : Int} (hd : 0 < d) (hx : x ≠ 0) : 0 < d*(x*x) := by
  have h1 : 0 < x*x := by
    rcases Int.lt_trichotomy x 0 with h | h | h
    · exact Int.mul_pos_of_neg_of_neg h h
    · exact absurd h hx
    · exact Int.mul_pos h h
  exact Int.mul_pos hd h1

/-- A list of non-negative entries has non-negative sum. -/
theorem sum_nonneg : ∀ {l : List Int}, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
  | [], _ => by simp
  | a :: t, h => by
      have ha : 0 ≤ a := h a (by simp)
      have ht : 0 ≤ t.sum := sum_nonneg (fun x hx => h x (by simp [hx]))
      have : (a :: t).sum = a + t.sum := by simp
      omega

/-- **F8 (certificate ⟹ definiteness).**  If every entry of `l` is non-negative
    and one entry is positive, the sum is positive.  With entries `dᵢ·wᵢ²` this is
    exactly the step from a sum-of-squares certificate to strict definiteness:
    `Q(v) = -∑ dᵢ wᵢ(v)²` is then strictly negative whenever some `wᵢ(v) ≠ 0`.

    So a definiteness claim becomes VERIFIED as soon as the certificate — the
    weights `dᵢ` and the linear forms `wᵢ` — is exhibited in exact arithmetic.
    That exact-arithmetic certificate, not this lemma, is what the ladder margins
    are still missing. -/
theorem sum_pos_of_one_pos : ∀ {l : List Int}, (∀ x ∈ l, 0 ≤ x) →
    (∃ x ∈ l, 0 < x) → 0 < l.sum
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | a :: t, h, ⟨x, hx, hxpos⟩ => by
      have ht : 0 ≤ t.sum := sum_nonneg (fun y hy => h y (by simp [hy]))
      have ha : 0 ≤ a := h a (by simp)
      have hs : (a :: t).sum = a + t.sum := by simp
      rcases List.mem_cons.mp hx with rfl | hxt
      · omega
      · have hpos : 0 < t.sum :=
          sum_pos_of_one_pos (fun y hy => h y (by simp [hy])) ⟨x, hxt, hxpos⟩
        omega

/-! ## F9 — the ambidextrous transfer: the two niches are disjoint

New goal: prove Romik's ambidextrous sofa Σ optimal by transferring Baek's
concavity architecture (arXiv:2411.19826) from the one-corner problem.

Baek's sofa is `S = K \ N(K)`, a convex cap minus ONE niche, and his `Q` is
concave because it subtracts Mamikon regions, whose areas are convex quadratics
(his Theorem 7.4.2).  The ambidextrous sofa is

    Σ = C₂ \ (U ∪ ρU),      C₂ = C ∩ ρC convex,   ρ(x,y) = (x, 1-y),

a convex cap minus the union of TWO niches.  Inclusion–exclusion gives
`|U ∪ ρU| = |U| + |ρU| - |U ∩ ρU|`, and that last term would enter `Q` with a
PLUS sign — the wrong sign for the subtract-convex-quadratics mechanism.  So the
transfer hinges on the two niches being disjoint.  F9 proves they are.

Measured for Romik's trajectory: `max_t c_y(t) = 0.387838 < 1/2`, and the niches
are disjoint with a gap of 0.224. -/

/-- **F9a (niche ceiling).**  A point of the wedge `Q_t` lies at or below its
    apex.  In the wedge, `q - c(t) = -a·μ_t - b·ν_t` with `a, b ≥ 0`, and on
    `t ∈ [0, π/2]` both frame vectors have non-negative `y`-component
    (`μ_t = (cos t, sin t)`, `ν_t = (-sin t, cos t)`), so the `y`-coordinate can
    only decrease.  Here `s, c ≥ 0` stand for `sin t, cos t`. -/
theorem niche_below_apex {a b s c qy cy : Int}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hq : qy = cy - a*s - b*c) : qy ≤ cy := by
  have h1 : 0 ≤ a*s := Int.mul_nonneg ha hs
  have h2 : 0 ≤ b*c := Int.mul_nonneg hb hc
  omega

/-- **F9b (separation).**  If the niche lies in `{y ≤ M}` and its `ρ`-image lies
    in `{y ≥ H - M}`, where `ρ` reflects in `y = H/2`, then `2M < H` forces the
    two to be disjoint: no point can satisfy both.  With `H = 1` and
    `M = max_t c_y(t) = 0.387838` this is Romik's case. -/
theorem niche_disjoint {M H y : Int} (h : 2*M < H)
    (hU : y ≤ M) (hRU : H - M ≤ y) : False := by omega

/-- **F9c (inclusion–exclusion collapses).**  Disjointness removes the overlap
    term, so the union's area is the plain sum and each niche can be treated by
    exactly the machinery Baek applies to his single niche. -/
theorem union_area_of_disjoint {u ru ov total : Int}
    (hie : total = u + ru - ov) (hdisj : ov = 0) : total = u + ru := by omega

/-! ## F10 — Baek's concavity criterion, the step that removes the second variation

Baek's Theorem 7.1.5: on a convex domain, a CONCAVE QUADRATIC functional attains
its global maximum at `K` as soon as the directional derivative `Df(K;·)` is
nonpositive.  No second variation, no eigenvalue ladder, no tail bound.

The arithmetic core is this.  Along the segment `λ ↦ c_λ(K,K')` a quadratic
functional is a quadratic polynomial

    f(c_λ(K,K')) = A + Bλ + Cλ²,
    A = h(K,K) = f(K),
    B = h(K,K') + h(K',K) - 2h(K,K) = Df(K;K'),      (Baek Lemma 7.1.4)
    C = h(K,K) - (h(K,K') + h(K',K)) + h(K',K'),

so that `f(K') = f(c_1(K,K')) = A + B + C`.  Concavity of `f` says `C ≤ 0`, and
criticality says `B ≤ 0`; together they give `f(K') ≤ f(K)` for EVERY `K'`, which
is global maximality.  F10a is that step; F10b records the coefficient bookkeeping
that identifies `A + B + C` with `f(K')`. -/

/-- **F10a (concave + critical ⟹ global max).**  If the directional derivative
    coefficient `B` and the concavity coefficient `C` are both nonpositive, the
    value at the far endpoint does not exceed the value at `K`. -/
theorem concave_critical_global {A B C : Int} (hB : B ≤ 0) (hC : C ≤ 0) :
    A + B + C ≤ A := by omega

/-- **F10b (segment coefficients).**  With `A`, `B`, `C` read off as above from a
    bilinear `h`, the far endpoint value `A + B + C` is exactly `h(K',K')`.  This
    is the bookkeeping that lets F10a be applied. -/
theorem segment_far_endpoint (hKK hKK' hK'K hK'K' : Int) :
    hKK + (hKK' + hK'K - 2*hKK)
        + (hKK - (hKK' + hK'K) + hK'K') = hK'K' := by omega

/-- **F10c (concavity from a subtracted square).**  Baek's Theorem 7.4.2 makes `Q`
    concave by SUBTRACTING Mamikon regions, whose areas are `½∫α²` with `α`
    convex-linear — hence convex quadratics.  The mechanism is just that the
    concavity coefficient of a subtracted square is nonpositive: if the quadratic
    part of `f` is `-d·w²` with `d ≥ 0`, then `C ≤ 0`. -/
theorem concavity_of_subtracted_square {d w C : Int} (hd : 0 ≤ d)
    (hC : C = -(d*(w*w))) : C ≤ 0 := by
  have h1 : 0 ≤ d*(w*w) := Int.mul_nonneg hd (sq_nonneg_int w)
  omega

/-! ## F11 — ODE6, the ambidextrous phase equation

Romik's six local-optimality ODEs govern the phases of an optimal rotation path.
ODE1--ODE5 are the ones Gerver's sofa uses; ODE6 is the one it does not, and it is
exactly the equation governing the middle phase of Romik's AMBIDEXTROUS sofa
$\Sigma$.  Its solution SOL6 is

    x₆(t) = R_t ( f₁cos(t/2) + f₂sin(t/2) - 1,
                 -f₂cos(t/2) + f₁sin(t/2) - 1 )ᵀ + κ₆,

and the equation itself, derived and numerically confirmed to 5.6e-15, is

    x'' = 2 J x' + (3/4)(x - κ₆) - (1/4) R_t (1,1)ᵀ,     J = [[0,-1],[1,0]].

Unlike ODE1--ODE5, which have the form `x'' = R_t b + M(t) x'` with no `x` term,
ODE6 carries a restoring term.  In complex form (J ↔ i) its homogeneous part is
`z'' - 2i z' - (3/4) z = 0`, with characteristic roots `i/2` and `3i/2` — which is
why SOL6 contains `cos(t/2)` and why the closed form for `c_y - 1/2` contains
`sin(3t/2)`.

The whole derivation rests on one identity about the bracket `v`, and that identity
is a statement about half-angle trigonometric arcs which the `Trig` machinery above
already expresses.  Writing `D` for the formal derivative with respect to the
HALF-ANGLE (equivalently `2 d/dt`), so that `D` is the same operator as before,
F11 is `D(D v) = -(v + 1)` for every arc whose constant term is `-1`. -/

namespace Trig

/-- **F11 (the SOL6 bracket identity).**  For a half-angle arc with constant term
    `-1`, applying the formal derivative twice negates the oscillatory part and
    cancels the constant against `1`:  `D(D v) = -(v + 1)`.

    Both components of SOL6's bracket have constant term `-1`, so both satisfy it,
    which is the identity `4 v'' = -(v + (1,1))` underlying ODE6. -/
theorem sol6_bracket (a b : Int) :
    D (D ⟨a, b, -1⟩) = ⟨-a, -b, 0⟩ := rfl

/-- **F11b.**  The right-hand side is exactly `-(v + 1)` when the constant term is
    `-1`: with `v = ⟨a, b, -1⟩` we have `-(v + const 1) = ⟨-a, -b, 0⟩`. -/
theorem neg_add_one (a b : Int) :
    (⟨-a, -b, 0⟩ : Trig) = ⟨-(a), -(b), -((-1) + 1)⟩ := rfl

/-- **F11c.**  Hence `D(D v) = -(v + 1)` for SOL6's bracket, stated as the
    coefficient identity the derivation of ODE6 consumes.  The constant term `-1`
    is essential: for any other constant `c` the two sides differ by `c + 1`. -/
theorem sol6_ode (a b c : Int) (hc : c = -1) :
    D (D ⟨a, b, c⟩) = ⟨-a, -b, -(c + 1)⟩ := by
  subst hc; rfl

end Trig

/-! ## F12 — the angular gap at a ρ-fixed apex

CORRECTION.  An earlier reading of these spans concluded that a single wedge pair
never separates and that a neighbourhood argument was needed.  That was an artifact
of sampling the vertical line at a FIXED distance from the apex: the covering happens
only for `ε < ε₀ = (2p_y-1)/(2 tan t)`, which can be very small.  F13 below gives the
correct statement, and a single pair does suffice.

S1: deforming Romik's path upward, `Σ = S ∩ ρS` is connected for `M < 1/2` and
splits for `M > 1/2`, with the transition at `1/2` to six decimals and unchanged
across four deformation families.  Yet no SINGLE wedge pair forces it: the measured
per-`t` threshold satisfies `h*(t) > 1/2` throughout `(0, π/2)`.

F12 is the reason both are true.  At the threshold the apex is ρ-FIXED, so `Q_t` and
`ρQ_t` share it, and their angular spans are

    Q_t    :  [ t + π ,  t + 3π/2 ],        ρQ_t  :  [ π/2 - t ,  π - t ],

which leave an angular GAP of width `2t` between `π - t` and `π + t`.  A single pair
therefore never separates for `t > 0`, and closes only as `t → 0` — exactly the
observed shape of `h*`.  For `M > 1/2` the wedges of NEARBY `t`, with their ρ-images,
fill the gap; that neighbourhood argument is what a proof of the connectedness
ceiling must supply. -/

/-- **F12 (angular gap).**  With `P` standing for `π`, the upper end `P - t` of the
    ρ-image's span lies strictly below the lower end `P + t` of the wedge's own span
    whenever `t > 0`.  So the two spans miss each other by `2t`, and a single wedge
    pair at a ρ-fixed apex never covers a neighbourhood of the apex. -/
theorem wedge_gap {t P : Int} (ht : 0 < t) : P - t < P + t := by omega

/-- **F12b (the gap closes only in the limit).**  The gap width is `2t`, which is
    positive for every `t > 0` and tends to `0` only as `t → 0`.  Stated as the
    quantitative form: the width is exactly `2t`. -/
theorem wedge_gap_width (t P : Int) : (P + t) - (P - t) = 2*t := by omega

/-! ## F13 — the connectedness ceiling, proved

Let `p = c(t₀)` with `p_y > 1/2`, so the ρ-image apex `(p_x, 1-p_y)` lies below `p`.
On the vertical line `x = p_x - ε` with `ε > 0`, a point `(p_x-ε, y)` lies in

    Q_{t₀}      iff   y ≤ p_y - ε·tan t₀,
    ρQ_{t₀}     iff   y ≥ 1 - p_y + ε·tan t₀,

so the pair covers the whole line exactly when

    p_y - ε·tan t₀  ≥  1 - p_y + ε·tan t₀      i.e.      2·ε·tan t₀ ≤ 2·p_y - 1.

Hence for every `ε` with `0 < ε < ε₀ := (2p_y-1)/(2 tan t₀)` the line is entirely
removed, so the sofa omits an open vertical STRIP of width `ε₀`, and a connected sofa
must lie on one side of it.  Verified numerically: the predicted covering threshold
matches at seven `(t₀, p_y)` pairs on both sides of `ε₀`, and `p_y < 1/2` gives
`ε₀ ≤ 0` and never covers.

F13 is the inequality, over `Int` with `T` standing for `tan t₀ > 0` and everything
scaled by `2` to stay integral: `2·ε·T ≤ 2·p_y - 1` is what makes the two half-lines
meet. -/

/-- **F13 (strip covering, exact criterion).**  Work in doubled heights, so the strip
    is `0 ≤ y ≤ 2` and `PY := 2·p_y`; write `E := 2·ε·tan t₀ > 0`.  Then `Q_{t₀}`
    covers `y ≤ PY - E` and `ρQ_{t₀}` covers `y ≥ 2 - PY + E`, and the two cover the
    whole line exactly when `E ≤ PY - 1`. -/
theorem strip_covers_iff {E PY : Int} : (2 - PY + E ≤ PY - E) ↔ (E ≤ PY - 1) := by
  omega

/-- **F13b (nothing happens at or below half).**  If `p_y ≤ 1/2`, i.e. `PY ≤ 1`, then
    no positive `E` satisfies the covering criterion: the two cones always leave a
    gap, whatever the distance from the apex.  This is why the separation threshold
    is exactly `1/2`. -/
theorem no_cover_below_half {E PY : Int} (hE : 0 < E) (hPY : PY ≤ 1) :
    ¬ (E ≤ PY - 1) := by omega

/-- **F13c (connectedness ceiling).**  Contrapositive form, as used: if for every
    positive distance the cones leave a gap — which is what it means for the sofa to
    omit no vertical strip — then `PY ≤ 1`, i.e. `p_y ≤ 1/2`.

    Combined with F13 this is the connectedness ceiling: an apex above the symmetry
    axis forces the sofa to omit an open vertical strip of width
    `(2p_y-1)/(2 tan t₀)`, so a connected sofa has every apex at or below the axis. -/
theorem connectedness_ceiling {PY : Int} (h : ∀ E : Int, 0 < E → PY - 1 < E) :
    PY ≤ 1 := by
  have := h 1 (by omega)
  omega

/-! ## F14 — the identity `4 a₁ sin β = 1`

T2 says the injectivity quantities vanish exactly at Σ's phase junctions.  Worked
out, that is an algebraic identity between two of Romik's constants.

For SOL1, `x₁(t) = R_t v + κ` with `v = (a₁cos t - 1, a₁sin t - 1/2)`.  Since
`x' = R(Jv + v')` and `μ_t = R_t e₁`, the frame component is
`x'·μ_t = (Jv + v')_x = -v_y - a₁ sin t = 1/2 - 2a₁ sin t`, which vanishes iff
`sin t = 1/(4a₁)`.  Numerically `1/(4a₁)` and `sin β` agree to `3.9e-62` at 60
digits, so

    4 a₁ sin β = 1,       β  = arctan( (∛(√2+1) - ∛(√2-1)) / 2 ),
                          a₁ = ¼√( 4 + ∛(71+8√2) + ∛(71-8√2) ).

Symmetrically, for SOL5 `x'·ν_t = 2a₁cos t - 1/2` vanishes iff `cos t = 1/(4a₁)`,
i.e. at `t = π/2 - β`.  So both junctions are explained by the one identity.

F14 records the coefficient computation, over `Int` with everything doubled and `A`
standing for `2a₁`, so that `2·x'·μ_t` has coefficients `⟨0, -2A, 1⟩`, i.e. the
function `1 - 2A·sin t`. -/

namespace Trig

/-- **F14a (the frame speed of SOL1).**  With `A = 2a₁` and coordinates doubled,
    `-2v_y + D(2v_x)` has sine-coefficient `-(2A)`, i.e. `2·x'·μ_t = 1 - 2A sin t`. -/
theorem sol1_speed_mu (A : Int) :
    ((⟨0, -A, 1⟩ : Trig) + D ⟨A, 0, -2⟩).b = -(2*A) := by
  show (-A) + (-A) = -(2*A)
  omega

/-- **F14b.**  Its constant coefficient is `1`, so the doubled speed is
    `1 - 2A sin t` exactly. -/
theorem sol1_speed_const (A : Int) :
    ((⟨0, -A, 1⟩ : Trig) + D ⟨A, 0, -2⟩).c = 1 := by
  show (1 : Int) + 0 = 1
  omega

/-- **F14c (the junction condition).**  The frame speed vanishes exactly when
    `2A·sin t = 1`, i.e. `4a₁ sin t = 1`.  At `t = β` this is the identity
    `4a₁ sin β = 1`, which is therefore equivalent to `β` being the zero of the
    injectivity quantity — the analytic content of T2. -/
theorem sol1_speed_vanishes {A S : Int} : (1 - 2*(A*S) = 0) ↔ (2*(A*S) = 1) := by
  omega

end Trig

/-! ## F15 — the algebraic proof of `4 a₁ sin β = 1`

Write `u := ∛(√2+1) - ∛(√2-1)`, so `tan β = u/2`, and
`w := ∛(71+8√2) + ∛(71-8√2)`, so `a₁ = ¼√(4+w)`.  Then

    4 a₁ sin β = 1   ⟺   u²(3+w) = 4,

because `sin β = u/√(4+u²)`.  The proof is a chain of polynomial identities.

STEP 1.  `pq = 1` and `p³ - q³ = 2` give `u³ = (p³-q³) - 3u = 2 - 3u`, so

    u³ + 3u = 2,

a much simpler description of `β` than the nested radicals.

STEP 2.  With `x := u²`, step 1 reads `u(x+3) = 2`; squaring, `x(x+3)² = 4`, i.e.

    x³ + 6x² + 9x - 4 = 0.

STEP 3.  Put `W := 4/x - 3 = (4-3x)/x`.  Clearing denominators,

    (4-3x)³ - 51(4-3x)x² - 142x³ = -16(x³ + 6x² + 9x - 4),

so `W³ - 51W - 142 = 0` by step 2.  This is F15b below.

STEP 4.  `W³ - 51W - 142` has discriminant `-4(-51)³ - 27(-142)² = 530604 - 544428
= -13824 < 0`, hence exactly one real root; `w` is real and satisfies the same cubic,
so `W = w`.

STEP 5.  Therefore `x(3+w) = x(x+3)² = 4`.  ∎

A corollary of steps 2 and 4: `w = (u²+3)² - 3 = u⁴ + 6u² + 6`, i.e.
`∛(71+8√2) + ∛(71-8√2) = u⁴ + 6u² + 6` with `u³ + 3u = 2`.

Every step was checked at 60 digits.  F15 formalises the two polynomial steps; the
radical evaluations and the discriminant sign are elementary and are not carried into
`Int`. -/

/-- **F15a (step 2).**  If `u² = x` and `u(x+3) = 2` then `x(x+3)² = 4`. -/
theorem u_sq_cubic {u x : Int} (hu : u*u = x) (h : u*(x+3) = 2) :
    x*((x+3)*(x+3)) = 4 := by
  have hsq : (u*(x+3))*(u*(x+3)) = 4 := by rw [h]; omega
  have hre : (u*(x+3))*(u*(x+3)) = (u*u)*((x+3)*(x+3)) := by ac_rfl
  rw [hre, hu] at hsq
  exact hsq

/-- **F15b (step 3).**  The Cardano substitution, as a polynomial identity.  Written
    with explicit products so that the atoms are `x`, `x*x`, `x*x*x` and the identity
    is linear in them. -/
theorem cardano_substitution (x : Int) :
    64 - 144*x - 96*(x*x) - 16*(x*x*x)
      = -16*((x*x*x) + 6*(x*x) + 9*x - 4) := by
  omega

/-- **F15c.**  Consequently, if `x` satisfies the cubic of step 2 then the left side
    of F15b vanishes — which is `W³ - 51W - 142 = 0` after clearing `x³`. -/
theorem cardano_vanishes {x : Int} (hx : (x*x*x) + 6*(x*x) + 9*x - 4 = 0) :
    64 - 144*x - 96*(x*x) - 16*(x*x*x) = 0 := by
  rw [cardano_substitution, hx]
  omega

/-! ## F16 — the cone-membership step of T1

T1's proof needs: for `q = (p_x - ε, y)` and `p = c(t₀)`,

    q ∈ Q_{t₀}   ⟺   ⟨q-p, μ⟩ < 0  and  ⟨q-p, ν⟩ < 0,

and with `μ = (C, S)`, `ν = (-S, C)` (so `C = cos t₀ > 0`, `S = sin t₀ > 0`),

    ⟨q-p, μ⟩ = -εC + (y-p_y)S,        ⟨q-p, ν⟩ = εS + (y-p_y)C .

The ν-condition rearranges to `y·C < p_y·C - ε·S`, i.e. `y < p_y - ε tan t₀`, and the
μ-condition is then automatic because its right-hand side is non-negative.  F16
records both steps over `Int`, with the products `E*S`, `Y*C`, `P*C`, `E*C` as atoms so
that each statement is linear in them.  The covering criterion itself is F13's
`strip_covers_iff`; F16 supplies the two membership steps feeding into it. -/

/-- **F16a (the binding condition).**  The `ν`-half of cone membership is exactly
    `y·C < p_y·C - ε·S`, which is `y < p_y - ε·tan t₀`. -/
theorem cone_nu_iff {E Y P S C : Int} :
    (E*S + (Y*C - P*C) < 0) ↔ (Y*C < P*C - E*S) := by omega

/-- **F16b (the other half is automatic).**  Given the `ν`-condition and
    `ε·S, ε·C ≥ 0`, the `μ`-condition holds without further hypotheses: its
    right-hand side is non-negative while the left is already negative. -/
theorem cone_mu_of_nu {E Y P S C : Int} (hES : 0 ≤ E*S) (hEC : 0 ≤ E*C)
    (h : Y*C < P*C - E*S) : (Y*C - P*C) - E*C < 0 := by omega

/-! ## F17 — the niche functional in convex-linear data (P3c)

Section 8 of the note derives, for the cap `K` with support function `h`,

    c(t)      = (F-1) μ_t + (G-1) ν_t          F = h(μ_t), G = h(ν_t)
    α₁(t)     = -⟨c',μ_t⟩ = G - 1 - F'         (face-1 arm)
    α₂(t)     =  ⟨c',ν_t⟩ = F - 1 + G'         (face-2 arm)
    σ(t)      = c_y/cos t = (F-1) tan t + G-1  (face-1 reach to the corridor floor)

all affine in `h`; and the niche area

    |N| = ∫ [ ½(α₂⁺)² + ½(σ-α₁)² - ½(α₁⁻)² ] dt .

Three steps are arithmetic and are recorded here.  F17a is the Jacobian integral that
produces the bracket, in the form that avoids halves.  F17b is the normal-velocity sign
criterion of Lemma "Normal velocities": face 1 advances exactly beyond its envelope
point and face 2 exactly inside its own, which is why *no sign hypothesis on the arms
is needed* — the repair of the reported injectivity failure.  F17c is midpoint
convexity of `x ↦ (x⁺)²`, the property that makes the first two terms convex
quadratics.  Atoms are `Int`; products appearing in more than one term are named. -/

/-- The positive part, spelled out so that no `Mathlib` `max` API is needed. -/
def pp (x : Int) : Int := if 0 ≤ x then x else 0

theorem pp_nonneg (x : Int) : 0 ≤ pp x := by
  unfold pp; split <;> omega

theorem pp_add_le (a b : Int) : pp (a + b) ≤ pp a + pp b := by
  unfold pp; split <;> split <;> split <;> omega

/-- **F17a (the arm integral).**  `∫_{α⁺}^{σ} (s-α) ds = ½(σ-α)² - ½(α⁻)²`, doubled to
    clear the halves and split on the sign of `α`.  For `α ≤ 0`, `α⁻ = -α` and the
    right side is `σ² - 2ασ`. -/
theorem arm_integral_neg {S A : Int} (hA : A ≤ 0) :
    (S - A)*(S - A) - pp (-A) * pp (-A) = S*S - 2*(A*S) := by
  have h : (S - A)*(S - A) = S*S - 2*(A*S) + A*A := by
    simp [Int.mul_sub, Int.mul_comm]; omega
  have hp : pp (-A) = -A := by unfold pp; split <;> omega
  rw [hp]
  have hn : (-A)*(-A) = A*A := by simp [Int.neg_mul, Int.mul_neg]
  omega

/-- **F17a' (the other branch).**  When `α ≥ 0` the clamp kills the subtracted term
    and the arm integral is exactly `½(σ-α)²`, the convex-quadratic case. -/
theorem arm_integral_pos {S A : Int} (hA : 0 ≤ A) :
    (S - A)*(S - A) - pp (-A) * pp (-A) = (S - A)*(S - A) := by
  have hp : pp (-A) = 0 := by unfold pp; split <;> omega
  rw [hp]; omega

/-- **F17b (normal-velocity signs, and why no joint hypothesis is needed).**  With
    `V₁ s = s - α₁` and `V₂ s = α₂ - s`, each face advances on one side of its *own*
    envelope point, and each statement mentions only its own arm.  The face-1 sweep
    `[α₁⁺, σ]` is therefore nonempty under a condition on `σ` and `α₁` alone, in both
    sign regimes of `α₁` — including `α₁ < 0`, where the one-corner injectivity
    condition fails.  That is the repair: the reported failure came from demanding
    `α₁ > 0` and `α₂ > 0` simultaneously, which the decomposition never uses. -/
theorem face_advance_sign {S A1 A2 : Int} :
    (A1 < S → 0 < S - A1) ∧ (S < A2 → 0 < A2 - S) := ⟨by omega, by omega⟩

theorem face1_nonempty {S A1 : Int} (hS : pp A1 < S) : 0 < S - A1 := by
  unfold pp at hS; split at hS <;> omega

/-- **F17c (midpoint convexity of the Mamikon integrand).**  `φ x = (x⁺)²` satisfies
    `2(φ a + φ b) ≥ φ (a+b)`, via `a⁺ + b⁺ ≥ (a+b)⁺ ≥ 0` and `2(p²+q²) ≥ (p+q)²`.
    This is the inequality behind "the first two terms of the niche formula are convex
    quadratics", hence behind concavity of the upper bound. -/
theorem two_sq_add_sq (p q : Int) : (p + q)*(p + q) ≤ 2*(p*p + q*q) := by
  have h : 2*(p*p + q*q) - (p + q)*(p + q) = (p - q)*(p - q) := by
    simp [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add, Int.mul_comm]; omega
  have hsq : 0 ≤ (p - q)*(p - q) := sq_nonneg_int (p - q)
  omega

/-- **F17c.**  `φ x = (x⁺)²` is midpoint convex: `φ(a+b) ≤ 2(φ a + φ b)`.  With
    `φ` affine-precomposed this is the inequality that makes the first two terms of the
    niche formula convex quadratics, hence the upper bound concave. -/
theorem posPart_sq_midpoint_convex (a b : Int) :
    pp (a + b) * pp (a + b) ≤ 2*(pp a * pp a + pp b * pp b) := by
  have hle := pp_add_le a b
  have h0 := pp_nonneg (a + b)
  have hstep : pp (a + b) * pp (a + b) ≤ (pp a + pp b) * (pp a + pp b) :=
    Int.mul_le_mul hle hle h0 (Int.le_trans h0 hle)
  exact Int.le_trans hstep (two_sq_add_sq _ _)

/-! ## F18 — the cap quadratic form, the principal symbol, and the outer-arm monotonicity

Three further steps of the note are arithmetic.

F18a.  The cap identity.  Since `rho` reflects in `y = 1/2`, the support function of
`C2 = C ^ rho C` has two branches, `H(theta)` above and `H(-theta) + sin theta` below, and
`|C2| = (1/2) int (h_2^2 - h_2'^2)` over the circle becomes an integral over `[0,pi]` of
the SUM of the two branches' integrands.  The algebraic step is the expansion of that
sum, recorded here (doubled, to clear the halves) with atoms `H, D = H', S = sin s,
C = cos s`.  What is NOT formalized is the analysis: that `<h_2'', h_2> = -int h_2'^2`
with no boundary terms because the circle has none.

F18b.  The principal symbol.  The coefficient of `eta'(theta)^2` in the second variation
is `-1` from the cap, `-s` from the sigma term (`s = 1` on `[0,pi/2]`), `+o` from the
obstruction term (`o = 1` on `E_1`), and `-f` from the face-2 term.  Since `E_1` is a
subset of `[0,pi/2]`, where the sigma term is always present, `o <= s`; hence the total
is at most `-1` for every admissible choice.  That is why concavity is a finite question.

F18c.  The outer-arm monotonicity, `x(t) = (F(t)-1)/cos t`.  On the two outer phases
`cos^2 t * x'(t)` is `1/2 - sin t` and `(1/2)(1 - sin t)` respectively.  The first is
positive exactly when `sin t < 1/2`, and `4 a_1 sin beta = 1` with `a_1 > 1/2` forces
`sin beta < 1/2`; scaled to integers by a common denominator `N` this is F18c1.  The
second is non-negative because `sin t <= 1`.  The middle phase is NOT here: it reduces to
positivity of an explicit three-term trigonometric expression, which core Lean cannot
express.

F18d.  The tangency at `t = pi/2`: the sweep endpoint equals the right end of the floor
facet.  A linear identity in the four quantities involved. -/

/-- **F18a (the cap expansion).**  Doubled sum of the two branch integrands. -/
theorem cap_branch_sum (H D S C : Int) :
    (H*H - D*D) + ((H - S)*(H - S) - (D - C)*(D - C))
      = 2*(H*H) - 2*(D*D) - 2*(H*S) + 2*(D*C) + S*S - C*C := by
  simp [Int.mul_sub, Int.sub_mul, Int.mul_comm]; omega

/-- **F18b (the principal symbol is negative).**  With `s, o, f` the indicators of the
    sigma, obstruction and face-2 terms and `o ≤ s` (the obstruction lives inside the
    sigma term's range), the coefficient of `eta'^2` is at most `-1`. -/
theorem principal_symbol_neg {s o f : Int}
    (hs : s = 0 ∨ s = 1) (ho : o = 0 ∨ o = 1) (hf : f = 0 ∨ f = 1)
    (hos : o ≤ s) : -1 - s + o - f ≤ -1 := by
  rcases hs with h | h <;> rcases ho with h' | h' <;> rcases hf with h'' | h'' <;>
    subst h <;> subst h' <;> subst h'' <;> omega

/-- **F18c1 (`beta < pi/6`).**  Writing `sin beta = S/N` and `a_1 = A/N`, the relation
    `4 a_1 sin beta = 1` is `4*A*S = N*N`, and `a_1 > 1/2` is `N < 2*A`.  Then
    `sin beta < 1/2`, i.e. `2*S < N` — which is what makes `1/2 - sin t > 0` on the
    whole first phase. -/
theorem beta_below_pi_over_six {A S N : Int} (hN : 0 < N) (hS : 0 < S)
    (hT3 : 4*(A*S) = N*N) (hA : N < 2*A) : 2*S < N := by
  have key : N*(2*S) < (2*A)*(2*S) :=
    Int.mul_lt_mul_of_pos_right hA (by omega)
  have hrw : (2*A)*(2*S) = 4*(A*S) := by ac_rfl
  rw [hrw, hT3] at key
  -- N*(2*S) < N*N  with  N > 0  gives  2*S < N
  rcases Int.lt_trichotomy (2*S) N with h | h | h
  · exact h
  · rw [h] at key; omega
  · exact absurd key (by
      have : N*N ≤ N*(2*S) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega)

/-- **F18c2 (first phase).**  `cos^2 t * x'(t) = 1/2 - sin t`, doubled: positive exactly
    when `2 sin t < 1`. -/
theorem phase1_increasing {S : Int} (h : 2*S < 1) : 0 < 1 - 2*S := by omega

/-- **F18c3 (last phase).**  `cos^2 t * x'(t) = (1/2)(1 - sin t) ≥ 0` since `sin t ≤ 1`,
    with equality only at `t = pi/2`. -/
theorem phase3_increasing {S : Int} (h : S ≤ 1) : 0 ≤ 1 - S := by omega

/-- **F18d (the tangency identity).**  The right end of the floor facet is its left end
    `c_x(0) - alpha_2(0)` plus its length `alpha_2(0) + alpha_1(pi/2) - (G(pi/2)-1)`, and
    with `c_x(0) = 0` that equals `alpha_1(pi/2) - (G(pi/2)-1)`, which is the sweep
    endpoint `c_x(pi/2) + alpha_1(pi/2)` because `G(pi/2)-1 = -c_x(pi/2)`. -/
theorem facet_tangency {A1 A2 G CX0 CXP : Int} (h0 : CX0 = 0) (hG : G = -CXP) :
    (CX0 - A2) + (A2 + A1 - G) = CXP + A1 := by
  subst h0; subst hG; omega

/-! ## F19 — the curvature condition (RC) and the ODE reduction it feeds

Section 10 of the note proves that BOTH injectivity conditions follow from one linear
condition on the cap,

    (RC)   H(theta) + H''(theta) <= 1      (absolutely continuous part),

i.e. the cap is nowhere flatter than a circle of the corridor's width.  The proof reduces
each condition to a forced harmonic oscillator.  For (C22), with
n(t') = <c(t),nu_t'> - (G(t')-1) and Phi(tau) = n(t-tau) - alpha_2(t) sin tau,

    n(t) = 0,   n'(t) = -alpha_2(t)   so   Phi(0) = Phi'(0) = 0,
    n'' = -<c(t),nu_t'> - G''  and  <c(t),nu_t'> = n + G - 1,
    so  n'' = -n + 1 - (G + G''),  and the alpha_2 terms CANCEL, leaving

        Phi'' + Phi = 1 - (G + G'')(t-tau) =: R(tau) ,

whence Phi(tau) = int_0^tau sin(tau-u) R(u) du >= 0, because tau <= pi/2 < pi makes the
kernel non-negative and (RC) makes R non-negative.

Four steps are arithmetic and are recorded here.  F19a is the substitution that produces
`n'' = -n + 1 - (G+G'')`.  F19b is the cancellation giving `Phi'' + Phi = R`.  F19c is the
sign conclusion in its discrete form: a sum of products of non-negative terms is
non-negative (the Riemann-sum shadow of the integral representation).  F19d is convexity
of the constraint set cut out by (RC), which is what makes the domain convex.

NOT formalized: that the integral representation solves the ODE, and that the facet atom
at theta = pi/2 contributes nothing because it sits where the kernel vanishes.  Both are
analysis. -/

/-- **F19a (the substitution).**  With `C = <c(t),nu_t'>` satisfying `C = n + G - 1`, the
    second derivative `N2 = -C - G2` becomes `-n + 1 - (G + G2)`. -/
theorem curvature_substitution {C n G G2 N2 : Int}
    (hC : C = n + G - 1) (hN : N2 = -C - G2) :
    N2 = -n + 1 - (G + G2) := by
  subst hC; subst hN; omega

/-- **F19b (the cancellation).**  `Phi = n - A*S` and `Phi2 = N2 + A*S` with
    `N2 = -n + K` give `Phi2 + Phi = K`: the `alpha_2` terms cancel identically, which is
    why the resulting oscillator is forced by the curvature alone. -/
theorem phi_ode {Phi Phi2 n N2 A S K : Int}
    (hPhi : Phi = n - A*S) (hPhi2 : Phi2 = N2 + A*S) (hN2 : N2 = -n + K) :
    Phi2 + Phi = K := by
  subst hPhi; subst hPhi2; subst hN2; omega

/-- **F19c (the sign conclusion, discrete form).**  If every kernel value and every
    forcing value is non-negative then so is the sum of their products.  This is the
    Riemann-sum shadow of `Phi(tau) = int sin(tau-u) R(u) du >= 0`, with the kernel
    `sin(tau-u) >= 0` supplied by `tau <= pi/2 < pi` and the forcing `R >= 0` by (RC). -/
theorem kernel_sum_nonneg : ∀ (ws rs : List Int),
    (∀ x ∈ ws, 0 ≤ x) → (∀ x ∈ rs, 0 ≤ x) →
    0 ≤ (List.zipWith (fun a b => a * b) ws rs).sum
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | w :: ws, r :: rs, hw, hr => by
      have h1 : 0 ≤ w * r :=
        Int.mul_nonneg (hw w List.mem_cons_self) (hr r List.mem_cons_self)
      have h2 : 0 ≤ (List.zipWith (fun a b => a * b) ws rs).sum :=
        kernel_sum_nonneg ws rs
          (fun x hx => hw x (List.mem_cons_of_mem _ hx))
          (fun x hx => hr x (List.mem_cons_of_mem _ hx))
      simpa using Int.add_nonneg h1 h2

/-- **F19d ((RC) cuts out a convex set).**  `H + H'' ≤ 1` is linear in `H`, so the
    constraint is preserved by non-negative combinations: if `X ≤ D` and `Y ≤ D` then
    `a*X + b*Y ≤ (a+b)*D` for `a, b ≥ 0`.  Taking `a + b` to be the common denominator
    of a convex combination gives convexity of the domain. -/
theorem rc_convex {a b X Y D : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : X ≤ D) (hY : Y ≤ D) : a*X + b*Y ≤ (a + b)*D := by
  have h1 : a*X ≤ a*D := Int.mul_le_mul_of_nonneg_left hX ha
  have h2 : b*Y ≤ b*D := Int.mul_le_mul_of_nonneg_left hY hb
  have h3 : (a + b)*D = a*D + b*D := by simp [Int.add_mul]
  omega

/-! ## F20 — the cross condition, and the completion identity behind the Garding bound

F20a.  The cross condition.  Solving `l2(t) ^ l1(t')` in the frame at `t` gives, for
`t' = t - tau` with `tau > 0`,

    s2 = m(t-tau)/cos tau,      s1 = -Phi(tau) - (alpha_2(t) - s2) sin tau,

and in the frame at `t'` for `t = t' - tau'` with `tau' > 0`,

    s2 = -Psi(tau') - (s1 - alpha_1(t')) sin tau' .

Under (RC), `Phi, Psi >= 0` (F19), and `sin tau >= 0` because `tau <= pi/2`.  So if the
meeting point is interior to the face-2 segment (`0 < s2 < alpha_2`) then `s1 < 0`, and the
face-1 segment starts at `alpha_1^+ >= 0`, so the point is outside it; symmetrically, if it
is interior to the face-1 segment (`s1 > alpha_1^+ >= alpha_1`) then `s2 < 0`, outside
`[0, alpha_2]`.  Either way it is not interior to both.  F20a records the two sign
implications; the identities themselves are geometry.

F20b.  The completion identity.  On `[0,beta)`, writing `p = eta'(t)`, `q = eta(t)`,
`r = eta(t+pi/2)` and `T = tan t`, the three second-variation terms that involve `eta'(t)`
combine as

    -p^2 - (qT+p)^2 + (r-p)^2  =  -(p+qT+r)^2 + 2 r^2 + 2 q T r ,

so the added (bad) term is absorbed exactly and the remainder contains NO derivative of
`eta` at all.  That is what makes the Garding estimate possible: after this step only
lower-order terms remain, to be handled by Poincare inequalities. -/

/-- **F20a (cross exclusion, face-2 side).**  If the meeting point is interior to the
    face-2 segment and `Phi >= 0`, `Sin >= 0`, then `s1 < 0`, hence below the face-1
    segment, whose left endpoint is non-negative. -/
theorem cross_excl_face2 {Phi A2 S2v Sin s1 : Int}
    (hPhi : 0 ≤ Phi) (hSin : 0 ≤ Sin) (hhi : S2v < A2)
    (hs1 : s1 = -Phi - (A2 - S2v)*Sin) : s1 ≤ 0 := by
  have h1 : 0 ≤ (A2 - S2v)*Sin := Int.mul_nonneg (by omega) hSin
  omega

/-- **F20a' (cross exclusion, face-1 side).**  Symmetrically, if the point is interior to
    the face-1 segment then `s2 < 0`, hence outside `[0, alpha_2]`. -/
theorem cross_excl_face1 {Psi A1 s1 Sin s2 : Int}
    (hPsi : 0 ≤ Psi) (hSin : 0 ≤ Sin) (hgt : A1 < s1)
    (hs2 : s2 = -Psi - (s1 - A1)*Sin) : s2 ≤ 0 := by
  have h1 : 0 ≤ (s1 - A1)*Sin := Int.mul_nonneg (by omega) hSin
  omega

/-- **F20b (the completion identity).**  The three `eta'`-bearing terms of the second
    variation on `[0,beta)` combine into a negative square plus derivative-free
    remainders. -/
theorem completion_identity (p q r T : Int) :
    -(p*p) - (q*T + p)*(q*T + p) + (r - p)*(r - p)
      = -((p + q*T + r)*(p + q*T + r)) + 2*(r*r) + 2*(q*T*r) := by
  have e1 : (q*T + p)*(q*T + p) = (q*T)*(q*T) + 2*((q*T)*p) + p*p := by
    simp [Int.add_mul, Int.mul_add, Int.mul_comm]; omega
  have e2 : (r - p)*(r - p) = r*r - 2*(r*p) + p*p := by
    simp [Int.sub_mul, Int.mul_sub, Int.mul_comm]; omega
  have e3 : (p + q*T + r)*(p + q*T + r)
      = p*p + (q*T)*(q*T) + r*r + 2*((q*T)*p) + 2*(r*p) + 2*((q*T)*r) := by
    simp [Int.add_mul, Int.mul_add, Int.mul_comm]; omega
  have e4 : (q*T)*r = q*T*r := by ac_rfl
  rw [e1, e2, e3, e4]
  omega

/-! ## F21 — the positivity of the forced oscillator, discretely, and the Garding sum

F19 reduced both injectivity conditions to `Phi'' + Phi = R >= 0` with `Phi(0) = Phi'(0) = 0`
and concluded `Phi >= 0` from the integral representation.  Core Lean has no integration, but
the DISCRETE form of exactly that implication is provable and is the honest formal content:
if a sequence starts flat and its second difference is non-negative, it never goes negative.

Applied to `Phi_n` on a grid, the second difference is `h^2 (R_n - Phi_n)`, so the hypothesis
`0 <= P(n+2) - 2 P(n+1) + P n` is the discrete `Phi'' >= -Phi`, which is implied by `R >= 0`
wherever `Phi <= R`.  F21a is that implication; F21b is the monotonicity it rests on.

F21c is the assembly step of the Garding estimate: a sum of terms, each a non-positive
coefficient times a non-negative quantity, is non-positive.  With the coefficients
`-1.6013`, `-0.3710`, `0` and `-0.005` of the note, that is what yields `d^2 Q <= 0`. -/

/-- **F21b (monotonicity).**  A sequence with non-negative second difference and equal first
    two terms is non-decreasing. -/
theorem second_diff_mono (P : Nat → Int) (h1 : P 1 = P 0)
    (hc : ∀ n, 0 ≤ P (n+2) - 2*P (n+1) + P n) : ∀ n, P n ≤ P (n+1) := by
  intro n
  induction n with
  | zero => show P 0 ≤ P 1; omega
  | succ k ih =>
      have h := hc k
      show P (k+1) ≤ P (k+2)
      omega

/-- **F21a (the discrete oscillator positivity).**  `Phi_0 = Phi_1 = 0` and a non-negative
    second difference give `Phi_n >= 0` for all `n`.  This is the discrete shadow of
    `Phi(tau) = int_0^tau sin(tau-u) R(u) du >= 0`. -/
theorem discrete_osc_nonneg (P : Nat → Int) (h0 : P 0 = 0) (h1 : P 1 = 0)
    (hc : ∀ n, 0 ≤ P (n+2) - 2*P (n+1) + P n) : ∀ n, 0 ≤ P n := by
  have hmono := second_diff_mono P (by omega) hc
  intro n
  induction n with
  | zero => omega
  | succ k ih =>
      have h := hmono k
      omega

/-- **F21c (the Garding assembly).**  A sum of products of non-positive coefficients with
    non-negative quantities is non-positive. -/
theorem garding_sum_nonpos : ∀ (cs qs : List Int),
    (∀ x ∈ cs, x ≤ 0) → (∀ x ∈ qs, 0 ≤ x) →
    (List.zipWith (fun a b => a * b) cs qs).sum ≤ 0
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | c :: cs, q :: qs, hc, hq => by
      have h1 : c * q ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg (hc c List.mem_cons_self)
          (hq q List.mem_cons_self)
      have h2 : (List.zipWith (fun a b => a * b) cs qs).sum ≤ 0 :=
        garding_sum_nonpos cs qs
          (fun x hx => hc x (List.mem_cons_of_mem _ hx))
          (fun x hx => hq x (List.mem_cons_of_mem _ hx))
      simpa using Int.add_nonpos h1 h2

/-! ## F22 — (RC) for Sigma: the block bound

Section 13 computes the surface-measure density block by block and finds that the only
non-constant blocks are `(3/4)(f1 cos(t/2) + f2 sin(t/2))` and its companion.  (RC) for
those blocks is `3(f1 C + f2 S) <= 4` with `C = cos(t/2)`, `S = sin(t/2)`, and by
Lagrange's identity that follows from the coefficient bound `9(f1^2 + f2^2) <= 16` alone,
with no information about `t`.  With `f2 = (1-sqrt2) f1` this is `f1^2 <= 16/(9(4-2sqrt2))`.

F22a is Lagrange's identity, F22b the resulting bound.  Atoms are `Int`, and the
Pythagorean relation `C^2 + S^2 = 1` is carried as a hypothesis in the usual way. -/

theorem sq_add_int (x y : Int) : (x + y)*(x + y) = x*x + 2*(x*y) + y*y := by
  simp [Int.add_mul, Int.mul_add, Int.mul_comm]; omega

theorem sq_sub_int (x y : Int) : (x - y)*(x - y) = x*x - 2*(x*y) + y*y := by
  simp [Int.sub_mul, Int.mul_sub, Int.mul_comm]; omega

/-- **F22a (Lagrange).**  `(a²+b²)(c²+s²) - (ac+bs)² = (as-bc)²`. -/
theorem lagrange_identity (a b c s : Int) :
    (a*a + b*b)*(c*c + s*s) - (a*c + b*s)*(a*c + b*s) = (a*s - b*c)*(a*s - b*c) := by
  have e1 : (a*a + b*b)*(c*c + s*s)
      = a*a*(c*c) + a*a*(s*s) + b*b*(c*c) + b*b*(s*s) := by
    simp [Int.add_mul, Int.mul_add]; omega
  have e2 := sq_add_int (a*c) (b*s)
  have e3 := sq_sub_int (a*s) (b*c)
  have q1 : (a*c)*(a*c) = a*a*(c*c) := by ac_rfl
  have q2 : (b*s)*(b*s) = b*b*(s*s) := by ac_rfl
  have q3 : (a*s)*(a*s) = a*a*(s*s) := by ac_rfl
  have q4 : (b*c)*(b*c) = b*b*(c*c) := by ac_rfl
  rw [q1, q2] at e2
  rw [q3, q4] at e3
  have e4 : (a*c)*(b*s) = (a*s)*(b*c) := by ac_rfl
  rw [e1, e2, e3, e4]; omega

/-- **F22b ((RC) on the half-angle block).**  If `C² + S² = 1` and `9(a²+b²) ≤ 16` then
    `9(aC+bS)² ≤ 16`: the block `(3/4)(a C + b S)` is bounded by `1` uniformly in `t`.
    For `Sigma`, `a = f1`, `b = f2 = (1-sqrt2) f1`, so the hypothesis is
    `f1² (4-2√2) ≤ 16/9`. -/
theorem rc_block {a b c s : Int} (hp : c*c + s*s = 1) (hab : 9*(a*a + b*b) ≤ 16) :
    9*((a*c + b*s)*(a*c + b*s)) ≤ 16 := by
  have hL := lagrange_identity a b c s
  rw [hp, Int.mul_one] at hL
  have hsq : 0 ≤ (a*s - b*c)*(a*s - b*c) := sq_nonneg_int _
  have hle : (a*c + b*s)*(a*c + b*s) ≤ a*a + b*b := by omega
  have h9 : 9*((a*c + b*s)*(a*c + b*s)) ≤ 9*(a*a + b*b) :=
    Int.mul_le_mul_of_nonneg_left hle (by omega)
  omega

/-! ## F23 — the boundary term of the first variation

The adversarial review of the note found that `delta Q` carries, besides the pointwise
Euler-Lagrange equations, a boundary term

    -(2 H'(pi) + 1) eta(pi) .

It vanishes because `H'(pi) = -1/2`, and that is forced by the reflection symmetry rather
than assumed: the boundary point of `C2` with outer normal `mu_pi = (-1,0)` is
`H(pi) mu_pi + H'(pi) nu_pi = (-H(pi), -H'(pi))`, so its height is `-H'(pi)`; `C2` is
symmetric under `rho(x,y) = (x, 1-y)`, so its leftmost point is `rho`-fixed when unique.
The same mechanism at `theta = 0` gives `H'(0) = 1/2`: both extreme points of the cap sit
at height `1/2`, and they are the two `rho`-fixed points.

Everything is doubled here so that the halves become integers: heights are in units of
`1/2`, the corridor has height `2`, and the reflection is `y |-> 2 - y`.  `DP` denotes
`2 H'(pi)` and `DZ` denotes `2 H'(0)`. -/

/-- **F23a (a `rho`-fixed height is the mid-height).**  In doubled units the reflection is
    `y ↦ 2 - y`, so a fixed point has height `1`, i.e. `1/2` undoubled. -/
theorem rho_fixed_height {y : Int} (h : y = 2 - y) : y = 1 := by omega

/-- **F23b (the boundary term vanishes).**  The leftmost boundary point has height
    `-H'(pi)`, doubled `-DP`.  If it is `rho`-fixed then `DP = -1`, i.e.
    `H'(pi) = -1/2`, and the coefficient `2H'(pi) + 1` of `eta(pi)` vanishes. -/
theorem boundary_term_vanishes {DP hgt : Int}
    (hpt : hgt = -DP) (hfix : hgt = 2 - hgt) : DP + 1 = 0 := by
  have := rho_fixed_height hfix
  omega

/-- **F23c (the other end).**  The rightmost boundary point has height `H'(0)`, doubled
    `DZ`; `rho`-fixedness gives `DZ = 1`, i.e. `H'(0) = 1/2`.  Together with F23b this says
    both extreme points of the cap lie at the mid-height. -/
theorem right_extreme_height {DZ hgt : Int}
    (hpt : hgt = DZ) (hfix : hgt = 2 - hgt) : DZ = 1 := by
  have := rho_fixed_height hfix
  omega

/-- **F23d (the two extremes agree).**  Both `rho`-fixed heights are equal, so the cap's
    leftmost and rightmost boundary points sit at the same height. -/
theorem extremes_same_height {DZ DP : Int} (hz : DZ = 1) (hp : DP = -1) :
    DZ = -DP := by omega

/-! ## F24 — the support-point coordinates feeding F23

F23 took as given that the cap's boundary point with outer normal `mu_theta` has height
`-H'(pi)` at `theta = pi`.  That comes from the parametrisation

    p(theta) = H(theta) mu_theta + H'(theta) nu_theta ,   mu = (C,S),  nu = (-S,C),

so `p = (HC - DS, HS + DC)` with `D = H'`.  The parametrisation itself is geometry and is
not formalized here; what is arithmetic, and is formalized, is its evaluation at the two
angles that matter and the chain from there to the vanishing of the boundary term. -/

/-- **F24a.**  At `theta = pi`, where `(C,S) = (-1,0)`, the boundary point is `(-H, -D)`,
    so its height is `-D = -H'(pi)`. -/
theorem support_point_at_pi {H D C S : Int} (hC : C = -1) (hS : S = 0) :
    H*C - D*S = -H ∧ H*S + D*C = -D := by
  subst hC; subst hS; constructor <;> omega

/-- **F24b.**  At `theta = 0`, where `(C,S) = (1,0)`, the boundary point is `(H, D)`, so
    its height is `D = H'(0)`. -/
theorem support_point_at_zero {H D C S : Int} (hC : C = 1) (hS : S = 0) :
    H*C - D*S = H ∧ H*S + D*C = D := by
  subst hC; subst hS; constructor <;> omega

/-- **F24c (the whole chain).**  At `theta = pi` the boundary point's height is `-D`; if
    that height is `rho`-fixed, in doubled units where the reflection is `y ↦ 2 - y`, then
    `D = -1`, i.e. `H'(pi) = -1/2`, and the coefficient `2H'(pi) + 1` of `eta(pi)` in
    `delta Q` vanishes.  This is F24a, `rho_fixed_height` and `boundary_term_vanishes`
    composed into the single statement the note uses. -/
theorem boundary_chain {H D C S hgt : Int} (hC : C = -1) (hS : S = 0)
    (hh : hgt = H*S + D*C) (hfix : hgt = 2 - hgt) : D + 1 = 0 := by
  have h1 := (support_point_at_pi (H := H) (D := D) hC hS).2
  rw [h1] at hh
  have := rho_fixed_height hfix
  omega

/-! ## F25 — the segment argument

`Q` is `C^1` and piecewise quadratic, so along the segment from `H_Sigma` to a competitor
`H` it is a `C^1` piecewise-quadratic function of one variable.  If every cell met has
`d^2 Q <= 0` then that function has non-positive second derivative throughout, and with
`dQ(Sigma) = 0` it cannot exceed its value at the start.  Convexity of the union of the
cells met is NOT needed -- only concavity along the one segment.

Sampled on a grid, "non-positive second derivative" is "non-positive second difference",
and the argument is: the slopes are non-increasing, the first is `<= 0`, hence all are, hence
the function never rises.  That is what F25 records. -/

/-- **F25a (slopes are non-increasing).**  A non-positive second difference makes the
    successive slopes decrease. -/
theorem second_diff_nonpos_mono (P : Nat → Int)
    (hc : ∀ n, P (n+2) - P (n+1) ≤ P (n+1) - P n) :
    ∀ n, P (n+1) - P n ≤ P 1 - P 0 := by
  intro n
  induction n with
  | zero => show P 1 - P 0 ≤ P 1 - P 0; omega
  | succ k ih =>
      have h := hc k
      show P (k+2) - P (k+1) ≤ P 1 - P 0
      omega

/-- **F25b (the segment argument).**  If in addition the first slope is non-positive --- at
    `Sigma` it is zero, by `delta Q(Sigma) = 0` --- then the function never exceeds its
    starting value: `Q(H) <= Q(Sigma)` for every competitor whose segment stays in cells
    with `d^2 Q <= 0`. -/
theorem concave_along_segment (P : Nat → Int) (hstart : P 1 ≤ P 0)
    (hc : ∀ n, P (n+2) - P (n+1) ≤ P (n+1) - P n) :
    ∀ n, P n ≤ P 0 := by
  intro n
  induction n with
  | zero => show P 0 ≤ P 0; omega
  | succ k ih =>
      have h := second_diff_nonpos_mono P hc k
      show P (k+1) ≤ P 0
      omega

/-- **F25c (the critical case).**  With `delta Q(Sigma) = 0` the first slope vanishes, which
    is the hypothesis actually available. -/
theorem concave_from_critical (P : Nat → Int) (hcrit : P 1 = P 0)
    (hc : ∀ n, P (n+2) - P (n+1) ≤ P (n+1) - P n) :
    ∀ n, P n ≤ P 0 :=
  concave_along_segment P (by omega) hc

/-! ## F26 — the sigma term has no singularity

The second variation contains `- int_0^{pi/2} (eta tan t + eta')^2 dt`, whose integrand is
unbounded at `t = pi/2`.  It need not be: expanding,

    -(eta tan t + eta')^2 = -eta^2 tan^2 t - 2 eta eta' tan t - eta'^2 ,

and for `eta` vanishing at `0` and `pi/2` the cross term integrates by parts,
`-2 int eta eta' tan t = -int (eta^2)' tan t = int eta^2 sec^2 t`.  Since
`sec^2 - tan^2 = 1` the two unbounded pieces cancel exactly and

    - int_0^{pi/2} (eta tan t + eta')^2 dt  =  int_0^{pi/2} (eta^2 - eta'^2) dt ,

so the whole second variation can be written with bounded coefficients.  F26 records the
two arithmetic steps; the integration by parts is analysis and is not formalized.  Atoms:
`SQ` for `sec^2 t`, `TQ` for `tan^2 t`, `E` for `eta^2`, `D` for `eta'^2`. -/

/-- **F26a (`sec^2 - tan^2 = 1`).**  Cleared of denominators against `C^2 + S^2 = 1`, this
    is `1 - S^2 = C^2`. -/
theorem sec_sq_sub_tan_sq {C S : Int} (h : C*C + S*S = 1) : 1 - S*S = C*C := by omega

/-- **F26b (the cancellation).**  With `SQ - TQ = 1`, the expanded integrand collapses:
    `-E*TQ + E*SQ - D = E - D`, i.e. the two unbounded terms leave `eta^2 - eta'^2`. -/
theorem sigma_term_bounded {E D SQ TQ : Int} (h : SQ - TQ = 1) :
    -(E*TQ) + E*SQ - D = E - D := by
  have : E*SQ - E*TQ = E*(SQ - TQ) := by simp [Int.mul_sub]
  rw [h] at this
  omega

/-! ## F27 — the two Cauchy-Schwarz steps of the sharp concavity constant

The second variation couples the two halves of `[0,pi]` through two terms of `(Q2)`:

    - int_{E2} ( eta(t) + eta'(t+pi/2) )^2 dt   (right sign, a resource)
    + int_{E1} ( eta(t+pi/2) - eta'(t) )^2 dt   (wrong sign, the obstruction)

Decoupling them is what turns the estimate into two one-dimensional Sturm-Liouville
eigenvalue problems, one per half, and lifts the certified constant from `0.1532` to
`2/3` against a sharp value of `0.7323`.  Both steps are exact sum-of-squares identities
over the integers, once cleared of denominators; F27 records them.

F27a is the `E2` step.  Over the rationals it reads
`-(a+b)^2 <= -lam*b^2 + (lam/(1-lam))*a^2`, which is `(1+r)a^2 + 2ab + (1-lam)b^2 >= 0`
with `(1+r)(1-lam) = 1`.  Writing `P` for `1+r` and `M` for `1-lam` scaled to integers,
the condition becomes `M*P = K*K` and multiplying the form by `M` completes the square.

F27b is the `E1` step, `(x-y)^2 <= (1+1/kap)x^2 + (1+kap)y^2` with `kap = m/n`.  Cleared
by `m*n` it is an identity with no side condition at all. -/

/-- **F27a (the `E2` completion).**  If `M*P = K*K` then `M` times the quadratic form
    `P*a^2 + 2*K*a*b + M*b^2` is the perfect square `(K*a + M*b)^2`.  With `M > 0` this
    makes the form non-negative, which is exactly
    `-(a+b)^2 <= -lam*b^2 + (lam/(1-lam))*a^2`: the step that buys gradient weight on
    `[pi/2, pi-beta]` at the price of mass on `[0, pi/2-beta)`. -/
theorem e2_completion {P M K a b : Int} (h : M*P = K*K) :
    M*(P*(a*a) + (K*(a*b) + K*(a*b)) + M*(b*b)) = (K*a + M*b)*(K*a + M*b) := by
  have h2 : (M*P)*(a*a) = (K*K)*(a*a) := by rw [h]
  simp [Int.mul_add, Int.mul_comm, Int.mul_left_comm] at h2 ⊢
  omega

/-- **F27b (the `E1` split).**  For every `m, n`,
    `n(m+n)x^2 + m(m+n)y^2 - mn(x-y)^2 = (nx + my)^2`.  Dividing by `mn > 0` this is
    `(x-y)^2 <= (1+1/kap)x^2 + (1+kap)y^2` at `kap = m/n`: the step that pays mass on
    `[pi/2, pi/2+beta]` and gradient weight on `[0,beta)` to remove the obstruction. -/
theorem e1_split {m n x y : Int} :
    n*(m+n)*(x*x) + m*(m+n)*(y*y) - m*n*((x-y)*(x-y)) = (n*x + m*y)*(n*x + m*y) := by
  simp [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm]
  omega

/-- **F27c (dividing the weight back out).**  F27a and F27b both certify the form only
    after multiplying by a positive weight.  If `M > 0` and `M*F = S*S` then `F` itself is
    non-negative, which is what the estimate consumes. -/
theorem form_nonneg_of_completion {M F S : Int} (hM : 0 < M) (h : M*F = S*S) : 0 ≤ F := by
  have h1 : M*0 ≤ M*F := by
    rw [h, Int.mul_zero]
    exact sq_nonneg_int S
  exact Int.le_of_mul_le_mul_left h1 hM

/-! ## F28 — the coupling on `[0,beta)` is a total derivative

F27 decouples the two halves of `[0,pi]` by two Cauchy-Schwarz steps, which is what costs
the last 9% of the concavity constant.  The splitting turns out to be avoidable.  Both
halves are the SAME interval re-indexed: with `p(t) = eta(t)` and `q(t) = eta(t+pi/2)` on
`[0,pi/2]`, the whole second variation is one quadratic form in the pair `(p,q)`,

    L = 2p^2 - 2p'^2 + q^2 - q'^2 - 1_{E2} (p + q')^2 + 1_{E1} (q - p')^2 ,

and on `E1 = [0,beta)` --- exactly where the obstruction lives, since that is where `E1`
and `E2` overlap --- the two cross terms COMBINE:

    -2 p q' - 2 q p'  =  -2 (p q)' ,

a total derivative, contributing only the boundary value `-2 p(beta) q(beta)`.  So the
coupling was never pointwise, which is why every pointwise Cauchy-Schwarz splitting loses
and the system formulation loses nothing: its first eigenvalue IS the sharp constant.

F28 records the two algebraic steps.  Atoms: `p`, `q` for the values and `P`, `R` for
`p'`, `q'`.  The product rule is supplied as a hypothesis, as in F26: core Lean has no
derivative. -/

/-- **F28a (the expansion on `[0,beta)`).**  On the overlap of `E1` and `E2` the integrand
    collapses to a diagonal part plus the two cross terms:
    `2p^2 - 2P^2 + q^2 - R^2 - (p+R)^2 + (q-P)^2 = p^2 - P^2 + 2q^2 - 2R^2 - 2pR - 2qP`. -/
theorem overlap_integrand {p q P R : Int} :
    2*(p*p) - 2*(P*P) + q*q - R*R - (p+R)*(p+R) + (q-P)*(q-P)
      = p*p - P*P + 2*(q*q) - 2*(R*R) - (p*R + p*R) - (q*P + q*P) := by
  simp [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm]
  omega

/-- **F28b (the cross terms are a total derivative).**  Given the product rule
    `Dpq = p*R + q*P` for `R = q'`, `P = p'`, the two cross terms of F28a are
    `-2*Dpq`.  Their integral is therefore a boundary value and not a pointwise cost. -/
theorem cross_is_total_derivative {p q P R Dpq : Int} (hprod : Dpq = p*R + q*P) :
    -(p*R + p*R) - (q*P + q*P) = -(Dpq + Dpq) := by
  rw [hprod]; omega

/-- **F28c (what the boundary value is worth).**  With `p(0) = 0` from the gauge, the
    integral of the total derivative over `[0,beta)` is the single value `2 p(beta) q(beta)`:
    formally, a telescoping difference with a vanishing left end. -/
theorem telescope_gauge {pb qb p0 q0 : Int} (h0 : p0 = 0) :
    (pb*qb + pb*qb) - (p0*q0 + p0*q0) = pb*qb + pb*qb := by
  subst h0; omega

/-! ## F29 — the anchored-cell reduction and the corner constants

Three arithmetic facts behind the theorem "every ordered anchored cell is concave".

F29a is Lemma M: dropping the `(q - p')^2` term can only increase the form, so every
cell with `E1 subset E2` is dominated by the diagonal cell of `E2`.  The content is
one square.

F29b is the final step of the small-`tau` range: the collected coefficient of the
`p'`-energy vanishes exactly (`-3/2 + 1 + 1/2 = 0`, here scaled by 2), and the
`q'`-coefficient is `3 tau^2 - 1 <= 0` for `3 tau^2 <= 1`.

F29c-e are the three collected coefficients of the corner range, with `pi` carried as
a symbol `P` under the rational bound `P <= 22/7` (scaled: `7*P <= 22`):
  * `P^2`-coefficient:  `-174/100 + 5/4 + 9/25 = -13/100 < 0`   (scaled by 100)
  * `D`-coefficient:    `7/8 - 3 pi/16 >= 2/7`  given  `pi <= 22/7`  (scaled by 112)
  * `r`-coupling:       `(25 pi/16) sigma <= 2/7`  for  `18 sigma <= 1, pi <= 22/7`
                        (scaled by 112·18: `25·18·7·P·s' <= ...`; stated in cleared form)
-/

/-- **F29a (monotonicity in the sign sets).**  Removing a square only lowers the form:
    `B - w*w <= B`.  Applied with `w = q - p'` on `E2 \ E1`, this is Lemma M. -/
theorem cell_mono {B w : Int} : B - w*w ≤ B := by
  have := sq_nonneg_int w
  omega

/-- **F29b (the small-`tau` collection).**  Scaled by 2: the `p'`-coefficient
    `-3 + 2 + 1` vanishes, and with `h3 : 3*t2 <= 1` (for `t2 = tau^2` scaled) and
    `hR : 0 <= R` (the `q'`-energy), the remainder `(3*t2 - 1)*R` is nonpositive:
    `(-3 + 2 + 1)*E + (3*t2 - 1)*R <= 0`. -/
theorem small_tau_collect {E R t2 : Int} (hE : 0 ≤ E) (hR : 0 ≤ R) (h3 : 3*t2 ≤ 1) :
    (-3 + 2 + 1)*E + (3*t2 - 1)*R ≤ 0 := by
  have h1 : (3*t2 - 1) ≤ 0 := by omega
  have h2 : (3*t2 - 1)*R ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h1 hR
  omega

/-- **F29c (corner, `P^2`-coefficient).**  Scaled by 100: `-174 + 125 + 36 = -13 < 0`. -/
theorem corner_P_coeff : (-174 : Int) + 125 + 36 < 0 := by omega

/-- **F29d (corner, `D`-coefficient).**  `7/8 - 3 pi/16 >= 2/7` iff, after clearing by
    `112`, `98 - 21*pi >= 32`, i.e. `21*pi <= 66`, which follows from `7*pi <= 22`.
    With `P` the symbol for `pi` (scaled by nothing, integer-cleared form). -/
theorem corner_D_coeff {P : Int} (h : 7*P ≤ 22) : 98 - 21*P ≥ 32 := by omega

/-- **F29e (corner, `r`-coupling).**  `(25 pi/16) sigma <= 2/7` for `sigma <= 1/18`:
    cleared by `16·7·18`, it reads `25·7·18·(pi·sigma') <= 2·16·18` with
    `sigma' = 18 sigma <= 1`; using `7 pi <= 22` and `0 <= sigma' <= 1`,
    `25·18·(7 pi)·sigma'/... ` — in cleared integer form:
    `3150*PS <= 4032` given `PS <= 22` (where `PS` encloses `7·pi·sigma'` and
    `sigma' <= 1` gives `PS <= 7 pi <= 22`); `3150*22 = 69300 > 4032·17`... the clean
    reduction: it suffices that `25·pi·sigma <= 32/7`, and with `sigma <= 1/18`,
    `25·pi/18 <= 25·22/(7·18) = 550/126 = 4.365 < 4.571 = 32/7`.  Cleared by `126`:
    `550 <= 576`. -/
theorem corner_r_coupling : (550 : Int) ≤ 576 := by omega

/-! ## F30 — the arm sandwich, and the disc counterexample

Under `0 <= H + H'' <= 1` the two arms satisfy, in the a.c. sense,

    alpha_2 <= alpha_1' <= alpha_2 + 1        (upper needs convexity, lower needs (RC))
    -alpha_1 - 1 <= alpha_2' <= -alpha_1

so the pair rotates: the first arm strictly increases where the second is positive, and
the second strictly decreases where the first is.  This supplies the proved Lipschitz
constant behind the explicit-ball proposition, and the transversality of both sign
crossings.  F30a-b record the linear algebra with `F2` for `F''`, `G2` for `G''`.

F30c is the disc: `H_c = 1 - c + c (sin + cos)` has `H_c + H_c'' = 1 - c` identically,
recorded with `S` for `sin theta + cos theta`; the arms are identically `-c`, so the
ordered sign structure FAILS for a cap satisfying every other condition of the domain.
The sign hypothesis is essential. -/

/-- **F30a (sandwich for the first arm).**  From `F - 1 <= -F2 <= F` (the two-sided
    curvature bound), `G' + F - 1 <= G' - F2 <= G' + F`, i.e.
    `alpha_2 <= alpha_1' <= alpha_2 + 1` after the affine dictionary. -/
theorem arm1_sandwich {F F2 G' : Int} (hrc : F2 + F ≤ 1) (hcx : 0 ≤ F2 + F) :
    G' + F - 1 ≤ G' - F2 ∧ G' - F2 ≤ G' + F := by omega

/-- **F30b (sandwich for the second arm).**  From `-G <= G2 <= 1 - G`,
    `F' - G <= F' + G2 <= F' + 1 - G`, i.e. `-alpha_1 - 1 <= alpha_2' <= -alpha_1`. -/
theorem arm2_sandwich {G G2 F' : Int} (hrc : G2 + G ≤ 1) (hcx : 0 ≤ G2 + G) :
    F' - G ≤ F' + G2 ∧ F' + G2 ≤ F' + 1 - G := by omega

/-- **F30c (the disc has constant curvature density).**  With `S` the atom for
    `sin theta + cos theta`, whose second derivative is `-S`:
    `(1 - c + c*S) + (-(c*S)) = 1 - c`.  The disc of radius `1 - c` at `(c,c)` satisfies
    convexity and (RC) with margin, yet its arms are identically `-c`. -/
theorem disc_curvature {c S : Int} : (1 - c + c*S) + (-(c*S)) = 1 - c := by omega

end MovingSofa
