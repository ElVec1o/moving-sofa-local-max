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

end MovingSofa
