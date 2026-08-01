/-
# The Wirtinger inequalities, verified — by a shifted Riccati, with no singularity

The two remaining analytic hypotheses of the elementary constant were the Poincaré
inequalities `∫ f'² ≥ ∫ f²` (Dirichlet–Neumann) and `∫ f'² ≥ 4 ∫ f²`
(Dirichlet–Dirichlet) on `[0, π/2]`.  Their classical proofs divide by the ground state,
which vanishes at the Dirichlet ends; formalising that route needs an integration by parts
with a removable singularity.

This file avoids the singularity entirely.  The Riccati supersolution `v = k·cot(kt + c)`
with a SHIFT `c > 0` is regular on all of `[0, T]` when `kT + c < π`, and satisfies the
Riccati equation exactly: `v' = -k²/sin²(kt+c)`, so `v' + v² + k² = 0`.  The pointwise
square `(f'·sin - k·cos·f)² ≥ 0` then gives

    (v f²)' + k² f²  ≤  f'²        pointwise on [0, T],

and the fundamental theorem of calculus — ordinary, no limits — yields

    k² ∫₀ᵀ f²  ≤  ∫₀ᵀ f'²  -  v(T) f(T)²  +  v(0) f(0)² .

At the Dirichlet end `f(0) = 0` kills the `v(0)` term however large `cot c` is.  The price
of the shift is the boundary term `-v(T) f(T)² = k·tan(shift) · f(T)²`-sized loss, and
THAT is absorbed by the already-verified engine `sq_sub_le`:
`f(T)² ≤ T ∫₀ᵀ f'²`.  The result is the near-sharp inequality

    ∫ f²  ≤  (1 + T·tan c) ∫ f'²          (DN, k = 1)
    4 ∫ f²  ≤  (1 + π·tan c) ∫ f'²        (DD, k = 2, two halves glued by reflection)

for every `c > 0`, and the elementary chain of `prop:elem` has slack `1/1886`, so
`c = 1/8000` (with the crude bound `tan c ≤ 2c`) closes it.  `secondvar_assembly'` below
re-runs the assembly with the weakened Wirtinger inputs and still reaches `1/12`.

Nothing in this file is a hypothesis.  Together with `Poincare.lean` and
`SecondVar.lean`, the analytic content of Proposition "an elementary constant" is now
machine-checked end to end.
-/
import Mathlib
import MovingSofa.Poincare

namespace MovingSofa

open Real MeasureTheory intervalIntegral

variable {f f' : ℝ → ℝ}

/-! ## The shifted cotangent and its derivative -/

/-- The derivative of `k·cot(kt + c)` where the argument stays off the zeros of `sin`. -/
theorem hasDerivAt_kcot (k c t : ℝ) (h : sin (k*t + c) ≠ 0) :
    HasDerivAt (fun u => k * (cos (k*u + c) / sin (k*u + c))) (-(k^2) / sin (k*t+c)^2) t := by
  have hlin : HasDerivAt (fun u : ℝ => k*u + c) k t := by
    simpa using ((hasDerivAt_id t).const_mul k).add_const c
  have hcos : HasDerivAt (fun u => cos (k*u + c)) (-sin (k*t+c) * k) t :=
    HasDerivAt.cos hlin |>.congr_deriv (by ring)
  have hsin : HasDerivAt (fun u => sin (k*u + c)) (cos (k*t+c) * k) t :=
    HasDerivAt.sin hlin |>.congr_deriv (by ring)
  have hfin := (hcos.div hsin h).const_mul k
  have hs2 : sin (k*t+c)^2 + cos (k*t+c)^2 = 1 := by
    rw [add_comm]; exact Real.cos_sq_add_sin_sq _
  have heq : k * ((-sin (k*t+c) * k * sin (k*t+c) - cos (k*t+c) * (cos (k*t+c) * k))
      / sin (k*t+c)^2) = -(k^2) / sin (k*t+c)^2 := by
    rw [mul_div_assoc' k _ _, div_eq_div_iff (pow_ne_zero 2 h) (pow_ne_zero 2 h)]
    ring_nf
    linear_combination (-(k^2) * sin (k*t+c)^2) * hs2
  exact hfin.congr_deriv heq

/-- **The pointwise Riccati inequality**, as pure algebra: with `s = sin`, `co = cos` at
the point, `s ≠ 0` and `s² + co² = 1`,
`(-k²/s²)·b² + 2(k·co/s)·b·a + k²·b² ≤ a²`, which is `(a·s - k·co·b)² ≥ 0`. -/
theorem pointwise_riccati (a b s co k : ℝ) (hs : s ≠ 0) (hp : s^2 + co^2 = 1) :
    (-(k^2)/s^2) * b^2 + 2*(k*(co/s))*b*a + k^2*b^2 ≤ a^2 := by
  have h1 : (1 : ℝ) - s^2 - co^2 = 0 := by linarith
  have key : a^2 - ((-(k^2)/s^2) * b^2 + 2*(k*(co/s))*b*a + k^2*b^2)
      = (a*s - k*co*b)^2/s^2 + (k^2*b^2)*((1 - s^2 - co^2)/s^2) := by
    field_simp
    ring
  rw [h1] at key
  simp only [zero_div, mul_zero, add_zero] at key
  have hnn : 0 ≤ (a*s - k*co*b)^2/s^2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

/-! ## The Riccati block -/

/-- **The master block.**  For `f` continuously differentiable, `k > 0`, `c > 0` and
`k·T + c < π` with `0 ≤ T`:

  `k² ∫₀ᵀ f² + k·cot(kT+c)·f(T)² - k·cot(c)·f(0)² ≤ ∫₀ᵀ f'²`.

Entirely regular: the shift keeps `sin(kt+c) > 0` on all of `[0, T]`. -/
theorem riccati_block (hd : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    {k c T : ℝ} (hk : 0 < k) (hc0 : 0 < c) (hT : 0 ≤ T) (hr : k*T + c < π) :
    k^2 * (∫ t in (0:ℝ)..T, f t ^2)
      + k * (cos (k*T+c)/sin (k*T+c)) * f T ^2
      - k * (cos c/sin c) * f 0 ^2
      ≤ ∫ t in (0:ℝ)..T, f' t ^2 := by
  have hdifff : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hcf : Continuous f := hdifff.continuous
  -- sin(kt+c) > 0 on [0,T]
  have hsin : ∀ t ∈ Set.Icc (0:ℝ) T, 0 < sin (k*t + c) := by
    intro t ht
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  -- the auxiliary function w = v·f²
  set w : ℝ → ℝ := fun t => k * (cos (k*t + c) / sin (k*t + c)) * f t ^2 with hw
  have hwd : ∀ t ∈ Set.Icc (0:ℝ) T,
      HasDerivAt w ((-(k^2) / sin (k*t+c)^2) * f t ^2
        + (k * (cos (k*t + c) / sin (k*t + c))) * (2 * f t * f' t)) t := by
    intro t ht
    have h1 := hasDerivAt_kcot k c t (ne_of_gt (hsin t ht))
    have h2 : HasDerivAt (fun u => f u ^2) (2 * f t * f' t) t := by
      have := (hd t).mul (hd t)
      have hfun : (fun u => f u ^2) = fun u => f u * f u := by funext u; ring
      rw [hfun]
      exact this.congr_deriv (by ring)
    exact (h1.mul h2).congr_deriv (by ring)
  -- pointwise: w' + k² f² ≤ f'²
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) T,
      ((-(k^2) / sin (k*t+c)^2) * f t ^2
        + (k * (cos (k*t + c) / sin (k*t + c))) * (2 * f t * f' t)) + k^2 * f t ^2
      ≤ f' t ^2 := by
    intro t ht
    have hs := hsin t ht
    have hp : sin (k*t+c)^2 + cos (k*t+c)^2 = 1 := by
      rw [add_comm]; exact Real.cos_sq_add_sin_sq _
    have := pointwise_riccati (f' t) (f t) (sin (k*t+c)) (cos (k*t+c)) k
      (ne_of_gt hs) hp
    nlinarith [this]
  -- FTC for w on [0, T]
  have hwcont : ContinuousOn (fun t => (-(k^2) / sin (k*t+c)^2) * f t ^2
      + (k * (cos (k*t + c) / sin (k*t + c))) * (2 * f t * f' t)) (Set.Icc 0 T) := by
    apply ContinuousOn.add
    · apply ContinuousOn.mul
      · apply ContinuousOn.div continuousOn_const
        · fun_prop
        · intro t ht; exact pow_ne_zero 2 (ne_of_gt (hsin t ht))
      · fun_prop
    · apply ContinuousOn.mul
      · apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro t ht; exact ne_of_gt (hsin t ht)
      · fun_prop
  have hFTC : (∫ t in (0:ℝ)..T, ((-(k^2) / sin (k*t+c)^2) * f t ^2
      + (k * (cos (k*t + c) / sin (k*t + c))) * (2 * f t * f' t)))
      = w T - w 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hT] at ht
      exact hwd t ht
    · exact (by rw [Set.uIcc_of_le hT]; exact hwcont :
        ContinuousOn _ (Set.uIcc 0 T)).intervalIntegrable
  -- integrate the pointwise inequality
  have hci : ContinuousOn (fun t => f' t ^2 - k^2 * f t ^2
      - ((-(k^2) / sin (k*t+c)^2) * f t ^2
        + (k * (cos (k*t + c) / sin (k*t + c))) * (2 * f t * f' t))) (Set.Icc 0 T) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.sub <;> fun_prop
    · exact hwcont
  have hint : (∫ t in (0:ℝ)..T, (f' t ^2 - k^2 * f t ^2
      - ((-(k^2) / sin (k*t+c)^2) * f t ^2
        + (k * (cos (k*t + c) / sin (k*t + c))) * (2 * f t * f' t)))) ≥ 0 := by
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    have := hpt t ht
    linarith
  have hii1 : IntervalIntegrable (fun t => f' t ^2) volume 0 T := by
    apply Continuous.intervalIntegrable; fun_prop
  have hii2 : IntervalIntegrable (fun t => k^2 * f t ^2) volume 0 T := by
    apply Continuous.intervalIntegrable; fun_prop
  have hii3 : IntervalIntegrable (fun t => (-(k^2) / sin (k*t+c)^2) * f t ^2
      + (k * (cos (k*t + c) / sin (k*t + c))) * (2 * f t * f' t)) volume 0 T :=
    (by rw [Set.uIcc_of_le hT]; exact hwcont :
      ContinuousOn _ (Set.uIcc 0 T)).intervalIntegrable
  rw [intervalIntegral.integral_sub (hii1.sub hii2) hii3,
      intervalIntegral.integral_sub hii1 hii2, hFTC] at hint
  have hmul : (∫ t in (0:ℝ)..T, k^2 * f t ^2) = k^2 * ∫ t in (0:ℝ)..T, f t ^2 :=
    intervalIntegral.integral_const_mul _ _
  rw [hmul] at hint
  simp only [hw] at hint
  rw [show k*(0:ℝ) + c = c by ring] at hint
  linarith

/-! ## The two Wirtinger inequalities, with an explicit shift loss -/

/-- `tan c ≤ 2c` for `0 < c ≤ 1/2`, via `sin c ≤ c` and `cos c ≥ 7/8`. -/
theorem tan_ratio_le (c : ℝ) (h0 : 0 < c) (h1 : c ≤ 1/2) :
    sin c / cos c ≤ 2 * c := by
  have hsin : sin c ≤ c := Real.sin_le (le_of_lt h0)
  have hhalf : sin (c/2) ≤ c/2 := Real.sin_le (by linarith)
  have hhalf0 : 0 ≤ sin (c/2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · nlinarith [Real.pi_gt_three]
  have hcossq : sin (c/2)^2 = (1 - cos c)/2 := by
    have := Real.sin_sq_eq_half_sub (c/2)
    have h2 : 2*(c/2) = c := by ring
    rw [h2] at this; linarith
  have hcos : cos c ≥ 7/8 := by nlinarith [hcossq, hhalf, hhalf0]
  have hcpos : (0:ℝ) < cos c := by linarith
  rw [div_le_iff₀ hcpos]
  nlinarith

/-- **Dirichlet–Neumann Wirtinger with shift loss.**  For `f(0) = 0` and `0 < c ≤ 1/2`:
`∫₀^{π/2} f² ≤ ∫₀^{π/2} f'² + 2c·(π/2)·∫₀^{π/2} f'²`. -/
theorem wirtinger_DN (hd : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    (h0 : f 0 = 0) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1/2) :
    (∫ t in (0:ℝ)..(π/2), f t ^2)
      ≤ (1 + 2*c*(π/2)) * ∫ t in (0:ℝ)..(π/2), f' t ^2 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hpi3 : (3:ℝ) < π := Real.pi_gt_three
  have hblock := riccati_block hd hc (k := 1) (c := c) (T := π/2) one_pos hc0
    (by positivity) (by nlinarith)
  simp only [one_pow, one_mul] at hblock
  -- cot(π/2 + c) = -sin c/cos c
  have hshift : cos (π/2 + c) / sin (π/2 + c) = -(sin c/cos c) := by
    have h1 : π/2 + c = c + π/2 := by ring
    rw [h1, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    ring
  rw [hshift, h0] at hblock
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] at hblock
  -- the engine: f(π/2)² ≤ (π/2) ∫ f'²
  have heng : f (π/2)^2 ≤ (π/2) * ∫ s in (0:ℝ)..(π/2), f' s ^2 := by
    have := sq_sub_le hd hc (a := 0) (b := π/2) (by positivity)
    rw [h0, sub_zero] at this
    simpa using this
  have htan : sin c / cos c ≤ 2*c := tan_ratio_le c hc0 hc1
  have hf2 : (0:ℝ) ≤ f (π/2)^2 := sq_nonneg _
  have hgr : (0:ℝ) ≤ ∫ s in (0:ℝ)..(π/2), f' s ^2 :=
    intervalIntegral.integral_nonneg (by positivity) (fun s _ => sq_nonneg _)
  nlinarith [hblock, heng, htan, hf2, hgr, hc0]

/-- **Dirichlet–Dirichlet Wirtinger with shift loss.**  For `f(0) = f(π/2) = 0` and
`0 < c ≤ 1/2`:  `4 ∫₀^{π/2} f² ≤ (1 + 2c·π) ∫₀^{π/2} f'²`. -/
theorem wirtinger_DD (hd : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    (h0 : f 0 = 0) (hT : f (π/2) = 0) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1/2) :
    4 * (∫ t in (0:ℝ)..(π/2), f t ^2)
      ≤ (1 + 2*c*π) * ∫ t in (0:ℝ)..(π/2), f' t ^2 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hpi3 : (3:ℝ) < π := Real.pi_gt_three
  -- left half: k = 2 on [0, π/4]
  have hL := riccati_block hd hc (k := 2) (c := c) (T := π/4) two_pos hc0
    (by positivity) (by nlinarith [hpi3])
  have hshift : cos (2*(π/4)+c) / sin (2*(π/4)+c) = -(sin c/cos c) := by
    have h1 : (2:ℝ)*(π/4)+c = c + π/2 := by ring
    rw [h1, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    ring
  rw [hshift, h0] at hL
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] at hL
  -- right half: reflect r(u) = f(π/2 - u)
  set r : ℝ → ℝ := fun u => f (π/2 - u) with hrdef
  set r' : ℝ → ℝ := fun u => -f' (π/2 - u) with hrdef'
  have hrd : ∀ u, HasDerivAt r (r' u) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => π/2 - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (π/2)
    have h2 : HasDerivAt (fun v => f (π/2 - v)) (f' (π/2 - u) * (-1)) u :=
      HasDerivAt.comp u (hd _) hlin
    have : r' u = f' (π/2 - u) * (-1) := by simp [hrdef']
    rw [hrdef, this]
    exact h2
  have hrc : Continuous r' := by
    have h1 : Continuous fun u : ℝ => -f' (π/2 - u) := by fun_prop
    exact h1
  have hr0 : r 0 = 0 := by simp [hrdef, hT]
  have hR := riccati_block hrd hrc (k := 2) (c := c) (T := π/4) two_pos hc0
    (by positivity) (by nlinarith [hpi3])
  rw [hshift, hr0] at hR
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] at hR
  -- change of variables for the reflected integrals
  have hb1 : π/2 - π/4 = π/4 := by ring
  have hb2 : π/2 - 0 = π/2 := by ring
  have hcv1 : (∫ u in (0:ℝ)..(π/4), r u ^2) = ∫ t in (π/4)..(π/2), f t ^2 := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/4)
      (fun t => f t ^2) (π/2)
    rw [hb1, hb2] at h
    simpa [hrdef] using h
  have hcv2 : (∫ u in (0:ℝ)..(π/4), r' u ^2) = ∫ t in (π/4)..(π/2), f' t ^2 := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/4)
      (fun t => f' t ^2) (π/2)
    rw [hb1, hb2] at h
    have hsq : ∀ u, r' u ^2 = f' (π/2 - u)^2 := by
      intro u; simp only [hrdef']; ring
    simp_rw [hsq]
    exact h
  have hrq : r (π/4) = f (π/4) := by
    simp only [hrdef]
    rw [hb1]
  rw [hcv1, hcv2, hrq] at hR
  -- glue the halves
  have hdifff : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hcf : Continuous f := hdifff.continuous
  have hfi : ∀ a b : ℝ, IntervalIntegrable (fun t => f t ^2) volume a b := by
    intro a b; apply Continuous.intervalIntegrable; fun_prop
  have hfi' : ∀ a b : ℝ, IntervalIntegrable (fun t => f' t ^2) volume a b := by
    intro a b; apply Continuous.intervalIntegrable; fun_prop
  have hsplit1 : (∫ t in (0:ℝ)..(π/2), f t ^2)
      = (∫ t in (0:ℝ)..(π/4), f t ^2) + ∫ t in (π/4)..(π/2), f t ^2 := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _)]
  have hsplit2 : (∫ t in (0:ℝ)..(π/2), f' t ^2)
      = (∫ t in (0:ℝ)..(π/4), f' t ^2) + ∫ t in (π/4)..(π/2), f' t ^2 := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hfi' _ _) (hfi' _ _)]
  -- the engine bounds f(π/4)²
  have heng : f (π/4)^2 ≤ (π/4) * ∫ s in (0:ℝ)..(π/4), f' s ^2 := by
    have := sq_sub_le hd hc (a := 0) (b := π/4) (by positivity)
    rw [h0, sub_zero] at this
    simpa using this
  have hmono : (∫ s in (0:ℝ)..(π/4), f' s ^2) ≤ ∫ s in (0:ℝ)..(π/2), f' s ^2 := by
    rw [hsplit2]
    have : 0 ≤ ∫ t in (π/4)..(π/2), f' t ^2 :=
      intervalIntegral.integral_nonneg (by nlinarith) (fun s _ => sq_nonneg _)
    linarith
  have htan : sin c / cos c ≤ 2*c := tan_ratio_le c hc0 hc1
  have hf2 : (0:ℝ) ≤ f (π/4)^2 := sq_nonneg _
  have hgr : (0:ℝ) ≤ ∫ s in (0:ℝ)..(π/2), f' s ^2 :=
    intervalIntegral.integral_nonneg (by positivity) (fun s _ => sq_nonneg _)
  -- the product step, explicit: τ·f(π/4)² ≤ 2c·(π/4)·∫₀^{π/2} f'²
  have heng2 : f (π/4)^2 ≤ (π/4) * ∫ s in (0:ℝ)..(π/2), f' s ^2 := by
    have h1 : (π/4) * (∫ s in (0:ℝ)..(π/4), f' s ^2)
        ≤ (π/4) * ∫ s in (0:ℝ)..(π/2), f' s ^2 := by
      apply mul_le_mul_of_nonneg_left hmono (by positivity)
    linarith [heng]
  have hkey : (sin c/cos c) * f (π/4)^2
      ≤ (2*c) * ((π/4) * ∫ s in (0:ℝ)..(π/2), f' s ^2) :=
    mul_le_mul htan heng2 hf2 (by positivity)
  nlinarith [hL, hR, hkey, hsplit1, hsplit2]

/-! ## The assembly, re-run with the shifted-Wirtinger inputs -/

/-- `secondvar_assembly` with the Wirtinger inputs weakened by the shift losses
`1/1200` (DD) and `1/2500` (DN).  The chain still clears `1/12`: the left half has slack
`2/11 - 1/12` and the right half `1/1886`, and the losses fit under both. -/
theorem secondvar_assembly'
    (Pg Pm Qg Qm Qgc Qgt Qmb Qgb FL FR : ℝ)
    (hPm : 0 ≤ Pm) (hQm : 0 ≤ Qm) (hQgt : 0 ≤ Qgt) (hQgb : 0 ≤ Qgb)
    (hQgc : 0 ≤ Qgc)
    (hsplit : Qg = Qgc + Qgt)
    (hGL : (3/4) * Pg - (2 + 9/11) * Pm ≤ FL)
    (hGR : Qg + (9/20) * Qgc - Qm - 5 * Qmb ≤ FR)
    (hW4 : 4 * Pm ≤ (1 + 1/1200) * Pg)
    (hW1 : Qm ≤ (1 + 1/2500) * Qg)
    (habs : Qmb ≤ (9/200) * Qgb)
    (hsub : Qgb ≤ Qgc)
    (hcut : Qm ≤ (11/5) * Qgc + (9/50) * Qgt) :
    (1/12) * Pm ≤ FL ∧ (1/12) * Qm ≤ FR := by
  constructor
  · nlinarith [hGL, hW4, hPm]
  · have habs' : 5 * Qmb ≤ (9/40) * Qgc := by nlinarith [habs, hsub, hQgb]
    have hQgc' : (5/11) * Qm - (9/110) * Qgt ≤ Qgc := by nlinarith [hcut]
    nlinarith [hGR, habs', hQgc', hW1, hsplit, hQm, hQgt, hQgc]

/-! ## The capstone: zero analytic hypotheses -/

/-- **The elementary constant, fully verified.**  For continuously differentiable `p, q`
with `p(0) = p(π/2) = 0`, `q(0) = 0`, and any `0 ≤ β ≤ 3/10`, the decoupled forms of
Proposition "an elementary constant" dominate `1/12` of the mass:

no analytic hypothesis remains — the Wirtinger inequalities come from the shifted
Riccati block, the absorption, subset and cut inequalities from `Poincare.lean`, and the
assembly from pure arithmetic. -/
theorem elementary_constant_verified
    {p p' q q' : ℝ → ℝ}
    (hpd : ∀ t, HasDerivAt p (p' t) t) (hpc : Continuous p')
    (hqd : ∀ t, HasDerivAt q (q' t) t) (hqc : Continuous q')
    (hp0 : p 0 = 0) (hpT : p (π/2) = 0) (hq0 : q 0 = 0)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 3/10) :
    (1/12) * ((∫ t in (0:ℝ)..(π/2), p t ^2) + ∫ t in (0:ℝ)..(π/2), q t ^2)
      ≤ ((3/4) * (∫ t in (0:ℝ)..(π/2), p' t ^2)
          - (2 + 9/11) * ∫ t in (0:ℝ)..(π/2), p t ^2)
        + ((∫ t in (0:ℝ)..(π/2), q' t ^2)
          + (9/20) * (∫ t in (0:ℝ)..(π/2 - β), q' t ^2)
          - (∫ t in (0:ℝ)..(π/2), q t ^2)
          - 5 * ∫ t in (0:ℝ)..β, q t ^2) := by
  have hpi3 : (3:ℝ) < π := Real.pi_gt_three
  have hpi315 : π < 3.15 := Real.pi_lt_d2
  have hβπ : β ≤ π/2 - β := by nlinarith
  have hqint : ∀ a b : ℝ, IntervalIntegrable (fun s => q' s ^2) volume a b := by
    intro a b; apply Continuous.intervalIntegrable; fun_prop
  -- the ten quantities
  set Pg := ∫ t in (0:ℝ)..(π/2), p' t ^2 with hPgd
  set Pm := ∫ t in (0:ℝ)..(π/2), p t ^2 with hPmd
  set Qg := ∫ t in (0:ℝ)..(π/2), q' t ^2 with hQgd
  set Qm := ∫ t in (0:ℝ)..(π/2), q t ^2 with hQmd
  set Qgc := ∫ t in (0:ℝ)..(π/2 - β), q' t ^2 with hQgcd
  set Qgt := ∫ t in (π/2 - β)..(π/2), q' t ^2 with hQgtd
  set Qmb := ∫ t in (0:ℝ)..β, q t ^2 with hQmbd
  set Qgb := ∫ t in (0:ℝ)..β, q' t ^2 with hQgbd
  -- nonnegativity
  have hPm0 : 0 ≤ Pm :=
    intervalIntegral.integral_nonneg (by positivity) (fun s _ => sq_nonneg _)
  have hQm0 : 0 ≤ Qm :=
    intervalIntegral.integral_nonneg (by positivity) (fun s _ => sq_nonneg _)
  have hQgt0 : 0 ≤ Qgt :=
    intervalIntegral.integral_nonneg (by nlinarith) (fun s _ => sq_nonneg _)
  have hQgb0 : 0 ≤ Qgb :=
    intervalIntegral.integral_nonneg hβ0 (fun s _ => sq_nonneg _)
  have hQgc0 : 0 ≤ Qgc :=
    intervalIntegral.integral_nonneg (by nlinarith) (fun s _ => sq_nonneg _)
  -- the split
  have hsplit : Qg = Qgc + Qgt := by
    rw [hQgd, hQgcd, hQgtd,
      intervalIntegral.integral_add_adjacent_intervals (hqint _ _) (hqint _ _)]
  -- Wirtinger with shift c = 1/8000
  have hW4 : 4 * Pm ≤ (1 + 1/1200) * Pg := by
    have h := wirtinger_DD hpd hpc hp0 hpT (c := 1/8000) (by norm_num) (by norm_num)
    have hfac : 2*(1/8000 : ℝ)*π ≤ 1/1200 := by nlinarith
    have hPg0 : 0 ≤ Pg :=
      intervalIntegral.integral_nonneg (by positivity) (fun s _ => sq_nonneg _)
    nlinarith [h, hfac, hPg0]
  have hW1 : Qm ≤ (1 + 1/2500) * Qg := by
    have h := wirtinger_DN hqd hqc hq0 (c := 1/8000) (by norm_num) (by norm_num)
    have hfac : 2*(1/8000 : ℝ)*(π/2) ≤ 1/2500 := by nlinarith
    have hQg0 : 0 ≤ Qg :=
      intervalIntegral.integral_nonneg (by positivity) (fun s _ => sq_nonneg _)
    nlinarith [h, hfac, hQg0]
  -- absorption
  have habs : Qmb ≤ (9/200) * Qgb := by
    have h := habs_verified hqd hqc hq0 hβ0
    have : (β^2/2 : ℝ) ≤ 9/200 := by nlinarith
    nlinarith [h, hQgb0]
  -- subset
  have hsub : Qgb ≤ Qgc := hsub_verified q' hqc hβ0 hβπ
  -- the cut, with the numeric constants
  have hcut : Qm ≤ (11/5) * Qgc + (9/50) * Qgt := by
    have h := hcut_verified hqd hqc hq0 (c₀ := π/2 - β) (T := π/2)
      (by nlinarith) (by nlinarith)
    have hLβ : π/2 - (π/2 - β) = β := by ring
    rw [hLβ] at h
    have hc1 : ((π/2 - β)^2/2 + 2*(π/2 - β)*β : ℝ) ≤ 11/5 := by nlinarith
    have hc2 : (2*β^2 : ℝ) ≤ 9/50 := by nlinarith
    nlinarith [h, hQgc0, hQgt0]
  have := secondvar_assembly' Pg Pm Qg Qm Qgc Qgt Qmb Qgb
    ((3/4) * Pg - (2 + 9/11) * Pm)
    (Qg + (9/20) * Qgc - Qm - 5 * Qmb)
    hPm0 hQm0 hQgt0 hQgb0 hQgc0 hsplit (le_refl _) (le_refl _)
    hW4 hW1 habs hsub hcut
  linarith [this.1, this.2]

end MovingSofa
