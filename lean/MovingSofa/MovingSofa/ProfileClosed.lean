/-
# Lemma E, verified end to end

`LemmaE.lean` machine-checks the assembly of the profile inequality from three analytic
facts L1, L3, L4, and `Excess.lean` proves the identities behind L4 on the band.  This
file discharges everything that was still a hypothesis:

  * the four ramp integrals (`ramp_up_in`, `ramp_up_ge`, `ramp_down_in`, `ramp_down_le`),
    each a split-and-identify computation with no absolute values;
  * the clipping loss on the band, `Kloss x ≤ (x - √2/2)²/2`, by the zone analysis
    `[0, √2-1) / [√2-1, 1] / (1, √2]` in which at most one ramp is active;
  * the closed forms of `C` to the right of the band (`Cfun_right`, `Cfun_far`) and the
    reflection `Cfun_symm`, which delivers the left side for free;
  * (L3) and (L4) as the `∀`-statements `L3_full`, `L4_full`;
  * the triangle bound (L1), `∫ F ≤ D²/4`, by extending the domain and splitting at the
    midpoint; and the cap bounds (L2);
  * the final statements `lemmaE_verified` and `profile_bound_verified`, the latter being
    Lemma "the profile inequality" of the note in its original `g`-form.

After this file the two-hallway upper bound `A_ambi ≤ 2√2 - 1` has every analytic step of
its proof machine-checked except the reduction from the sofa to the placement problem
(a geometry statement, PROVED in the note) — no covering, no interval arithmetic, no
numerics of any kind remain in the verified chain.
-/
import Mathlib
import MovingSofa.Integral
import MovingSofa.LemmaE
import MovingSofa.Excess

namespace MovingSofa

open Real MeasureTheory

/-! ## The four ramp integrals -/

/-- `∫_0^b (s-k)⁺ ds = (b-k)²/2` when `0 ≤ k ≤ b`. -/
theorem ramp_up_in (b k : ℝ) (h0 : 0 ≤ k) (h1 : k ≤ b) :
    (∫ s in (0:ℝ)..b, max 0 (s - k)) = (b - k)^2/2 := by
  have hi : ∀ a c : ℝ, IntervalIntegrable (fun s => max 0 (s - k)) volume a c := by
    intro a c; apply Continuous.intervalIntegrable; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := k) (c := b)
      (hi _ _) (hi _ _)]
  have hL : (∫ s in (0:ℝ)..k, max 0 (s - k)) = 0 := by
    have : (∫ s in (0:ℝ)..k, max 0 (s - k)) = ∫ s in (0:ℝ)..k, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs; rw [Set.uIcc_of_le h0] at hs
      exact max_eq_left (by linarith [hs.2])
    rw [this]; simp
  have hR : (∫ s in k..b, max 0 (s - k)) = (b - k)^2/2 := by
    have h1' : (∫ s in k..b, max 0 (s - k)) = ∫ s in k..b, (s - k) := by
      apply intervalIntegral.integral_congr
      intro s hs; rw [Set.uIcc_of_le h1] at hs
      exact max_eq_right (by linarith [hs.1])
    rw [h1', intervalIntegral.integral_comp_sub_right (fun u => u) k, integral_id]
    ring
  rw [hL, hR]; ring

/-- `∫_0^b (s-k)⁺ ds = 0` when `b ≤ k`. -/
theorem ramp_up_ge (b k : ℝ) (h0 : 0 ≤ b) (h : b ≤ k) :
    (∫ s in (0:ℝ)..b, max 0 (s - k)) = 0 := by
  have : (∫ s in (0:ℝ)..b, max 0 (s - k)) = ∫ s in (0:ℝ)..b, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs; rw [Set.uIcc_of_le h0] at hs
    exact max_eq_left (by linarith [hs.2])
  rw [this]; simp

/-- `∫_0^b (k-s)⁺ ds = k²/2` when `0 ≤ k ≤ b`. -/
theorem ramp_down_in (b k : ℝ) (h0 : 0 ≤ k) (h1 : k ≤ b) :
    (∫ s in (0:ℝ)..b, max 0 (k - s)) = k^2/2 := by
  have hi : ∀ a c : ℝ, IntervalIntegrable (fun s => max 0 (k - s)) volume a c := by
    intro a c; apply Continuous.intervalIntegrable; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := k) (c := b)
      (hi _ _) (hi _ _)]
  have hL : (∫ s in (0:ℝ)..k, max 0 (k - s)) = k^2/2 := by
    have h1' : (∫ s in (0:ℝ)..k, max 0 (k - s)) = ∫ s in (0:ℝ)..k, (k - s) := by
      apply intervalIntegral.integral_congr
      intro s hs; rw [Set.uIcc_of_le h0] at hs
      exact max_eq_right (by linarith [hs.2])
    rw [h1', intervalIntegral.integral_comp_sub_left (fun u => u) k, integral_id]
    ring
  have hR : (∫ s in k..b, max 0 (k - s)) = 0 := by
    have : (∫ s in k..b, max 0 (k - s)) = ∫ s in k..b, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs; rw [Set.uIcc_of_le h1] at hs
      exact max_eq_left (by linarith [hs.1])
    rw [this]; simp
  rw [hL, hR]; ring

/-- `∫_0^b (k-s)⁺ ds = 0` when `k ≤ 0 ≤ b`. -/
theorem ramp_down_le (b k : ℝ) (h0 : 0 ≤ b) (hk : k ≤ 0) :
    (∫ s in (0:ℝ)..b, max 0 (k - s)) = 0 := by
  have : (∫ s in (0:ℝ)..b, max 0 (k - s)) = ∫ s in (0:ℝ)..b, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs; rw [Set.uIcc_of_le h0] at hs
    exact max_eq_left (by linarith [hs.1])
  rw [this]; simp

/-! ## The clipping loss on the band -/

/-- `(|y|-1)⁺ = (y-1)⁺ + (-y-1)⁺`: the two clipping tails are disjoint. -/
theorem pos_part_abs_split (y : ℝ) :
    max 0 (|y| - 1) = max 0 (y - 1) + max 0 (-y - 1) := by
  rcases le_total 0 y with h | h
  · have h1 : max 0 (-y - 1) = 0 := max_eq_left (by linarith)
    rw [abs_of_nonneg h, h1]; ring
  · have h1 : max 0 (y - 1) = 0 := max_eq_left (by linarith)
    rw [abs_of_nonpos h, h1]; ring

/-- The clipping loss splits into its two ramps. -/
theorem Kloss_split (x : ℝ) :
    Kloss x = (∫ s in (0:ℝ)..(Real.sqrt 2), max 0 (s - (x+1)))
            + ∫ s in (0:ℝ)..(Real.sqrt 2), max 0 ((x-1) - s) := by
  have hi1 : IntervalIntegrable (fun s => max 0 (s - (x+1))) volume 0 (Real.sqrt 2) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable (fun s => max 0 ((x-1) - s)) volume 0 (Real.sqrt 2) := by
    apply Continuous.intervalIntegrable; fun_prop
  unfold Kloss
  rw [← intervalIntegral.integral_add hi1 hi2]
  apply intervalIntegral.integral_congr
  intro s _
  have := pos_part_abs_split (s - x)
  have e1 : s - x - 1 = s - (x+1) := by ring
  have e2 : -(s - x) - 1 = (x-1) - s := by ring
  rw [e1, e2] at this
  exact this

/-- **The clipping loss is at most half the squared offset**, for `x` in the band.  The
zone analysis: at most one ramp is active, and each active ramp is dominated because
`√2 - 1 ≤ √2/2 ≤ 1`. -/
theorem Kloss_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.sqrt 2) :
    Kloss x ≤ (x - Real.sqrt 2/2)^2/2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hs1 : 1 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  rw [Kloss_split]
  rcases le_total x 1 with hc | hc
  · -- down-ramp dead: k = x-1 ≤ 0
    rw [ramp_down_le _ _ (Real.sqrt_nonneg 2) (by linarith)]
    rcases le_total (x+1) (Real.sqrt 2) with hu | hu
    · rw [ramp_up_in _ _ (by linarith) hu]
      -- (√2-(x+1))² ≤ (x-√2/2)²: both sides of the same sign comparison
      nlinarith [sq_nonneg (Real.sqrt 2/2 - x), sq_nonneg (Real.sqrt 2 - x - 1)]
    · rw [ramp_up_ge _ _ (Real.sqrt_nonneg 2) hu]
      nlinarith [sq_nonneg (x - Real.sqrt 2/2)]
  · -- up-ramp dead: x+1 ≥ 2 > √2
    rw [ramp_up_ge _ _ (Real.sqrt_nonneg 2) (by linarith)]
    rw [ramp_down_in _ _ (by linarith) (by nlinarith)]
    -- (x-1)² ≤ (x-√2/2)²  since  √2/2 ≤ 1 ≤ x
    nlinarith [sq_nonneg (x - 1)]

/-- **(L4) on the band.** -/
theorem L4_band (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.sqrt 2) :
    (x - Real.sqrt 2/2)^2/2 ≤ (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s) - 1/2 :=
  L4_of_Kloss_le x hx0 hx1 (by
    have := Kloss_le x hx0 hx1
    linarith)

/-! ## `C` outside the band -/

/-- On `[√2, √2+1]`, `C x = √2 - (√2+1-x)²/2`. -/
theorem Cfun_right (x : ℝ) (h0 : Real.sqrt 2 ≤ x) (h1 : x ≤ Real.sqrt 2 + 1) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s) = Real.sqrt 2 - (Real.sqrt 2 + 1 - x)^2/2 := by
  have hs1 : 1 < Real.sqrt 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hpt : ∀ s ∈ Set.uIcc (0:ℝ) (Real.sqrt 2),
      cap x s = 1 - max 0 (s - (x-1)) := by
    intro s hs
    rw [Set.uIcc_of_le (Real.sqrt_nonneg 2)] at hs
    have hsx : s ≤ x := le_trans hs.2 h0
    unfold cap
    rw [abs_of_nonpos (by linarith)]
    rcases le_total (s - (x-1)) 0 with h | h
    · rw [max_eq_left h, min_eq_right (by linarith)]; ring
    · rw [max_eq_right h, min_eq_left (by linarith)]; ring
  have hi : IntervalIntegrable (fun s => max 0 (s - (x-1))) volume 0 (Real.sqrt 2) := by
    apply Continuous.intervalIntegrable; fun_prop
  calc (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s)
      = ∫ s in (0:ℝ)..(Real.sqrt 2), (1 - max 0 (s - (x-1))) :=
        intervalIntegral.integral_congr hpt
    _ = Real.sqrt 2 - (Real.sqrt 2 + 1 - x)^2/2 := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
          ramp_up_in _ _ (by linarith) (by linarith)]
        simp; ring

/-- Beyond `√2+1`, `C x = √2`. -/
theorem Cfun_far (x : ℝ) (h : Real.sqrt 2 + 1 ≤ x) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s) = Real.sqrt 2 := by
  have hpt : ∀ s ∈ Set.uIcc (0:ℝ) (Real.sqrt 2), cap x s = 1 := by
    intro s hs
    rw [Set.uIcc_of_le (Real.sqrt_nonneg 2)] at hs
    unfold cap
    rw [abs_of_nonpos (by linarith [hs.2])]
    exact min_eq_right (by linarith [hs.2])
  calc (∫ s in (0:ℝ)..(Real.sqrt 2), cap x s)
      = ∫ s in (0:ℝ)..(Real.sqrt 2), (1:ℝ) := intervalIntegral.integral_congr hpt
    _ = Real.sqrt 2 := by simp

/-- **Reflection.**  `C(√2 - x) = C x`, so the left side of the band comes for free. -/
theorem Cfun_symm (x : ℝ) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), cap (Real.sqrt 2 - x) s)
      = ∫ s in (0:ℝ)..(Real.sqrt 2), cap x s := by
  have h : ∀ s : ℝ, cap (Real.sqrt 2 - x) s = cap x (Real.sqrt 2 - s) := by
    intro s; unfold cap
    congr 1
    rw [abs_sub_comm]
    congr 1; ring
  calc (∫ s in (0:ℝ)..(Real.sqrt 2), cap (Real.sqrt 2 - x) s)
      = ∫ s in (0:ℝ)..(Real.sqrt 2), cap x (Real.sqrt 2 - s) :=
        intervalIntegral.integral_congr (fun s _ => h s)
    _ = ∫ s in (Real.sqrt 2 - Real.sqrt 2)..(Real.sqrt 2 - 0), cap x s :=
        intervalIntegral.integral_comp_sub_left (cap x) (Real.sqrt 2)
    _ = ∫ s in (0:ℝ)..(Real.sqrt 2), cap x s := by norm_num

/-! ## (L3) and (L4), in full -/

/-- **(L3).**  `C x < 1` confines `x` to within `1` of the midpoint. -/
theorem L3_full (x : ℝ) (h : Cfun x < 1) : |x - Real.sqrt 2/2| ≤ 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs54 : (5:ℝ)/4 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have key : ∀ y : ℝ, Real.sqrt 2/2 + 1 ≤ y →
      1 ≤ ∫ s in (0:ℝ)..(Real.sqrt 2), cap y s := by
    intro y hy
    rcases le_total (Real.sqrt 2 + 1) y with hf | hf
    · rw [Cfun_far y hf]; linarith
    · rw [Cfun_right y (by nlinarith) hf]
      have hb : Real.sqrt 2 + 1 - y ≤ Real.sqrt 2/2 := by linarith
      have hb0 : 0 ≤ Real.sqrt 2 + 1 - y := by linarith
      nlinarith [sq_nonneg (Real.sqrt 2 + 1 - y)]
  rw [abs_le]
  constructor
  · -- lower bound: if x < √2/2 - 1 then C(√2-x) ≥ 1 = C x, contradiction
    by_contra hcon
    push_neg at hcon
    have hy : Real.sqrt 2/2 + 1 ≤ Real.sqrt 2 - x := by linarith
    have hk := key (Real.sqrt 2 - x) hy
    rw [Cfun_symm x] at hk
    unfold Cfun at h
    linarith
  · by_contra hcon
    push_neg at hcon
    have hk := key x (by linarith)
    unfold Cfun at h
    linarith

/-- **(L4).**  On `|x - √2/2| ≤ 1` the excess dominates half the squared offset. -/
theorem L4_full (x : ℝ) (h : |x - Real.sqrt 2/2| ≤ 1) :
    (x - Real.sqrt 2/2)^2/2 ≤ efun x := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hs54 : (5:ℝ)/4 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  obtain ⟨hl, hr⟩ := abs_le.mp h
  have outer : ∀ y : ℝ, Real.sqrt 2 ≤ y → y ≤ Real.sqrt 2/2 + 1 →
      (y - Real.sqrt 2/2)^2/2 ≤ (∫ s in (0:ℝ)..(Real.sqrt 2), cap y s) - 1/2 := by
    intro y hy0 hy1
    rw [Cfun_right y hy0 (by linarith)]
    have halg := L4_outer_algebra (y - Real.sqrt 2/2) (by nlinarith) (by linarith)
    nlinarith [halg]
  unfold efun Cfun
  rcases le_total 0 x with hpos | hneg
  · rcases le_total x (Real.sqrt 2) with hband | houter
    · have hb := L4_band x hpos hband
      linarith
    · have := outer x houter (by linarith)
      linarith
  · -- x ≤ 0: reflect to y = √2 - x ∈ [√2, √2/2 + 1]
    have hy0 : Real.sqrt 2 ≤ Real.sqrt 2 - x := by linarith
    have hy1 : Real.sqrt 2 - x ≤ Real.sqrt 2/2 + 1 := by linarith
    have hout := outer (Real.sqrt 2 - x) hy0 hy1
    rw [Cfun_symm x] at hout
    have he : (Real.sqrt 2 - x - Real.sqrt 2/2)^2 = (x - Real.sqrt 2/2)^2 := by
      have hid : Real.sqrt 2 - x - Real.sqrt 2/2 = -(x - Real.sqrt 2/2) := by
        field_simp; ring
      rw [hid, neg_sq]
    rw [he] at hout
    linarith

/-! ## (L1), (L2), and the verified Lemma E -/

/-- The one-sided triangle profile. -/
noncomputable def Tfun (m₁ m₂ s : ℝ) : ℝ := min (max 0 (s - m₁)) (max 0 (m₂ - s))

/-- The capped profile of the note, `F`. -/
noncomputable def Ffun (m₁ m₂ s : ℝ) : ℝ :=
  min (Tfun m₁ m₂ s) (min 1 ((m₂ - m₁)/2))

lemma Tfun_nonneg (m₁ m₂ s : ℝ) : 0 ≤ Tfun m₁ m₂ s :=
  le_min (le_max_left _ _) (le_max_left _ _)

lemma continuous_Tfun (m₁ m₂ : ℝ) : Continuous (Tfun m₁ m₂) := by
  unfold Tfun; fun_prop

lemma continuous_Ffun (m₁ m₂ : ℝ) : Continuous (Ffun m₁ m₂) := by
  unfold Ffun Tfun; fun_prop

/-- **(L1): the triangle integral.**  `∫_0^√2 T ≤ D²/4`, by extending the domain to
`[min 0 m₁, max √2 m₂]` and splitting at the midpoint. -/
theorem L1_triangle (m₁ m₂ : ℝ) (hm : m₁ ≤ m₂) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), Tfun m₁ m₂ s) ≤ (m₂ - m₁)^2/4 := by
  set a := min 0 m₁ with ha
  set b := max (Real.sqrt 2) m₂ with hb
  have hii : ∀ p q : ℝ, IntervalIntegrable (Tfun m₁ m₂) volume p q :=
    fun p q => (continuous_Tfun m₁ m₂).intervalIntegrable p q
  have ha0 : a ≤ 0 := min_le_left _ _
  have ham : a ≤ m₁ := min_le_right _ _
  have hsb : Real.sqrt 2 ≤ b := le_max_left _ _
  have hmb : m₂ ≤ b := le_max_right _ _
  -- extension: the two side pieces are nonnegative
  have hext : (∫ s in (0:ℝ)..(Real.sqrt 2), Tfun m₁ m₂ s) ≤ ∫ s in a..b, Tfun m₁ m₂ s := by
    have hsplit : (∫ s in a..b, Tfun m₁ m₂ s)
        = (∫ s in a..(0:ℝ), Tfun m₁ m₂ s) + (∫ s in (0:ℝ)..(Real.sqrt 2), Tfun m₁ m₂ s)
          + ∫ s in (Real.sqrt 2)..b, Tfun m₁ m₂ s := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
          intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
    have hp1 : 0 ≤ ∫ s in a..(0:ℝ), Tfun m₁ m₂ s :=
      intervalIntegral.integral_nonneg ha0 (fun s _ => Tfun_nonneg _ _ _)
    have hp2 : 0 ≤ ∫ s in (Real.sqrt 2)..b, Tfun m₁ m₂ s :=
      intervalIntegral.integral_nonneg hsb (fun s _ => Tfun_nonneg _ _ _)
    linarith [hsplit]
  -- the extended integral is exactly D²/4
  have hmid : m₁ ≤ (m₁ + m₂)/2 := by linarith
  have hmid2 : (m₁ + m₂)/2 ≤ m₂ := by linarith
  have hval : (∫ s in a..b, Tfun m₁ m₂ s) = (m₂ - m₁)^2/4 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := m₁) (c := b)
        (hii _ _) (hii _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := m₁) (b := (m₁+m₂)/2) (c := b)
        (hii _ _) (hii _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := (m₁+m₂)/2) (b := m₂) (c := b)
        (hii _ _) (hii _ _)]
    have hz1 : (∫ s in a..m₁, Tfun m₁ m₂ s) = 0 := by
      have : (∫ s in a..m₁, Tfun m₁ m₂ s) = ∫ s in a..m₁, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs; rw [Set.uIcc_of_le ham] at hs
        unfold Tfun
        rw [max_eq_left (by linarith [hs.2] : s - m₁ ≤ 0)]
        exact min_eq_left (le_max_left _ _)
      rw [this]; simp
    have hz2 : (∫ s in m₂..b, Tfun m₁ m₂ s) = 0 := by
      have : (∫ s in m₂..b, Tfun m₁ m₂ s) = ∫ s in m₂..b, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs; rw [Set.uIcc_of_le hmb] at hs
        unfold Tfun
        rw [max_eq_left (by linarith [hs.1] : m₂ - s ≤ 0)]
        exact min_eq_right (le_max_left _ _)
      rw [this]; simp
    have hup : (∫ s in m₁..((m₁+m₂)/2), Tfun m₁ m₂ s) = (m₂ - m₁)^2/8 := by
      have hcg : (∫ s in m₁..((m₁+m₂)/2), Tfun m₁ m₂ s)
          = ∫ s in m₁..((m₁+m₂)/2), (s - m₁) := by
        apply intervalIntegral.integral_congr
        intro s hs; rw [Set.uIcc_of_le hmid] at hs
        unfold Tfun
        rw [max_eq_right (by linarith [hs.1] : (0:ℝ) ≤ s - m₁),
            max_eq_right (by linarith [hs.2] : (0:ℝ) ≤ m₂ - s)]
        exact min_eq_left (by linarith [hs.2])
      rw [hcg, intervalIntegral.integral_comp_sub_right (fun u => u) m₁, integral_id]
      ring
    have hdn : (∫ s in ((m₁+m₂)/2)..m₂, Tfun m₁ m₂ s) = (m₂ - m₁)^2/8 := by
      have hcg : (∫ s in ((m₁+m₂)/2)..m₂, Tfun m₁ m₂ s)
          = ∫ s in ((m₁+m₂)/2)..m₂, (m₂ - s) := by
        apply intervalIntegral.integral_congr
        intro s hs; rw [Set.uIcc_of_le hmid2] at hs
        unfold Tfun
        rw [max_eq_right (by linarith [hs.1] : (0:ℝ) ≤ s - m₁),
            max_eq_right (by linarith [hs.2] : (0:ℝ) ≤ m₂ - s)]
        exact min_eq_right (by linarith [hs.1])
      rw [hcg, intervalIntegral.integral_comp_sub_left (fun u => u) m₂, integral_id]
      ring
    rw [hz1, hz2, hup, hdn]; ring
  linarith [hext, hval]

/-- `F ≤ T` pointwise, so (L1) transfers to `F`. -/
theorem L1_F (m₁ m₂ : ℝ) (hm : m₁ ≤ m₂) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), Ffun m₁ m₂ s) ≤ (m₂ - m₁)^2/4 := by
  have hmono : (∫ s in (0:ℝ)..(Real.sqrt 2), Ffun m₁ m₂ s)
      ≤ ∫ s in (0:ℝ)..(Real.sqrt 2), Tfun m₁ m₂ s := by
    apply intervalIntegral.integral_mono_on (Real.sqrt_nonneg 2)
      ((continuous_Ffun m₁ m₂).intervalIntegrable _ _)
      ((continuous_Tfun m₁ m₂).intervalIntegrable _ _)
    intro s _; exact min_le_left _ _
  linarith [L1_triangle m₁ m₂ hm]

/-- **(L2): `F` is under each clipped distance.** -/
theorem L2_F (m₁ m₂ : ℝ) (hm : m₁ ≤ m₂) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), Ffun m₁ m₂ s) ≤ Cfun m₁
      ∧ (∫ s in (0:ℝ)..(Real.sqrt 2), Ffun m₁ m₂ s) ≤ Cfun m₂ := by
  have hpt1 : ∀ s ∈ Set.Icc (0:ℝ) (Real.sqrt 2), Ffun m₁ m₂ s ≤ cap m₁ s := by
    intro s _
    unfold Ffun Tfun cap
    apply le_min
    · calc min (min (max 0 (s - m₁)) (max 0 (m₂ - s))) (min 1 ((m₂ - m₁)/2))
          ≤ min (max 0 (s - m₁)) (max 0 (m₂ - s)) := min_le_left _ _
        _ ≤ max 0 (s - m₁) := min_le_left _ _
        _ ≤ |s - m₁| := max_le (abs_nonneg _) (le_abs_self _)
    · calc min (min (max 0 (s - m₁)) (max 0 (m₂ - s))) (min 1 ((m₂ - m₁)/2))
          ≤ min 1 ((m₂ - m₁)/2) := min_le_right _ _
        _ ≤ 1 := min_le_left _ _
  have hpt2 : ∀ s ∈ Set.Icc (0:ℝ) (Real.sqrt 2), Ffun m₁ m₂ s ≤ cap m₂ s := by
    intro s _
    unfold Ffun Tfun cap
    apply le_min
    · calc min (min (max 0 (s - m₁)) (max 0 (m₂ - s))) (min 1 ((m₂ - m₁)/2))
          ≤ min (max 0 (s - m₁)) (max 0 (m₂ - s)) := min_le_left _ _
        _ ≤ max 0 (m₂ - s) := min_le_right _ _
        _ ≤ |s - m₂| := max_le (abs_nonneg _) (by rw [abs_sub_comm]; exact le_abs_self _)
    · calc min (min (max 0 (s - m₁)) (max 0 (m₂ - s))) (min 1 ((m₂ - m₁)/2))
          ≤ min 1 ((m₂ - m₁)/2) := min_le_right _ _
        _ ≤ 1 := min_le_left _ _
  constructor
  · unfold Cfun
    apply intervalIntegral.integral_mono_on (Real.sqrt_nonneg 2)
      ((continuous_Ffun m₁ m₂).intervalIntegrable _ _)
      (intervalIntegrable_cap m₁ _ _) hpt1
  · unfold Cfun
    apply intervalIntegral.integral_mono_on (Real.sqrt_nonneg 2)
      ((continuous_Ffun m₁ m₂).intervalIntegrable _ _)
      (intervalIntegrable_cap m₂ _ _) hpt2

/-- **Lemma E, verified end to end.**  No hypothesis remains. -/
theorem lemmaE_verified (m₁ m₂ : ℝ) (hm : m₁ ≤ m₂) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), Ffun m₁ m₂ s) ≤ efun m₁ + efun m₂ := by
  obtain ⟨h21, h22⟩ := L2_F m₁ m₂ hm
  exact lemmaE_of m₁ m₂ _ hm (L1_F m₁ m₂ hm) h21 h22 L3_full L4_full

/-- `∫ tent = 2√2 - 2C`: the profile integral in its original form. -/
theorem integral_tent_eq (x : ℝ) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), tent x s)
      = 2 * Real.sqrt 2 - 2 * ∫ s in (0:ℝ)..(Real.sqrt 2), cap x s := by
  have hrw : (∫ s in (0:ℝ)..(Real.sqrt 2), tent x s)
      = (∫ s in (0:ℝ)..(Real.sqrt 2), (2 - 2 * cap x s)) := by
    simp_rw [tent_eq_cap]
  rw [hrw, intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegrable_cap x _ _).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp; ring

/-- **The profile inequality of the note (`lem:profineq`), verified.**
`g(m₁) + g(m₂) + 2∫F ≤ 2(2√2 - 1)`, for every `m₁ ≤ m₂`, with `g = ∫ tent` and `F` the
capped profile.  This is the last analytic step of the unconditional two-hallway bound. -/
theorem profile_bound_verified (m₁ m₂ : ℝ) (hm : m₁ ≤ m₂) :
    (∫ s in (0:ℝ)..(Real.sqrt 2), tent m₁ s) + (∫ s in (0:ℝ)..(Real.sqrt 2), tent m₂ s)
      + 2 * (∫ s in (0:ℝ)..(Real.sqrt 2), Ffun m₁ m₂ s)
      ≤ 2 * (2 * Real.sqrt 2 - 1) := by
  have hE := lemmaE_verified m₁ m₂ hm
  have h1 := integral_tent_eq m₁
  have h2 := integral_tent_eq m₂
  unfold efun Cfun at hE
  linarith

end MovingSofa
