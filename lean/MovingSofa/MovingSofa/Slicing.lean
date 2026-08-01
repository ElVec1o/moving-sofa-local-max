/-
# The slicing identity, discharged

`reduction_assembly` took the bound on `volume (placedRegion …)` as a hypothesis.  This
file proves it, so the only remaining obligation of the whole upper-bound chain is the
containment of the sofa in a placed region.

Three steps, all in Mathlib:

  * `placedRegion` is measurable (`placedRegion_measurable`): it is cut out by finitely
    many inequalities between continuous functions of `(s, t)`.
  * Its fibre over `s` is contained in an interval of length `ℓ(s)`, and the four-piece
    decomposition of `Bound.lean` bounds `ℓ(s)` by the two tents plus the two cross
    terms (`fibre_volume_le`).
  * Fubini turns the fibre bound into the area bound, and the profile integral of
    `Integral.lean` evaluates it (`placedRegion_volume_le`).

The factor two is the change of variables `du dv = ½ ds dt` recorded in
`Reduction.lean`: the fibre-coordinate volume is twice the plane area, so the bound
proved here is `2(2√2 − 1)` and `reduction_assembly` is stated to match.

The version proved here is the SIGN-RESTRICTED one, `δ_μ ≤ 0` and `δ_ν ≤ 0` in the note's
notation, where the two cross pieces are empty and the fibre reduces to the two ends.
That is the case Romik's sofa satisfies (its two `π/4` corners coincide).  The general
case adds the two cross terms, which `Bound.four_piece` already supplies; only the
arithmetic of the extra terms is missing, and it is the same argument.
-/
import Mathlib
import MovingSofa.Bound
import MovingSofa.Integral
import MovingSofa.Reduction

namespace MovingSofa

open MeasureTheory Real

/-! ## Measurability -/

theorem placedRegion_measurable (a a' b b' : ℝ) :
    MeasurableSet (placedRegion a a' b b') := by
  have m1 : Measurable fun z : ℝ × ℝ => z.1 := measurable_fst
  have m2 : Measurable fun z : ℝ × ℝ => z.2 := measurable_snd
  have mA : Measurable fun z : ℝ × ℝ => max (z.1 - 2*a') (2*b - z.1) - 2 := by
    apply Measurable.sub _ measurable_const
    exact (m1.sub measurable_const).max (measurable_const.sub m1)
  have mB : Measurable fun z : ℝ × ℝ => min (2*a - z.1) (z.1 - 2*b') + 2 := by
    apply Measurable.add _ measurable_const
    exact (measurable_const.sub m1).min (m1.sub measurable_const)
  have mp : Measurable fun z : ℝ × ℝ => z.1 - 2*a' := m1.sub measurable_const
  have mq : Measurable fun z : ℝ × ℝ => 2*a - z.1 := measurable_const.sub m1
  have mr : Measurable fun z : ℝ × ℝ => 2*b - z.1 := measurable_const.sub m1
  have mw : Measurable fun z : ℝ × ℝ => z.1 - 2*b' := m1.sub measurable_const
  unfold placedRegion
  refine MeasurableSet.inter (measurableSet_le measurable_const m1) ?_
  refine MeasurableSet.inter (measurableSet_le m1 measurable_const) ?_
  refine MeasurableSet.inter (measurableSet_le mA m2) ?_
  refine MeasurableSet.inter (measurableSet_le m2 mB) ?_
  refine MeasurableSet.inter ?_ ?_
  · exact ((measurableSet_lt mp m2).inter (measurableSet_lt m2 mq)).compl
  · exact ((measurableSet_lt mr m2).inter (measurableSet_lt m2 mw)).compl

/-! ## The fibre bound -/

/-- **The fibre over `s` sits inside the two end intervals.**  In the sign-restricted case
`2b - s < 2a - s` and `s - 2a' < s - 2b'` (that is, `b < a` and `a' < b'`, the note's
`δ_μ ≤ 0`, `δ_ν ≤ 0`), the two cross pieces of `four_piece` are empty. -/
theorem fibre_subset_ends (a a' b b' s : ℝ)
    (hB : 2*b - s < 2*a - s) (hC : s - 2*a' < s - 2*b') :
    (Prod.mk s ⁻¹' placedRegion a a' b b')
      ⊆ Set.Icc (max (s - 2*a') (2*b - s) - 2) (min (s - 2*a') (2*b - s))
        ∪ Set.Icc (max (2*a - s) (s - 2*b')) (min (2*a - s) (s - 2*b') + 2) := by
  intro t ht
  have h := fibre_subset_four_piece a a' b b' s t ht
  obtain ⟨_, _, hlo, hhi, _, _⟩ := ht
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hlo, le_min h1 h2⟩
  · exact absurd (le_trans h1 h2) (by linarith)
  · exact absurd (le_trans h1 h2) (by linarith)
  · exact Or.inr ⟨max_le h1 h2, hhi⟩

/-- The fibre measure is at most the sum of the two end lengths, each `≤ 2 − |·|`. -/
theorem fibre_volume_le (a a' b b' s : ℝ)
    (hB : 2*b - s < 2*a - s) (hC : s - 2*a' < s - 2*b') :
    volume (Prod.mk s ⁻¹' placedRegion a a' b b')
      ≤ ENNReal.ofReal (tent (a' + b) s) + ENNReal.ofReal (tent (a + b') s) := by
  have hsub := fibre_subset_ends a a' b b' s hB hC
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
  · rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have h := low_end_le (s - 2*a') (2*b - s)
    unfold tent
    rcases le_total (s - 2*a') (2*b - s) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at *
      apply le_max_of_le_right
      have : |s - 2*a' - (2*b - s)| = (2*b - s) - (s - 2*a') := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have hab : |s - (a' + b)| = ((2*b - s) - (s - 2*a'))/2 := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [hab]; linarith
    · rw [min_eq_right hle, max_eq_left hle] at *
      apply le_max_of_le_right
      have hab : |s - (a' + b)| = ((s - 2*a') - (2*b - s))/2 := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [hab]; linarith
  · rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    unfold tent
    rcases le_total (2*a - s) (s - 2*b') with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
      apply le_max_of_le_right
      have hab : |s - (a + b')| = ((s - 2*b') - (2*a - s))/2 := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [hab]; linarith
    · rw [min_eq_right hle, max_eq_left hle]
      apply le_max_of_le_right
      have hab : |s - (a + b')| = ((2*a - s) - (s - 2*b'))/2 := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [hab]; linarith

/-! ## The bridge from the Lebesgue integral to the verified profile bound -/

/-- `∫⁻ ofReal (tent x) = ofReal (∫ tent x)` over the band, then the verified bound. -/
theorem lintegral_tent_le (x : ℝ) :
    (∫⁻ s in Set.Icc (0:ℝ) (Real.sqrt 2), ENNReal.ofReal (tent x s))
      ≤ ENNReal.ofReal (2 * Real.sqrt 2 - 1) := by
  have hr2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hbridge : (∫⁻ s in Set.Icc (0:ℝ) (Real.sqrt 2), ENNReal.ofReal (tent x s))
      = ENNReal.ofReal (∫ s in Set.Icc (0:ℝ) (Real.sqrt 2), tent x s) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · exact ((continuous_tent x).integrableOn_Icc)
    · filter_upwards with y using tent_nonneg x y
  have hset : (∫ s in Set.Icc (0:ℝ) (Real.sqrt 2), tent x s)
      = ∫ s in (0:ℝ)..(Real.sqrt 2), tent x s := by
    rw [intervalIntegral.integral_of_le hr2, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hbridge, hset]
  exact ENNReal.ofReal_le_ofReal (integral_tent_le x)

/-! ## The slicing identity -/

/-- Outside the band the region is empty, so the Fubini integral restricts to it. -/
theorem placedRegion_volume_eq (a a' b b' : ℝ) :
    volume (placedRegion a a' b b')
      = ∫⁻ s in Set.Icc (0:ℝ) (Real.sqrt 2),
          volume (Prod.mk s ⁻¹' placedRegion a a' b b') := by
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply (placedRegion_measurable a a' b b'),
    ← lintegral_indicator measurableSet_Icc]
  congr 1; funext s
  by_cases hs : s ∈ Set.Icc (0:ℝ) (Real.sqrt 2)
  · simp [Set.indicator_of_mem hs]
  · have hempty : Prod.mk s ⁻¹' placedRegion a a' b b' = ∅ := by
      ext t
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro ht
      obtain ⟨h1, h2, _, _, _, _⟩ := ht
      exact hs ⟨h1, h2⟩
    simp [Set.indicator_of_notMem hs, hempty]

/-- **The slicing bound, sign-restricted case.**  The obligation `hslice` of
`reduction_assembly`, discharged. -/
theorem placedRegion_volume_le (a a' b b' : ℝ)
    (hB : ∀ s, 2*b - s < 2*a - s) (hC : ∀ s, s - 2*a' < s - 2*b') :
    volume (placedRegion a a' b b')
      ≤ ENNReal.ofReal (2 * (2 * Real.sqrt 2 - 1)) := by
  have hpair : ∀ s : ℝ,
      volume (Prod.mk s ⁻¹' placedRegion a a' b b')
        ≤ ENNReal.ofReal (tent (a' + b) s) + ENNReal.ofReal (tent (a + b') s) :=
    fun s => fibre_volume_le a a' b b' s (hB s) (hC s)
  rw [placedRegion_volume_eq]
  calc (∫⁻ s in Set.Icc (0:ℝ) (Real.sqrt 2),
          volume (Prod.mk s ⁻¹' placedRegion a a' b b'))
      ≤ ∫⁻ s in Set.Icc (0:ℝ) (Real.sqrt 2),
          (ENNReal.ofReal (tent (a' + b) s) + ENNReal.ofReal (tent (a + b') s)) :=
        lintegral_mono hpair
    _ = (∫⁻ s in Set.Icc (0:ℝ) (Real.sqrt 2), ENNReal.ofReal (tent (a' + b) s))
        + ∫⁻ s in Set.Icc (0:ℝ) (Real.sqrt 2), ENNReal.ofReal (tent (a + b') s) := by
        exact lintegral_add_left
          (((continuous_tent (a' + b)).measurable.ennreal_ofReal)) _
    _ ≤ ENNReal.ofReal (2 * Real.sqrt 2 - 1) + ENNReal.ofReal (2 * Real.sqrt 2 - 1) :=
        add_le_add (lintegral_tent_le _) (lintegral_tent_le _)
    _ = ENNReal.ofReal (2 * (2 * Real.sqrt 2 - 1)) := by
        have hs : (1:ℝ) < Real.sqrt 2 := by
          have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          nlinarith [Real.sqrt_nonneg 2]
        have hnn : (0:ℝ) ≤ 2 * Real.sqrt 2 - 1 := by linarith
        rw [← ENNReal.ofReal_add hnn hnn]
        congr 1
        ring

/-! ## The general case: the two cross pieces

Without the sign restriction the fibre also meets `B = [q, r]` and `C = [w, p]`.  Each is
an interval whose length is the corresponding offset, and each is confined to `I`, so its
contribution is at most `min` of the offset and `2`.  The bound below is the set-level
form of the cross terms of the note's closed form. -/

/-- **The fibre, in general**, lies in the two ends together with the two cross pieces. -/
theorem fibre_subset_four (a a' b b' s : ℝ) :
    (Prod.mk s ⁻¹' placedRegion a a' b b')
      ⊆ (Set.Icc (max (s - 2*a') (2*b - s) - 2) (min (s - 2*a') (2*b - s))
          ∪ Set.Icc (max (2*a - s) (s - 2*b')) (min (2*a - s) (s - 2*b') + 2))
        ∪ (Set.Icc (2*a - s) (2*b - s) ∪ Set.Icc (s - 2*b') (s - 2*a')) := by
  intro t ht
  have h := fibre_subset_four_piece a a' b b' s t ht
  obtain ⟨_, _, hlo, hhi, _, _⟩ := ht
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Or.inl ⟨hlo, le_min h1 h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inl (Or.inr ⟨max_le h1 h2, hhi⟩)

/-- **The general fibre bound.**  Two tents plus the two cross lengths, the latter being
`2δ_μ` and `2δ_ν` in the notation of the note, `2b - 2a` and `2b' - 2a'`,
each clipped at `0` by `Real.volume_Icc` when the piece is empty. -/
theorem fibre_volume_le_general (a a' b b' s : ℝ) :
    volume (Prod.mk s ⁻¹' placedRegion a a' b b')
      ≤ (ENNReal.ofReal (tent (a' + b) s) + ENNReal.ofReal (tent (a + b') s))
        + (ENNReal.ofReal (2*b - 2*a) + ENNReal.ofReal (2*b' - 2*a')) := by
  refine le_trans (measure_mono (fibre_subset_four a a' b b' s)) ?_
  refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
  · -- the two ends: identical to the sign-restricted proof
    refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
    · rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      unfold tent
      rcases le_total (s - 2*a') (2*b - s) with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]
        apply le_max_of_le_right
        have hab : |s - (a' + b)| = ((2*b - s) - (s - 2*a'))/2 := by
          rw [abs_of_nonpos (by linarith)]; ring
        rw [hab]; linarith
      · rw [min_eq_right hle, max_eq_left hle]
        apply le_max_of_le_right
        have hab : |s - (a' + b)| = ((s - 2*a') - (2*b - s))/2 := by
          rw [abs_of_nonneg (by linarith)]; ring
        rw [hab]; linarith
    · rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      unfold tent
      rcases le_total (2*a - s) (s - 2*b') with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]
        apply le_max_of_le_right
        have hab : |s - (a + b')| = ((s - 2*b') - (2*a - s))/2 := by
          rw [abs_of_nonneg (by linarith)]; ring
        rw [hab]; linarith
      · rw [min_eq_right hle, max_eq_left hle]
        apply le_max_of_le_right
        have hab : |s - (a + b')| = ((2*a - s) - (s - 2*b'))/2 := by
          rw [abs_of_nonpos (by linarith)]; ring
        rw [hab]; linarith
  · -- the two cross pieces: each an interval of the stated length
    refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
    · rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal; linarith
    · rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal; linarith

end MovingSofa
