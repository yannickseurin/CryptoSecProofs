/-
Copyright (c) 2026 Yannick Seurin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import CryptoSecProofs.Probability

/-!
# Total Variation Distance

This file provides general definitions and properties about
the total variation distance between two probability mass functions.
See https://en.wikipedia.org/wiki/Total_variation_distance_of_probability_measures.

We use the definition based on the L₁ distance between the two PMFs. The more standard
definition is based on the supremum of the absolute difference of the measures of the two PMFs
over all (measurable) sets. The two definitions are equivalent as shown in `TVD_eq_sup_abs_sub`.
-/

open ENNReal PMF

noncomputable section

/-- Total variation distance between two probability mass functions. -/
def TVD {α : Type*} (p q : PMF α) : ℝ :=
  (∑' a : α, |(p a).toReal - (q a).toReal|) / 2

lemma TVD_fintype {α : Type*} [Fintype α] (p q : PMF α) :
    TVD p q = (∑ a : α, |(p a).toReal - (q a).toReal|) / 2 := by
  simp [TVD, tsum_fintype]

lemma TVD_self {α : Type*} (p : PMF α) :
    TVD p p = 0 := by
  simp [TVD]

lemma TVD_comm {α : Type*} (p q : PMF α) :
    TVD p q = TVD q p := by
  simp [TVD, abs_sub_comm]

lemma TVD_triangle {α : Type*} (p q r : PMF α) :
    TVD p r ≤ TVD p q + TVD q r := by
  simp only [TVD]
  let f := fun a : α ↦ |(p a).toReal - (q a).toReal|
  let g := fun a : α ↦ |(q a).toReal - (r a).toReal|
  have hf : Summable f := ((PMF.summable_toReal p).sub (PMF.summable_toReal q)).abs
  have hg : Summable g := ((PMF.summable_toReal q).sub (PMF.summable_toReal r)).abs
  have hfg : Summable (fun a ↦ f a + g a) := hf.add hg
  have hpr :
      Summable fun a : α ↦
        |((p a).toReal - (q a).toReal) + ((q a).toReal - (r a).toReal)| := by
    apply (((PMF.summable_toReal p).sub (PMF.summable_toReal r)).abs).congr
    intro a
    congr
    linarith
  calc
        (∑' a : α, |(p a).toReal - (r a).toReal|) / 2
    _ = (∑' a : α, |((p a).toReal - (q a).toReal) +
        ((q a).toReal - (r a).toReal)|) / 2 := by
      congr 1
      apply tsum_congr
      intro a
      congr
      linarith
    _ ≤ (∑' a : α, (f a + g a)) / 2 := by
      apply div_le_div_of_nonneg_right
      · exact Summable.tsum_le_tsum
          (fun a ↦ abs_add_le ((p a).toReal - (q a).toReal) ((q a).toReal - (r a).toReal))
          hpr hfg
      · norm_num
    _ = ((∑' a : α, f a) + (∑' a : α, g a)) / 2 := by
      rw [hf.tsum_add hg]
    _ ≤ (∑' a : α, f a) / 2 + (∑' a : α, g a) / 2 := by
      linarith

lemma TVD_eq_tsum_max {α : Type*} (p q : PMF α) :
    TVD p q = ∑' a : α, max 0 ((p a).toReal - (q a).toReal) := by
  simp only [TVD]
  let fp := fun a : α ↦ max 0 ((p a).toReal - (q a).toReal)
  let fm := fun a : α ↦ max 0 ((q a).toReal - (p a).toReal)
  have hfp_nonneg : ∀ a, 0 ≤ fp a := fun a ↦ le_max_left _ _
  have hfm_nonneg : ∀ a, 0 ≤ fm a := fun a ↦ le_max_left _ _
  have hfp_le : ∀ a, fp a ≤ (p a).toReal := by
    intro a
    apply max_le
    · exact ENNReal.toReal_nonneg
    · linarith [ENNReal.toReal_nonneg (a := q a)]
  have hfm_le : ∀ a, fm a ≤ (q a).toReal := by
    intro a
    apply max_le
    · exact ENNReal.toReal_nonneg
    · linarith [ENNReal.toReal_nonneg (a := p a)]
  have hfp : Summable fp := Summable.of_nonneg_of_le hfp_nonneg hfp_le (PMF.summable_toReal p)
  have hfm : Summable fm := Summable.of_nonneg_of_le hfm_nonneg hfm_le (PMF.summable_toReal q)
  have hdiff : (∑' a : α, fp a) - (∑' a : α, fm a) = 0 := by
    calc
          (∑' a : α, fp a) - (∑' a : α, fm a)
      _ = ∑' a : α, (fp a - fm a) := by
        rw [hfp.tsum_sub hfm]
      _ = ∑' a : α, ((p a).toReal - (q a).toReal) := by
        apply tsum_congr
        intro a
        simp only [fp, fm]
        simpa only [neg_sub] using
          max_zero_sub_max_zero_neg ((p a).toReal - (q a).toReal)
      _ = (∑' a : α, (p a).toReal) - (∑' a : α, (q a).toReal) := by
        rw [(PMF.summable_toReal p).tsum_sub (PMF.summable_toReal q)]
      _ = 0 := by simp [PMF.tsum_toReal_eq_one]
  calc
        (∑' a : α, |(p a).toReal - (q a).toReal|) / 2
    _ = (∑' a : α, (fp a + fm a)) / 2 := by
      congr 1
      apply tsum_congr
      intro a
      simp only [fp, fm]
      simpa only [neg_sub] using
        (max_zero_add_max_zero_neg_eq_abs ((p a).toReal - (q a).toReal)).symm
    _ = ((∑' a : α, fp a) + (∑' a : α, fm a)) / 2 := by
      rw [hfp.tsum_add hfm]
    _ = ∑' a : α, fp a := by
      linarith

lemma toMeasure_real_sub_apply {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) (s : Set α) :
    p.toMeasure.real s - q.toMeasure.real s =
      ∑' a : α, s.indicator (fun a ↦ (p a).toReal - (q a).toReal) a := by
  have hp_s : Summable fun a : α ↦ s.indicator (fun a ↦ (p a).toReal) a :=
    (PMF.summable_toReal p).indicator s
  have hq_s : Summable fun a : α ↦ s.indicator (fun a ↦ (q a).toReal) a :=
    (PMF.summable_toReal q).indicator s
  rw [toMeasure_real_apply, toMeasure_real_apply, ← hp_s.tsum_sub hq_s]
  apply tsum_congr
  intro a
  exact (congrFun (Set.indicator_sub s (fun a ↦ (p a).toReal) (fun a ↦ (q a).toReal)) a).symm

lemma abs_toMeasure_real_sub_le_TVD {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) (s : Set α) :
    |p.toMeasure.real s - q.toMeasure.real s| ≤ TVD p q := by
  let d := fun a : α ↦ (p a).toReal - (q a).toReal
  let pos := fun a : α ↦ max 0 ((p a).toReal - (q a).toReal)
  let neg := fun a : α ↦ max 0 ((q a).toReal - (p a).toReal)
  have hpos_summable : Summable pos := by
    apply Summable.of_nonneg_of_le
    · intro a
      exact le_max_left _ _
    · intro a
      apply max_le
      · exact ENNReal.toReal_nonneg (a := (p a))
      · change (p a).toReal - (q a).toReal ≤ (p a).toReal
        linarith [ENNReal.toReal_nonneg (a := q a)]
    · exact PMF.summable_toReal p
  have hneg_summable : Summable neg := by
    apply Summable.of_nonneg_of_le
    · intro a
      exact le_max_left _ _
    · intro a
      apply max_le
      · exact ENNReal.toReal_nonneg (a := (q a))
      · change (q a).toReal - (p a).toReal ≤ (q a).toReal
        linarith [ENNReal.toReal_nonneg (a := p a)]
    · exact PMF.summable_toReal q
  have hpos_tvd : (∑' a : α, pos a) = TVD p q := by
    rw [TVD_eq_tsum_max]
  have hneg_tvd : (∑' a : α, neg a) = TVD p q := by
    rw [TVD_comm, TVD_eq_tsum_max]
  have hs_summable : Summable fun a : α ↦ s.indicator d a :=
    ((PMF.summable_toReal p).sub (PMF.summable_toReal q)).indicator s
  rw [toMeasure_real_sub_apply]
  have hle_pos : (∑' a : α, s.indicator d a) ≤ TVD p q := by
    rw [← hpos_tvd]
    apply Summable.tsum_le_tsum
    · intro a
      exact Set.indicator_apply_le'
        (fun _ ↦ by
          dsimp [d, pos]
          exact le_max_right 0 ((p a).toReal - (q a).toReal))
        (fun _ ↦ by
          dsimp [pos]
          exact le_max_left 0 ((p a).toReal - (q a).toReal))
    · exact hs_summable
    · exact hpos_summable
  have hle_neg : -(∑' a : α, s.indicator d a) ≤ TVD p q := by
    rw [← hneg_tvd, ← tsum_neg]
    apply Summable.tsum_le_tsum
    · intro a
      rw [← congrFun (Set.indicator_neg s d) a]
      exact Set.indicator_apply_le'
        (fun _ ↦ by
          dsimp [d, neg]
          linarith [le_max_right 0 ((q a).toReal - (p a).toReal)])
        (fun _ ↦ by
          dsimp [neg]
          exact le_max_left 0 ((q a).toReal - (p a).toReal))
    · exact hs_summable.neg
    · exact hneg_summable
  exact abs_le.mpr ⟨by linarith, hle_pos⟩

/-- The total variation distance is the supremum of the absolute
difference of the measures of the two probability mass functions
over all measurable sets. Often used as the definition of the total
variation distance in the literature. -/
lemma TVD_eq_sup_abs_sub {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) :
    TVD p q = ⨆ (s : Set α), |p.toMeasure.real s - q.toMeasure.real s| := by
  apply le_antisymm
  · let s : Set α := {a | (q a).toReal < (p a).toReal}
    have hs_eq :
        p.toMeasure.real s - q.toMeasure.real s = TVD p q := by
      rw [toMeasure_real_sub_apply, TVD_eq_tsum_max]
      apply tsum_congr
      intro a
      by_cases h : (q a).toReal < (p a).toReal
      · have ha : a ∈ s := h
        rw [Set.indicator_of_mem ha]
        exact (max_eq_right (sub_nonneg.mpr h.le)).symm
      · have ha : a ∉ s := h
        rw [Set.indicator_of_notMem ha]
        exact (max_eq_left (sub_nonpos.mpr (not_lt.mp h))).symm
    have h_nonneg : 0 ≤ p.toMeasure.real s - q.toMeasure.real s := by
      rw [hs_eq, TVD_eq_tsum_max]
      apply tsum_nonneg
      intro a
      exact le_max_left _ _
    rw [← hs_eq, ← abs_of_nonneg h_nonneg]
    exact le_ciSup (f := fun s : Set α ↦ |p.toMeasure.real s - q.toMeasure.real s|)
      ⟨TVD p q, by
      rintro _ ⟨t, rfl⟩
      exact abs_toMeasure_real_sub_le_TVD p q t⟩ s
  · exact ciSup_le (abs_toMeasure_real_sub_le_TVD p q)

lemma TVD_eq_tsum_min {α : Type*} (p q : PMF α) :
    TVD p q = ∑' a : α, ((p a).toReal - min (p a).toReal (q a).toReal) := by
  calc
        TVD p q
    _ = ∑' a : α, max 0 ((p a).toReal - (q a).toReal) :=
      TVD_eq_tsum_max p q
    _ = ∑' a : α, ((p a).toReal - min (p a).toReal (q a).toReal) := by
      apply tsum_congr
      intro a
      exact max_zero_sub_eq_sub_min (p a).toReal (q a).toReal

lemma TVD_eq_tsum_subset {α : Type*} (p q : PMF α) :
    TVD p q = ∑' a : α,
      if (q a).toReal < (p a).toReal then ((p a).toReal - (q a).toReal) else 0 := by
  rw [TVD_eq_tsum_max]
  apply tsum_congr
  intro a
  exact max_zero_sub_ite (p a).toReal (q a).toReal

lemma TVD_eq_tsum_support_max {α : Type*} (p q : PMF α) :
    TVD p q = ∑' a : p.support, max 0 ((p a).toReal - (q a).toReal) := by
  rw [TVD_eq_tsum_max]
  symm
  apply tsum_subtype_eq_of_support_subset
    (f := fun a : α ↦ max 0 ((p a).toReal - (q a).toReal))
    (s := p.support)
  rw [Function.support_subset_iff']
  intro a ha
  have hp : p a = 0 := by
    simpa [PMF.mem_support_iff] using ha
  have hle : (p a).toReal - (q a).toReal ≤ 0 := by
    rw [hp, ENNReal.toReal_zero]
    linarith [ENNReal.toReal_nonneg (a := q a)]
  exact max_eq_left hle

lemma TVD_eq_tsum_support_min {α : Type*} (p q : PMF α) :
    TVD p q = ∑' a  : support p, ((p a).toReal - min (p a).toReal (q a).toReal) := by
  rw [TVD_eq_tsum_min]
  symm
  apply tsum_subtype_eq_of_support_subset
    (f := fun a : α ↦ ((p a).toReal - min (p a).toReal (q a).toReal))
    (s := p.support)
  rw [Function.support_subset_iff']
  intro a ha
  have hp : p a = 0 := by
    simpa [PMF.mem_support_iff] using ha
  simp [hp, ENNReal.toReal_nonneg]

/-- Applying the same function to both probability mass functions
does not increase the total variation distance. -/
lemma TVD_map {α β : Type*}
    (p q : PMF α) (f : α → β) :
    TVD (map f p) (map f q) ≤ TVD p q := by
  classical
  rw [TVD_eq_tsum_max, TVD_eq_tsum_max]
  let g := fun a : α ↦ max 0 ((p a).toReal - (q a).toReal)
  have hg_nonneg : ∀ a, 0 ≤ g a := fun a ↦ le_max_left _ _
  have hg_le : ∀ a, g a ≤ (p a).toReal := by
    intro a
    apply max_le
    · exact ENNReal.toReal_nonneg
    · linarith [ENNReal.toReal_nonneg (a := q a)]
  have hg : Summable g :=
    Summable.of_nonneg_of_le hg_nonneg hg_le (PMF.summable_toReal p)
  have hfiber :
      (∑' b : β, ∑' a : (f ⁻¹' {b}), g a) = ∑' a : α, g a :=
    hg.hasSum.tsum_fiberwise f |>.tsum_eq
  have houter : Summable fun b : β ↦ ∑' a : (f ⁻¹' {b}), g a :=
    (hg.hasSum.tsum_fiberwise f).summable
  have hmap_fiber (r : PMF α) (b : β) :
      (map f r b).toReal = ∑' a : (f ⁻¹' {b}), (r a).toReal := by
    rw [map_toReal]
    symm
    rw [tsum_subtype (f ⁻¹' {b}) (fun a ↦ (r a).toReal)]
    apply tsum_congr
    intro a
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    by_cases h : f a = b
    · simp [h]
    · have hb : b ≠ f a := fun hb ↦ h hb.symm
      simp [h, hb]
  have hpoint (b : β) :
      max 0 (((map f p) b).toReal - ((map f q) b).toReal) ≤
        ∑' a : (f ⁻¹' {b}), g a := by
    rw [hmap_fiber p b, hmap_fiber q b]
    have hp : Summable fun a : (f ⁻¹' {b}) ↦ (p a).toReal :=
      (PMF.summable_toReal p).subtype _
    have hq : Summable fun a : (f ⁻¹' {b}) ↦ (q a).toReal :=
      (PMF.summable_toReal q).subtype _
    have hgf : Summable fun a : (f ⁻¹' {b}) ↦ g a :=
      hg.subtype _
    rw [← hp.tsum_sub hq]
    apply max_le
    · apply tsum_nonneg
      intro a
      exact hg_nonneg a
    · exact Summable.tsum_le_tsum
        (fun a ↦ le_max_right 0 ((p a).toReal - (q a).toReal))
        (hp.sub hq) hgf
  apply le_trans ?_ (le_of_eq hfiber)
  apply Summable.tsum_le_tsum hpoint
  · let mp := map f p
    let mq := map f q
    have h_nonneg :
        ∀ b, 0 ≤ max 0 ((mp b).toReal - (mq b).toReal) :=
      fun b ↦ le_max_left _ _
    have h_le :
        ∀ b, max 0 ((mp b).toReal - (mq b).toReal) ≤ (mp b).toReal := by
      intro b
      apply max_le
      · exact ENNReal.toReal_nonneg
      · linarith [ENNReal.toReal_nonneg (a := mq b)]
    exact Summable.of_nonneg_of_le h_nonneg h_le (PMF.summable_toReal mp)
  · exact houter

end
