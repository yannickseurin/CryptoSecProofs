/-
Copyright (c) 2026 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import Mathlib.Probability.Distributions.Uniform
import CryptoSecProofs.ToMathlib

open ENNReal

namespace PMF

@[simp]
theorem tsum_toReal {α : Type*} (p : PMF α) :
    ∑' a : α, (p a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (apply_ne_top p)]
  simp

@[simp]
theorem sum_toReal {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 := by
  have : ∑' a : α, (p a).toReal = ∑ a : α, (p a).toReal := by
    exact tsum_fintype fun a ↦ (p a).toReal
  rw [← this]
  simp [-tsum_fintype]

open scoped Classical in
theorem ite_ne_top {α : Type*} (p : PMF α) (a : α) (P : Prop) :
    (if P then p a else 0) ≠ ⊤ := by
  have ite_le : (if P then p a else 0) ≤  p a := by
    have : p a = max (p a) 0 := (ENNReal.max_zero_right).symm
    nth_rw 2 [this]
    apply ite_le_sup (p a) 0 P
  have : p a ≠ ⊤ := apply_ne_top p a
  exact ne_top_of_le_ne_top this ite_le

section PMFMonadVariants

universe u

variable {α β γ : Type u}

-- variant of `PMF.pure_bind`
@[simp]
theorem pure_bind' (a : α) (f : α → PMF β) :
    ((pure a) >>= f) = f a := pure_bind a f

-- variant of `PMF.pure_bind`
@[simp]
theorem pure_bind'' (a : α) (f : α → PMF β) :
    (do
      let a' ← pure a
      f a') = f a := pure_bind a f

-- variant of `PMF.bind_pure`
@[simp]
theorem bind_pure' (p : PMF α) :
    p >>= pure = p := bind_pure p

-- variant of `PMF.bind_pure`
@[simp]
theorem bind_pure'' (p : PMF α) :
    (do
      let a ← p
      pure a) = p := bind_pure p

-- variant of `PMF.bind_apply`
@[simp]
theorem bind_apply' (p : PMF α) (f : α → PMF β) (b : β) :
    (p >>= f) b = ∑' (a : α), p a * (f a) b := bind_apply p f b

-- variant of `PMF.bind_bind`
@[simp]
theorem bind_bind' (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (p >>= f) >>= g = p >>= (fun (a : α) ↦ (f a) >>= g) := bind_bind p f g

-- variant of `PMF.bind_bind`
@[simp]
theorem bind_bind'' (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (do
      let b ← (do
        let a ← p
        f a)
      g b) =
    (do
      let a ← p
      let b ← f a
      g b) := bind_bind p f g

theorem bind_comm' (p : PMF α) (q : PMF β) (f : α → β → PMF γ) :
    (p >>= fun a ↦ q >>= f a) = q >>= fun b ↦ p >>= fun a ↦ f a b := bind_comm p q f

theorem bind_comm'' (p : PMF α) (q : PMF β) (f : α → β → PMF γ) :
    (do
      let a ← p
      let b ← q
      f a b) =
    (do
      let b ← q
      let a ← p
      f a b) := bind_comm p q f

theorem mem_support_bind_iff' (p : PMF α) (f : α → PMF β) (b : β) :
    b ∈ (p >>= f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support :=
  mem_support_bind_iff p f b

theorem map_bind' (p : PMF α) (q : α → PMF β) (f : β → γ) :
    map f (p >>= q) = p >>= fun (a : α) ↦ map f (q a) := map_bind p q f

theorem map_bind'' (p : PMF α) (q : α → PMF β) (f : β → γ) :
    map f (do
      let a ← p
      q a) =
    (do
      let a ← p
      map f (q a)) := map_bind p q f

@[simp]
theorem bind_map' (p : PMF α) (f : α → β) (q : β → PMF γ) :
    (map f p) >>= q = p >>= (q ∘ f) := bind_map p f q

@[simp]
theorem bind_map'' (p : PMF α) (f : α → β) (q : β → PMF γ) :
    (do
      let b ← map f p
      q b) =
    (do
      let a ← p
      (q ∘ f) a) := bind_map p f q

end PMFMonadVariants

section PMFMonadNew

universe u

variable {α β : Type u}

theorem bind_skip (p : PMF α) (f g : α → PMF β) :
    (∀ a : α, f a = g a) → p.bind f = p.bind g := by
  intro h
  ext b
  simp only [bind_apply]
  apply tsum_congr
  intro b
  rw [h b]

theorem bind_skip' (p : PMF α) (f g : α → PMF β) :
    (∀ a : α, f a = g a) → (p >>= f) = (p >>= g) := bind_skip p f g

theorem bind_skip'' (p : PMF α) (f g : α → PMF β) :
    (∀ a : α, f a = g a) →
      (do
        let a ← p
        f a) =
      (do
        let a ← p
        g a) := bind_skip p f g

@[simp]
theorem bind_skip_const (pa : PMF α) (pb : PMF β) (f : α → PMF β) :
    (∀ a : α, f a = pb) → pa.bind f = pb := by
  intro h
  ext b
  simp only [bind_apply, h]
  rw [ENNReal.tsum_mul_right]
  rw [tsum_coe pa]
  simp only [one_mul]

@[simp]
lemma bind_skip_const' (pa : PMF α) (pb : PMF β) (f : α → PMF β) :
    (∀ a : α, f a = pb) → (pa >>= f) = pb := bind_skip_const pa pb f

@[simp]
theorem bind_skip_const'' (pa : PMF α) (pb : PMF β) (f : α → PMF β) :
    (∀ a : α, f a = pb) →
      (do
        let a ← pa
        f a) = pb := bind_skip_const pa pb f

@[simp]
theorem map_prod_fst (a : α) (p : PMF β) :
    map Prod.fst (do
      let b ← p
      PMF.pure (a, b)) =
    PMF.pure a := by
  simp [map_bind', pure_map]

@[simp]
theorem map_prod_snd (p : PMF α) (b : β) :
    map Prod.snd (do
      let a ← p
      PMF.pure (a, b)) =
    PMF.pure b := by
  simp [map_bind', pure_map]

theorem apply_eq_zero_of_map_pure_of_ne
    {a : α} {b₀ : β} (p : PMF α) (f : α → β)
    (h : map f p = PMF.pure b₀) (hne : b₀ ≠ f a) :
    p a = 0 := by
  classical
  have : (∑' (a' : α), if f a = f a' then p a' else 0) = 0 := by
    simp only [← (map_apply f p (f a)), h, pure_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    tauto
  simp only [ENNReal.tsum_eq_zero, ite_eq_right_iff] at this
  specialize this a
  tauto

theorem bind_pure_bind
    (p : PMF α) (f : α → β) (g : α → β → PMF γ)
    (h : map f p = PMF.pure b₀) :
    (do
      let a ← p
      let b ← PMF.pure (f a)
      g a b) =
    (do
      let a ← p
      g a b₀) := by
  simp only [pure_bind']
  ext x
  simp only [bind_apply']
  let s : Set α := {a : α | b₀ ≠ f a}
  have h₀ : ∀ a ∈ s, p a * (g a (f a)) x = 0 := by
    intro a
    simp only [Set.mem_setOf_eq, mul_eq_zero, s]
    intro hne
    left
    exact apply_eq_zero_of_map_pure_of_ne p f h hne
  have h₀' : ∀ a ∈ s, p a * (g a b₀) x = 0 := by
    intro a
    simp only [Set.mem_setOf_eq, mul_eq_zero, s]
    intro hne
    left
    exact apply_eq_zero_of_map_pure_of_ne p f h hne
  have h₁ : ∀ a ∈ Set.univ \ s, f a = b₀ := by
    simp [s]
    tauto
  rw [← tsum_univ]
  nth_rw 2 [← tsum_univ]
  rw [tsum_setElem_eq_tsum_setElem_diff Set.univ s h₀,
    tsum_setElem_eq_tsum_setElem_diff Set.univ s h₀']
  simp [h₁]

end PMFMonadNew

noncomputable section TVD

def TVD {α : Type*} [Fintype α] (p q : PMF α) :=
  (∑ a : α, |(p a).toReal - (q a).toReal|) / 2

theorem TVD_self {α : Type*} [Fintype α] (p : PMF α) :
    TVD p p = 0 := by
  simp [TVD]

theorem TVD_comm {α : Type*} [Fintype α] (p q : PMF α) :
    TVD p q = TVD q p := by
  simp [TVD, abs_sub_comm]

theorem TVD_triangle {α : Type*} [Fintype α] (p q r : PMF α) :
    TVD p r ≤ TVD p q + TVD q r := by
  simp only [TVD]
  calc
        (∑ a, |(p a).toReal - (r a).toReal|) / 2
    _ = (∑ a, |(p a).toReal - (q a).toReal + ((q a).toReal - (r a).toReal)|) / 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro a h
      congr
      linarith
    _ ≤ (∑ a, (|(p a).toReal - (q a).toReal| + |(q a).toReal - (r a).toReal|)) / 2 := by
      apply (div_le_div_iff_of_pos_right (by norm_num)).mpr
      apply Finset.sum_le_sum
      intro a ha
      exact abs_add_le ((p a).toReal - (q a).toReal) ((q a).toReal - (r a).toReal)
    _ = (∑ a, |(p a).toReal - (q a).toReal| + ∑ a, |(q a).toReal - (r a).toReal|) / 2 := by
      apply (div_left_inj' (by norm_num)).mpr
      exact Finset.sum_add_distrib
    _ ≤ (∑ a, |(p a).toReal - (q a).toReal|) / 2 + (∑ a, |(q a).toReal - (r a).toReal|) / 2 := by
      linarith
    _ = TVD p q + TVD q r := rfl

lemma TVD_eq_sum_subset_aux {α : Type*} [Fintype α] (p : PMF α) (q : PMF α) :
    ∑ a with ¬(q a).toReal < (p a).toReal, ((q a).toReal - (p a).toReal) =
      ∑ a with (q a).toReal < (p a).toReal, ((p a).toReal - (q a).toReal) := by
  apply eq_of_sub_eq_zero
  repeat rw [Finset.sum_sub_distrib]
  rw [sub_sub_sub_eq]
  repeat rw [Finset.sum_filter_not_add_sum_filter]
  simp

theorem TVD_eq_sum_subset {α : Type*} [Fintype α] (p : PMF α) (q : PMF α) :
    TVD p q = ∑ a with (q a).toReal < (p a).toReal, ((p a).toReal - (q a).toReal) := by
  calc
        TVD p q
    _ = (∑ a : α, |(p a).toReal - (q a).toReal|) / 2 := rfl
    _ = (∑ a with (q a).toReal < (p a).toReal, |(p a).toReal - (q a).toReal| +
          ∑ a with ¬((q a).toReal < (p a).toReal), |(p a).toReal - (q a).toReal|) / 2 := by
      rw [Finset.sum_filter_add_sum_filter_not]
    -- remove the absolute value in the first sum
    _ = (∑ a with (q a).toReal < (p a).toReal, ((p a).toReal - (q a).toReal) +
          ∑ a with ¬((q a).toReal < (p a).toReal), |(p a).toReal - (q a).toReal|) / 2 := by
      congr 2
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have hnonneg : 0 ≤ (p a).toReal - (q a).toReal :=
        sub_nonneg.mpr (le_of_lt ha)
      simp [abs_of_nonneg hnonneg]
    -- remove the absolute value in the second sum
    _ = (∑ a with (q a).toReal < (p a).toReal, ((p a).toReal - (q a).toReal) +
          ∑ a with ¬((q a).toReal < (p a).toReal), ((q a).toReal - (p a).toReal)) / 2 := by
      congr 2
      apply Finset.sum_congr rfl
      intro a ha
      simp only [not_lt, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [abs_sub_comm]
      have hnonneg : 0 ≤ (q a).toReal - (p a).toReal :=
        sub_nonneg.mpr ha
      simp [abs_of_nonneg hnonneg]
    _ = ∑ a with (q a).toReal < (p a).toReal, ((p a).toReal - (q a).toReal) := by
      rw [TVD_eq_sum_subset_aux, add_self_div_two]

theorem TVD_eq_sum_max {α : Type*} [Fintype α] (p : PMF α) (q : PMF α) :
    TVD p q = ∑ a : α, max 0 ((p a).toReal - (q a).toReal) := by
  calc
        TVD p q
    _ = ∑ a with (q a).toReal < (p a).toReal, ((p a).toReal - (q a).toReal) :=
      TVD_eq_sum_subset p q
    _ = ∑ a, if (q a).toReal < (p a).toReal then (p a).toReal - (q a).toReal else 0 :=
      Finset.sum_filter _ _
    _ = ∑ a : α, max 0 ((p a).toReal - (q a).toReal) := by
      simp_rw [max_zero_sub_ite]

theorem TVD_eq_sum_min {α : Type*} [Fintype α] (p : PMF α) (q : PMF α) :
    TVD p q = ∑ a : α, ((p a).toReal - min (p a).toReal (q a).toReal) := by
  calc
        TVD p q
    _ = ∑ a : α, max 0 ((p a).toReal - (q a).toReal) :=
      TVD_eq_sum_max p q
    _ = ∑ a : α, ((p a).toReal - min (p a).toReal (q a).toReal) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact max_zero_sub_eq_sub_min (p a).toReal (q a).toReal

theorem TVD_eq_sum_support_max {α : Type*} [Fintype α] (p : PMF α) (q : PMF α) :
    TVD p q = ∑ a with p a ≠ 0, max 0 ((p a).toReal - (q a).toReal) := by
  calc
        TVD p q
    _ = ∑ a, max 0 ((p a).toReal - (q a).toReal) := TVD_eq_sum_max p q
    _ = ∑ a with p a ≠ 0, max 0 ((p a).toReal - (q a).toReal) +
          ∑ a with p a = 0, max 0 ((p a).toReal - (q a).toReal) := by
      rw [Finset.sum_filter_not_add_sum_filter]
    _ = ∑ a with p a ≠ 0, max 0 ((p a).toReal - (q a).toReal) := by
      apply add_eq_left.mpr
      calc
            ∑ a with p a = 0, max 0 ((p a).toReal - (q a).toReal)
        _ = ∑ a with p a = 0, 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          have : (p a).toReal - (q a).toReal ≤ 0 := by
            rw [sub_le_iff_le_add, zero_add, ha,]
            apply (ENNReal.toReal_le_toReal (zero_ne_top) (apply_ne_top q a)).mpr
            exact zero_le (q a)
          exact max_eq_left_iff.mpr this
        _ = 0 := Finset.sum_const_zero

theorem TVD_eq_sum_support_min {α : Type*} [Fintype α] (p : PMF α) (q : PMF α) :
    TVD p q = ∑ a with p a ≠ 0, ((p a).toReal - min (p a).toReal (q a).toReal) := by
  calc
        TVD p q
    _ = ∑ a with p a ≠ 0, max 0 ((p a).toReal - (q a).toReal) :=
      TVD_eq_sum_support_max p q
    _ = ∑ a with p a ≠ 0, ((p a).toReal - min (p a).toReal (q a).toReal) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact max_zero_sub_eq_sub_min (p a).toReal (q a).toReal

end TVD

noncomputable section UniformDistributions

def uniformZMod (n : ℕ) [NeZero n] : PMF (ZMod n) :=
  uniformOfFintype (ZMod n)

@[simp]
lemma uniform_zmod_prob {n : ℕ} [NeZero n] (a : ZMod n) :
    (uniformZMod n) a = (n : ℝ≥0∞)⁻¹ := by
  simp [uniformZMod]

@[simp]
lemma uniform_threewise_prob {α : Type*} [Fintype α] [Nonempty α] (a : α × α × α) :
    (uniformOfFintype (α × α × α)) a =
      (Nat.card α : ℝ≥0∞)⁻¹ * (Nat.card α : ℝ≥0∞)⁻¹ * (Nat.card α : ℝ≥0∞)⁻¹ := by
  simp only [uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul, Nat.card_eq_fintype_card]
  rw [← Nat.cast_mul, ENNReal.mul_inv_natCast, Nat.cast_mul, ENNReal.mul_inv_natCast, ← mul_assoc]

def uniformCoin : PMF (Bool) := uniformOfFintype Bool

@[simp]
lemma pure_unit : uniformOfFintype Unit = pure () := by
  refine PMF.ext ?_
  simp

lemma sum_bool (p : PMF Bool) :
    p false + p true  = 1 := by
  rw [← tsum_bool, tsum_coe]

lemma sum_bool_real (p : PMF Bool) :
    (p false).toReal + (p true).toReal  = 1 := by
  rw [← (ENNReal.toReal_add (apply_ne_top p false) (apply_ne_top p true))]
  simp [sum_bool]

/-- The uniform probability over the subtype of generators of a group `G`. -/
noncomputable def uniformGenerator (G : Type) [Group G] [Fintype G] [IsCyclic G] :
    PMF (Group.Generator G) :=
  uniformOfFintype (Group.Generator G)

end UniformDistributions

noncomputable section UniformProd

universe u

variable {α β : Type u} [Fintype α] [Nonempty α]
                        [Fintype β] [Nonempty β]


/-- Drawing `a` uniformly from `α` and `b` uniformly from `β`
and forming the pair `(a, b)` yields the uniform distribution
on `α × β`. -/
/-
Note: The process can also be written
`PMF.uniformOfFintype α >>= fun x ↦ PMF.uniformOfFintype β >>= fun y ↦ PMF.pure (x, y)`
-/
lemma uniform_prod :
    (do
       let a ← uniformOfFintype α
       let b ← uniformOfFintype β
       pure (a, b)) = uniformOfFintype (α × β) := by
  classical
  ext p
  let (a, b) := p
  simp only [bind_apply', uniformOfFintype_apply, pure_apply,
    mul_ite, mul_one, mul_zero, Fintype.card_prod, Nat.cast_mul,
    ENNReal.tsum_mul_left, ← ENNReal.tsum_prod, ENNReal.mul_inv_natCast,
    eq_comm, Prod.mk.eta, tsum_ite_eq]

end UniformProd

noncomputable section UniformBij

universe u v

variable {α : Type u} [Fintype α] [Nonempty α]
         {β : Type v} [Fintype β] [Nonempty β]

/-- If `f : α → β` is bijective, then drawing `a` uniformly from `α`
and applying `f` yields the uniform distribution on `β`. -/
/-
Using the monadic structure of PMFs, the process of sampling `a` from
`α` and applying `f` is expressed as `PMF.map f (PMF.uniformOfFintype α)`.
By definition, this is `(PMF.uniformOfFintype α).bind (PMF.pure ∘ f)`
or, using `>>=` notation, `(PMF.uniformOfFintype α) >>= (PMF.pure ∘ f)`.
One can also define it with the `do` notation:
```lean4
def foo : PMF β := do
  let x ← PMF.uniformOfFintype α
  PMF.pure (f x)
```
-/
lemma map_eq_uniform_of_bijective (f : α → β) (hf : Function.Bijective f) :
    map f (uniformOfFintype α) = uniformOfFintype β := by
  classical
  ext b
  simp only [map_apply, uniformOfFintype_apply]
  rw [Fintype.card_of_bijective hf]
  rcases Function.bijective_iff_has_inverse'.mp hf with ⟨g, hg⟩
  simp_rw [hg]
  simp

end UniformBij

section UniformGroup

/-- Applying exponentiation to `x` drawn uniformly at random
from `ZMod #G` yields the uniform distribution on `G`. -/
theorem exp_eq_uniform_group {G : Type*} [Group G] [Fintype G]
    (g : G) (hg : Group.IsGenerator G g) :
    PMF.map (fun x ↦ g ^ x.val) (uniformZMod (Nat.card G)) = uniformOfFintype G := by
  rw [uniformZMod]
  apply map_eq_uniform_of_bijective
  exact Group.exp_bijective g hg

/-- Applying exponentiation to `x` drawn uniformly at random
from `ZMod #G` yields the uniform distribution on `G`. -/
theorem exp_eq_uniform_group' {G : Type} [Group G] [Fintype G]
    (g : G) (hg : Group.IsGenerator G g) :
    (do
      let x ← uniformZMod (Nat.card G)
      PMF.pure (g ^ x.val)
    ) = uniformOfFintype G := exp_eq_uniform_group g hg

/-- Applying exponentiation to `x` drawn uniformly at random
from `ZMod #G` and multiplying by a fixed group element yields
the uniform distribution on `G`. -/
theorem exp_mul_eq_uniform_group {G : Type*} [Group G] [Fintype G]
    (g m : G) (hg : Group.IsGenerator G g) :
    PMF.map (fun x ↦ g ^ x.val * m) (uniformZMod (Nat.card G)) = uniformOfFintype G := by
  rw [uniformZMod]
  apply map_eq_uniform_of_bijective
  exact Group.exp_mul_bijective g m hg

/-- Applying exponentiation to `x` drawn uniformly at random
from `ZMod #G` yields the uniform distribution on `G`. -/
theorem exp_mul_eq_uniform_group' {G : Type} [Group G] [Fintype G]
    (g m : G) (hg : Group.IsGenerator G g) :
    (do
      let x ← uniformZMod (Nat.card G)
      PMF.pure (g ^ x.val * m)
    ) = uniformOfFintype G := exp_mul_eq_uniform_group g m hg

end UniformGroup

end PMF
