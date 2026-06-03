/-
Copyright (c) 2026 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
General lemmas that could be ported to Mathlib, maybe...
-/

/- This instance allows to infer `NeZero (Nat.card G)` when working with a `Fintype` group.
See https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/instance.20synthesis.20failed -/
instance {α : Type u} [Finite α] [Nonempty α] : NeZero (Nat.card α) where
  out := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

lemma two_le_card_of_nontrivial (α : Type) [Fintype α] [Nontrivial α] :
    2 ≤ Fintype.card α := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have : ({a, b} : Finset α).card ≤ Fintype.card α :=
    Finset.card_le_card (by simp)
  simpa [Finset.card_pair, hab] using this

/-- The number of pairs whose left coordinate falls in a given set. -/
lemma card_pairs_with_fst_mem {α β : Type}
    [DecidableEq α] [Fintype α] [Fintype β]
    (s : Finset α) :
    ({ p : α × β | p.1 ∈ s } : Finset (α × β)).card = s.card * Fintype.card β := by
  have hs :
      ({ p : α × β | p.1 ∈ s } : Finset (α × β)) =
        s ×ˢ (Finset.univ : Finset β) := by
    ext p
    simp [Finset.mem_product]
  rw [hs, Finset.card_product, Finset.card_univ]

section Order

lemma max_zero_sub_ite {α : Type*}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (a b : α) :
    max 0 (a - b) = if b < a then a - b else 0 := by
  by_cases h : b < a
  · have : 0 ≤ a - b := sub_nonneg.mpr (le_of_lt h)
    simp [h, max_eq_right this]
  · have : a - b ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
    simp [h, max_eq_left this]

lemma sub_min_ite {α : Type*}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (a b : α) :
     a - min a b = if b < a then a - b else 0 := by
  by_cases h : b < a
  · have : b ≤ a := le_of_lt h
    simp [h, min_eq_right this]
  · have : a ≤ b := not_lt.mp h
    simp [h, min_eq_left this]

lemma max_zero_sub_eq_sub_min {α : Type*}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (a b : α) :
    max 0 (a - b) = a - min a b :=
  Eq.trans (max_zero_sub_ite a b) (sub_min_ite a b).symm

lemma max_zero_add_max_zero_neg_eq_abs {α : Type*}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (x : α) :
    max 0 x + max 0 (-x)  = |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right hx]
    have hnx : -x ≤ 0 := Right.neg_nonpos_iff.mpr hx
    rw [max_eq_left hnx]
    simp
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hx', max_eq_left (le_of_lt hx')]
    have hnx : 0 ≤ -x := by
      apply le_of_lt
      exact Left.neg_pos_iff.mpr hx'
    rw [max_eq_right hnx]
    simp

lemma max_zero_sub_max_zero_neg {α : Type*}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    (x : α) :
    max 0 x - max 0 (-x) = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx]
    have hnx : -x ≤ 0 := Right.neg_nonpos_iff.mpr hx
    rw [max_eq_left hnx]
    simp
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [max_eq_left (le_of_lt hx')]
    have hnx : 0 ≤ -x := by
      apply le_of_lt
      exact Left.neg_pos_iff.mpr hx'
    rw [max_eq_right hnx]
    simp

end Order

section List

lemma List.eraseDups_length_le_aux
    [DecidableEq α] (l : List α) (h : l.length ≤ q) :
    l.eraseDups.length ≤ q := by
  induction q generalizing l with
  | zero =>
    have : l = [] := by
      apply Nat.eq_zero_of_le_zero at h
      apply List.eq_nil_of_length_eq_zero at h
      exact h
    rw [this]
    simp
  | succ q ih =>
    cases l with
    | nil =>
      simp
    | cons a l =>
      simp only [List.eraseDups_cons]
      simp only [List.length_cons, add_le_add_iff_right] at h ⊢
      have : (filter (fun b ↦ !b == a) l).length ≤ q := by
        apply Nat.le_trans _ h
        exact length_filter_le (fun b ↦ !b == a) l
      exact ih _ this

lemma List.eraseDups_length_le
    [DecidableEq α] (l : List α) :
    l.eraseDups.length ≤ l.length := by
  exact List.eraseDups_length_le_aux l (by linarith)

lemma List.dedup_length_le
    [DecidableEq α] (l : List α) :
    l.dedup.length ≤ l.length := by
  simp [List.dedup_sublist, List.Sublist.length_le]

end List

section Vector

/-! There is a `Fintype` instance for `List.Vector`, but not for `Vector`,
so we define one here.
See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.E2.9C.94.20List.2EVector.20-.20could.20we.20just.20remove.20it.3F/near/519375687 -/

variable {α : Type*} {n : ℕ}

def toVector (v : List.Vector α n) : Vector α n := ⟨v.1.toArray, v.2⟩

def ofVector (v : Vector α n) : List.Vector α n := ⟨v.toList, v.2⟩

lemma ofVector_toVector (v : List.Vector α n) : ofVector (toVector v) = v := rfl

lemma toVector_ofVector (v : Vector α n) : toVector (ofVector v) = v := rfl

def equivVector : List.Vector α n ≃ Vector α n where
  toFun := toVector
  invFun := ofVector
  left_inv := ofVector_toVector
  right_inv := toVector_ofVector

instance Vector.fintype' [Fintype α] :
    Fintype (Vector α n) :=
  Fintype.ofEquiv (List.Vector α n) equivVector

instance Vector.measurableSpace [MeasurableSpace α] {n : ℕ} :
    MeasurableSpace (Vector α n) :=
  MeasurableSpace.comap
    (fun v : Vector α n => fun i : Fin n => v[i])
    inferInstance

instance Vector.measurableSingletonClass
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ} :
    MeasurableSingletonClass (Vector α n) := by
  constructor
  intro v
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{fun i : Fin n => v[i]}, measurableSet_singleton _, ?_⟩
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    subst h
    rfl

lemma Vector.ne_iff_exists_getElem_ne
    {α : Type*} {n : ℕ} {u : Vector α n} {v : Vector α n} :
    u ≠ v ↔ ∃ (i : ℕ) (hi : i < n), u[i] ≠ v[i] := by
  constructor
  · intro hne
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    apply Vector.ext
    intro i hi
    exact h i hi
  · intro h
    by_contra heq
    obtain ⟨i, hi, huv⟩ := h
    apply Vector.ext_iff.mp at heq
    specialize heq i hi
    tauto

lemma Vector.toFinset_card_eq_of_mem_eq_iff
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {n : ℕ} {u : Vector α n} {v : Vector β n}
    (h : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), u[i] = u[j] ↔ v[i] = v[j]) :
    u.toList.toFinset.card = v.toList.toFinset.card := by
  let f : Fin n → α := fun i => u[i]
  let g : Fin n → β := fun i => v[i]
  -- Reformulate hypothesis on `Fin` indices
  have h' : ∀ i j : Fin n, f i = f j ↔ g i = g j := by
    simp [f, g, h]
  -- Identify the `Finset`s as images
  have hu :
      u.toList.toFinset = Finset.univ.image f := by
    ext a
    simp [f, Vector.mem_toList_iff, Vector.mem_iff_getElem]
    tauto
  have hv :
      v.toList.toFinset = Finset.univ.image g := by
    ext a
    simp [g, Vector.mem_toList_iff, Vector.mem_iff_getElem]
    tauto
  simp only [hu, hv]
  fapply Finset.card_bij
  · use fun a ha => v[Classical.choose (Finset.mem_image.mp ha)]
  · exact fun a ha => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · intro a₁ ha₁ a₂ ha₂ h_eq
    let i₁ := Classical.choose (Finset.mem_image.mp ha₁)
    let i₂ := Classical.choose (Finset.mem_image.mp ha₂)
    have h₁ := Classical.choose_spec (Finset.mem_image.mp ha₁)
    have h₂ := Classical.choose_spec (Finset.mem_image.mp ha₂)
    specialize h i₁ i₂
    aesop
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.getElem_fin, forall_exists_index,
    forall_apply_eq_imp_iff]
    intro i
    use u[i], ⟨i ,rfl⟩
    have hi := Finset.mem_image_of_mem f (Finset.mem_univ i)
    have := Classical.choose_spec (Finset.mem_image.mp hi)
    aesop

end Vector

section FinsetSum

lemma Finset.sum_union_le_add_of_nonneg
    {ι : Type u} {N : Type v}
    {s₁ s₂ : Finset ι}
    [AddCommGroup N] [PartialOrder N]
    [AddLeftMono N]
    {f : ι → N}
    (hf : ∀ x, 0 ≤ f x)
    [DecidableEq ι] :
    ∑ x ∈ s₁ ∪ s₂, f x ≤
      ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x := by
  have h :=
    Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have hpos : 0 ≤ ∑ x ∈ s₁ ∩ s₂, f x :=
    Finset.sum_nonneg (fun x _ ↦ hf x)
  have h' :
      ∑ x ∈ s₁ ∪ s₂, f x =
        (∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x) -
        ∑ x ∈ s₁ ∩ s₂, f x := by
    symm
    apply sub_eq_of_eq_add
    exact h.symm
  simpa [h'] using
    sub_le_self (∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x) hpos

end FinsetSum

section NatCast

lemma Nat.cast_mul_sub_self_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * (n - 1) := by
  by_cases h : n = 0
  · simp [h]
  · apply mul_nonneg
    · positivity
    · have : 1 ≤ n := by grind
      aesop

lemma Nat.cast_choose_two_nonneg (n : ℕ) : 0 ≤ (n.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  apply div_nonneg
  · apply Nat.cast_mul_sub_self_nonneg
  · positivity

lemma Nat.cast_le_sq (n : ℕ) : (n : ℝ) ≤ n ^ 2 := by
  apply sub_nonneg.mp
  have : (n : ℝ) ^2 - n = (n : ℝ) * (n - 1) := by
    ring
  rw [this]
  exact cast_mul_sub_self_nonneg n

end NatCast

section Bijection

universe u v

/-- The n-fold product of a type. -/
def nfoldProd (α : Type u) : ℕ → Type u
  | 0     => PUnit
  | 1     => α
  | n + 2 => α × nfoldProd α (n + 1)

/-- The application of a function `f` coordinate-wise on an n-tuple. -/
def nfoldMap {α : Type u} {β : Type v} (f : α → β) : (n : ℕ) → nfoldProd α n → nfoldProd β n
  | 0, _       => PUnit.unit
  | 1, x       => f x
  | n + 2, (x, xs) => (f x, nfoldMap f (n + 1) xs)

variable {α : Type u} {β : Type v} {f : α → β}

lemma Function.bijective_iff_has_inverse' :
    Bijective f ↔ ∃ g : β → α, (∀ x : α, ∀ y : β, y = f x ↔ x = g y) := by
  constructor
  · intro f_bij
    rcases Function.bijective_iff_has_inverse.mp f_bij with ⟨g, gli, gri⟩
    use g
    intro x y
    constructor
    · intro h
      rw [eq_comm, h, gli]
    · intro h
      rw [eq_comm, h, gri]
  rintro ⟨g, hg⟩
  apply Function.bijective_iff_has_inverse.mpr
  use g
  constructor
  · intro x
    have : f x = f x ↔ x = g (f x) := hg x (f x)
    tauto
  · intro y
    have : g y = g y ↔ y = f (g y) := iff_comm.mp (hg (g y) y)
    tauto

lemma Function.bijective_nfold (n : ℕ) (hf : Function.Bijective f) :
    Function.Bijective (nfoldMap f n) := by
  apply (Function.bijective_iff_existsUnique (nfoldMap f n)).mpr
  cases n with
    | zero =>
      simp [nfoldProd, nfoldMap]
    | succ n =>
      induction n with
      | zero =>
        exact fun b ↦ Bijective.existsUnique hf b
      | succ n ih =>
        simp only [nfoldProd, nfoldMap, Prod.forall, Prod.mk.injEq] at *
        intro b bs
        specialize ih bs
        have hb : ∃! a, f a = b := Function.Bijective.existsUnique hf b
        simp only [ExistsUnique, and_imp, Prod.forall, Prod.exists, Prod.mk.injEq]
        rcases hb with ⟨a, ha, ha'⟩
        rcases ih with ⟨as, has, has'⟩
        use a, as
        tauto

end Bijection

section ENNReal

namespace ENNReal

lemma mul_natCast {a b : ℕ} : (a : ℝ≥0∞) * (b : ℝ≥0∞) = (↑(a * b) : ℝ≥0∞) := by
  rw [← Nat.cast_mul]

lemma mul_inv_natCast {a b : ℕ} :
    ((a : ℝ≥0∞) * (b : ℝ≥0∞))⁻¹ = (a : ℝ≥0∞)⁻¹ * (b : ℝ≥0∞)⁻¹ := by
  apply ENNReal.mul_inv
  · right
    exact ENNReal.natCast_ne_top b
  · left
    exact ENNReal.natCast_ne_top a

lemma inv_mul_cancel_natCast {a : ℕ} (ha : a ≠ 0) :
     (a : ℝ≥0∞)⁻¹ * (a : ℝ≥0∞) = 1 := by
  apply ENNReal.inv_mul_cancel
  · exact Nat.cast_ne_zero.mpr ha
  · exact natCast_ne_top a

lemma mul_inv_cancel_natCast {a : ℕ} (ha : a ≠ 0) :
     (a : ℝ≥0∞) * (a : ℝ≥0∞)⁻¹  = 1 := by
  apply ENNReal.mul_inv_cancel
  · exact Nat.cast_ne_zero.mpr ha
  · exact natCast_ne_top a

lemma toReal_ite (a b : ℝ≥0∞) (P : Prop) [Decidable P] :
    (if P then a else b).toReal = if P then a.toReal else b.toReal := by
  exact apply_ite ENNReal.toReal P a b

end ENNReal

end ENNReal

section Group

instance {G : Type*} [Group G] [IsCyclic G] : CommGroup G := IsCyclic.commGroup

namespace Group

def IsGenerator (G : Type*) [Group G] (g : G) :=
  ∀ x : G, x ∈ Subgroup.zpowers g

/-- The subtype of generators of a group `G`.
We make it a subtype because, when drawing a random generator
`g` of `G`, we want to have access to a proof that it is a
generator (something we would not have with a Finset).
Note: if `g : generator G`, then `g` is actually a pair
`(g.val, g.property)` where `g.val : G` and `g.property` is a
proof that `g.val` is a generator of `G`. -/
def Generator (G : Type*) [Group G] :=
  { g : G // IsGenerator G g }

noncomputable instance (G : Type*) [Group G] [IsCyclic G] [Fintype G] :
    Fintype (Generator G) :=
  Subtype.fintype fun x ↦ ∀ y : G, y ∈ Subgroup.zpowers x

instance (G : Type*) [Group G] [IsCyclic G] :
    Nonempty (Generator G) := by
  simp only [Generator, IsGenerator, nonempty_subtype]
  exact IsCyclic.exists_zpow_surjective

lemma g_order {G : Type*} [Group G] (g : G) (hg : IsGenerator G g) :
    orderOf g = Nat.card G :=
  orderOf_eq_card_of_forall_mem_zpowers hg

lemma zpow_val_add {G : Type*} [Group G] [Finite G]
    (g : G) (hg : IsGenerator G g)
    (a b : ZMod (Nat.card G)) :
    g ^ (a + b).val = g ^ (a.val + b.val) := by
  apply pow_eq_pow_iff_modEq.mpr
  rw [g_order g hg]
  unfold Nat.ModEq
  have : (a + b).val % (Nat.card G) = (a + b).val :=
    Nat.mod_eq_of_lt (ZMod.val_lt (a + b))
  rw [this]
  exact ZMod.val_add a b

lemma zpow_val_mul {G : Type*} [Group G] [Finite G]
    (g : G) (hg : IsGenerator G g)
    (a b : ZMod (Nat.card G)) :
    g ^ (a * b).val = g ^ (a.val * b.val) := by
  apply pow_eq_pow_iff_modEq.mpr
  rw [g_order g hg]
  unfold Nat.ModEq
  have : (a * b).val % (Nat.card G) = (a * b).val :=
    Nat.mod_eq_of_lt (ZMod.val_lt (a * b))
  rw [this]
  exact ZMod.val_mul a b

/-- In a cyclic group, exponentiation is bijective. -/
lemma exp_bijective {G : Type*} [Group G] [Finite G]
    (g : G) (hg : IsGenerator G g) :
    Function.Bijective fun (x : ZMod (Nat.card G)) ↦ g ^ x.val := by
  constructor
  · intro a₁ a₂ h
    rw [← ZMod.natCast_zmod_val a₁, ← ZMod.natCast_zmod_val a₂, ZMod.natCast_eq_natCast_iff]
    have : a₁.val ≡ a₂.val [MOD orderOf g] := pow_eq_pow_iff_modEq.mp h
    rw [g_order g hg] at this
    exact this
  · intro b
    rcases hg b with ⟨z, rfl⟩
    dsimp
    use (z : ZMod (Nat.card G))
    rw [← zpow_natCast g (z : ZMod (Nat.card G)).val, ZMod.val_intCast z]
    rw [← zpow_mod_orderOf g z, g_order g hg]

/-- In a cyclic group, exponentiation followed by multiplication by
a fixed group element is bijective. -/
lemma exp_mul_bijective {G : Type*} [Group G] [Finite G]
    (g m : G) (hg : IsGenerator G g) :
    Function.Bijective fun (x : ZMod (Nat.card G)) ↦ g ^ x.val * m := by
  change Function.Bijective ((fun (a : G) ↦ a * m) ∘ (fun (x : ZMod (Nat.card G)) ↦ g ^ x.val))
  apply Function.Bijective.comp
  · exact mulRight_bijective m
  · exact exp_bijective g hg

end Group

end Group
