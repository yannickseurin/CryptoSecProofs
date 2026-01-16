/-
Copyright (c) 2026 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import Mathlib.Probability.Distributions.Uniform
import CryptoSecProofs.ToMathlib

open ENNReal

namespace PMF

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

open scoped Classical in
theorem apply_eq_zero_of_map_pure_of_ne
    {a : α} {b₀ : β} (p : PMF α) (f : α → β)
    (h : map f p = PMF.pure b₀) (hne : b₀ ≠ f a) :
    p a = 0 := by
  have : (∑' (a' : α), if f a = f a' then p a' else 0) = 0 := by
    simp [← (map_apply f p (f a)), h]
    tauto
  simp only [ENNReal.tsum_eq_zero, ite_eq_right_iff] at this
  specialize this a
  tauto

open scoped Classical in
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

open scoped Classical in
theorem ite_ne_top {α : Type*} (p : PMF α) (a : α) (P : Prop) :
    (if P then p a else 0) ≠ ⊤ := by
  have ite_le : (if P then p a else 0) ≤  p a := by
    have : p a = max (p a) 0 := (ENNReal.max_zero_right).symm
    nth_rw 2 [this]
    apply ite_le_sup (p a) 0 P
  have : p a ≠ ⊤ := apply_ne_top p a
  exact ne_top_of_le_ne_top this ite_le

end PMFMonadNew

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


open scoped Classical in
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

open scoped Classical in
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
