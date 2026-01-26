/-
Copyright (c) 2026 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import CryptoSecProofs.Probability

/-!
# Hard problems in cyclic groups

We define the following hardness assumptions in a finite cyclic group `G`:

* the discrete logarithm problem
* the Computational Diffie-Hellman (CDH) problem
* the Decisional Diffie-Hellman (DDH) problem
-/

open Group ENNReal PMF

noncomputable section DLog

variable (G : Type) [Group G] [Fintype G] [IsCyclic G] [DecidableEq G]

local notation "#G" => Nat.card G

def dlogAdversary : Type := (Generator G) → G → PMF (ZMod #G)

def dlogGame (adv : dlogAdversary G) : PMF Bool := do
  let g ← uniformGenerator G
  let X ← uniformOfFintype G
  let x ← adv g X
  PMF.pure (if X = g.val ^ x.val then true else false)

def dlogAdvantage (adv : dlogAdversary G) : ℝ :=
  (dlogGame G adv true).toReal

end DLog

noncomputable section CDH

variable (G : Type) [Group G] [Fintype G] [IsCyclic G] [DecidableEq G]

local notation "#G" => Nat.card G

def cdhAdversary : Type := (Generator G) → G → G → PMF G

def cdhGame (adv : cdhAdversary G) : PMF Bool := do
  let g ← uniformGenerator G
  let x ← uniformZMod #G
  let y ← uniformZMod #G
  let Z ← adv g (g.val ^ x.val) (g.val ^ y.val)
  PMF.pure (if Z = g.val ^ (x.val * y.val) then true else false)

def chdAdvantage (adv : cdhAdversary G) : ℝ :=
  (cdhGame G adv true).toReal

end CDH

noncomputable section DDH

variable {G : Type} [Group G] [Fintype G] [IsCyclic G]

local notation "#G" => Nat.card G
local notation "G^3" => G × G × G
local notation "G^4" => G × G × G × G

/-- A quadruplet `(g, X, Y, Z)` is a DDH tuple if there exists
`x` and `y` such that `(X, Y, Z) = (g ^ x, g ^ y, g ^  (x * y))`. -/
def IsDdh (g X Y Z : G) : Prop :=
  ∃ x y : ZMod #G, (X, Y, Z) = (g ^ x.val, g ^ y.val, g ^ (x.val * y.val))

/-- A quadruplet `(g, X, Y, Z)` is a DDH tuple if there exists
`x` and `y` such that `X = g ^ x`, `Y = g ^ y`, and `Z = g ^  (x * y)`. -/
def IsDdh' (g X Y Z : G) : Prop :=
  ∃ x y : ZMod #G, X = g ^ x.val ∧ Y = g ^ y.val ∧ Z = g ^ (x.val * y.val)

omit [Fintype G] [IsCyclic G] in
theorem is_ddh_iff_is_ddh' (g X Y Z : G) : IsDdh g X Y Z ↔ IsDdh' g X Y Z := by
  constructor
  · rw [IsDdh, IsDdh']; simp
  rw [IsDdh, IsDdh']; simp

instance (g X Y Z : G) : Decidable (IsDdh g X Y Z) := by
  exact Classical.propDecidable (IsDdh g X Y Z)

omit [IsCyclic G] in
theorem not_is_ddh_iff (g X Y Z : G) (hg : IsGenerator G g) :
    ¬(IsDdh g X Y Z) ↔ ∃ x y z : ZMod #G,
    X = g ^x.val ∧ Y = g ^ y.val ∧ Z = g ^ z.val ∧ z ≠ x * y := by
  rw [is_ddh_iff_is_ddh']
  simp only [IsDdh']
  contrapose!
  constructor
  · intro h
    rcases h with ⟨x, y, ⟨hx, hy, hz⟩⟩
    rw [hx, hy, hz]
    intro x' y' z' hx' hy' hz'
    apply (exp_bijective g hg).left at hx'
    apply (exp_bijective g hg).left at hy'
    rw [← zpow_val_mul g hg] at hz'
    apply (exp_bijective g hg).left at hz'
    rw [← hz', hx', hy']
  intro h
  obtain ⟨x, hx⟩ := (exp_bijective g hg).right X
  dsimp at hx
  obtain ⟨y, hy⟩ := (exp_bijective g hg).right Y
  dsimp at hy
  obtain ⟨z, hz⟩ := (exp_bijective g hg).right Z
  dsimp at hz
  use x, y
  refine ⟨hx.symm, hy.symm, ?_⟩
  specialize h x y z hx.symm hy.symm hz.symm
  rw [← zpow_val_mul g hg, ← h, hz]

/-- The DDH distribution over `G^3` for some fixed `g : G`
(not necessarily a generator):
it draws two uniformly random scalars `x` and `y` and returns
`(g ^ x, g ^ y, g ^ (x * y))`. -/
def ddhPMF (g : G) : PMF (G^3) := do
  let x ← uniformZMod #G
  let y ← uniformZMod #G
  PMF.pure (g ^ x.val, g ^ y.val, g ^ (x.val * y.val))

/-- The random distribution over `G^3` where for some fixed `g : G`,
it draws three uniformly random scalars `x`, `y`, and `z`
and returns `(g ^ x, g ^ y, g ^ z)`. -/
def ddhRandomPMF (g : G) : PMF (G^3) := do
  let x ← uniformZMod #G
  let y ← uniformZMod #G
  let z ← uniformZMod #G
  PMF.pure (g ^ x.val, g ^ y.val, g ^ z.val)

/-- If `g` is a generator of `G`, then `ddhRandomPMF`
is the uniform distribution over `G^3`. -/
theorem ddhRandomPMF_eq_uniform (g : G) (hg : IsGenerator G g) :
    ddhRandomPMF g = uniformOfFintype G^3 := by
  ext Xs
  simp_rw [ddhRandomPMF, bind_apply', pure_apply, uniform_zmod_prob, uniform_threewise_prob,
    mul_ite, mul_one, mul_zero,
    ENNReal.tsum_mul_left, ← ENNReal.tsum_prod, mul_assoc]
  congr
  /- Rewrite the condition inside the sum as
     `if p = φ Xs` for some function `φ`
     so that we can rely on `tsum_ite_eq` or `Finset.sum_ite_eq'`-/
  let f (xs : ZMod #G × ZMod #G × ZMod #G) : G^3 :=
    (g ^ xs.1.val, g ^ xs.2.1.val, g ^ xs.2.2.val)
  have hf (xs : ZMod #G × ZMod #G × ZMod #G) :
      f xs = (g ^ xs.1.val, g ^ xs.2.1.val, g ^ xs.2.2.val) := rfl
  have f_bij : Function.Bijective f :=
    Function.bijective_nfold 3 (exp_bijective g hg)
  rcases Function.bijective_iff_has_inverse'.mp f_bij with ⟨φ, hφ⟩
  simp_rw [← hf, hφ]
  simp

/-- An adversary for the DDH problem takes a quadruple
`(g, X, Y, Z)` of group elements, where `g` is a generator
of `G` and `(X, Y, Z)` is either a DDH tuple or a uniform
tuple, and returns a bit. -/
def ddhAdversary (G : Type) [Group G] : Type := (Generator G) → G → G → G → PMF Bool

def ddhGame₀ (adv : ddhAdversary G) : PMF Bool := do
  let g ← uniformGenerator G
  let Xs ← ddhPMF g.val
  let (X, Y, Z) := Xs
  let b ← adv g X Y Z
  PMF.pure b

def ddhGame₁ (adv : ddhAdversary G) : PMF Bool := do
  let g ← uniformGenerator G
  let Xs ← ddhRandomPMF g.val
  let (X, Y, Z) := Xs
  let b ← adv g X Y Z
  PMF.pure b

def ddhAdvantage (adv : ddhAdversary G) : ℝ :=
  |(ddhGame₀ adv true).toReal - (ddhGame₁ adv true).toReal|

-- the DDH distribution can be expressed explicitly using `IsDdh`
theorem ddh_dist_ite (g X Y Z : G) (hg : IsGenerator G g) :
    (ddhPMF g) (X, Y, Z) = if IsDdh g X Y Z then (#G : ℝ≥0∞)⁻¹ ^ 2 else 0 := by
  classical
  simp_rw [ddhPMF, bind_apply', pure_apply, uniform_zmod_prob,
    mul_ite, mul_one, mul_zero, ENNReal.tsum_mul_left, ← ENNReal.tsum_prod]
  by_cases h : IsDdh g X Y Z
  · rw [if_pos h]
    rw [IsDdh] at h
    rcases h with ⟨x, y, h⟩
    simp_rw [h]
    have (p : ZMod #G × ZMod #G) :
        (g ^ x.val, g ^ y.val, g ^ (x.val * y.val)) =
          (g ^ p.1.val, g ^ p.2.val, g ^ (p.1.val * p.2.val)) ↔ p = (x, y) := by
      constructor
      · simp only [Prod.mk.injEq, and_imp]
        intro hx hy hxy
        apply (Group.exp_bijective g hg).left at hx
        apply (Group.exp_bijective g hg).left at hy
        rw [hx, hy]
      intro hp
      rw [hp]
    simp_rw [this, tsum_ite_eq]
    group
  rw [if_neg h]
  rw [IsDdh] at h
  push_neg at h
  simp_rw [h]
  simp

/-- Re-randomizing a tuple `(X, Y, Z)` as
`(g ^ u * X, g ^ v * Y ^ w, g ^ (u * v) * X ^ v * Y ^ (u * w) * Z ^ w)`
for `u, v, w` uniformly random. -/
def rerandTuple (g X Y Z : G) : PMF (G^3) := do
  let u ← uniformZMod #G
  let v ← uniformZMod #G
  let w ← uniformZMod #G
  PMF.pure (g ^ u.val * X, g ^ v.val * Y ^ w.val,
    g ^ (u.val * v.val) * X ^ v.val * Y ^ (u.val * w.val) * Z ^ w.val)

/-- Re-randomizing a DDH tuple yields the DDH distribution. -/
lemma rerand_eq_ddhPMF_of_isddh (g X Y Z : G) (hg : IsGenerator G g)
    (h : IsDdh g X Y Z) :
    rerandTuple g X Y Z = ddhPMF g := by
  /- if `(X, Y, Z) = (g ^ x, g ^ y, g ^ (x * y)`
    then the re-randomized triple is
    `(g ^ (u + x), g ^ (v + y * w), g ^ ((u + x) * (v + y * w))` -/
  classical
  ext Xs
  simp_rw [rerandTuple, ddhPMF, bind_apply', pure_apply, uniform_zmod_prob,
    mul_ite, mul_one, mul_zero,
    ENNReal.tsum_mul_left, ← ENNReal.tsum_prod]
  congr
  rw [is_ddh_iff_is_ddh'] at h
  rcases h with ⟨x, y, ⟨hx, hy, hz⟩⟩
  -- rewrite the terms inside the if condition
  conv =>
    lhs
    arg 2
    arg 1
    intro p
    rw [hx, hy, hz]
    rw [← pow_add, ← pow_mul, ← pow_add, ← pow_mul,
      ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add,
      ← add_mul, ← mul_assoc, mul_comm y.val p.1.val,
      mul_assoc, mul_assoc, add_assoc, ← add_mul, ← mul_add]
  -- we defined `f` and `f'` to simplify notation
  let f (q : ZMod #G × ZMod #G) : ℝ≥0∞ :=
    if Xs = (g ^ q.1.val, g ^ q.2.val, g ^ (q.1.val * q.2.val)) then
      (#G : ℝ≥0∞)⁻¹
    else 0
  let f' (p : ZMod #G × ZMod #G × ZMod #G) :=
    (p.1 + x, p.2.1 + y * p.2.2)
  have h (p : ZMod #G × ZMod #G × ZMod #G) : -- p.1 = u, p.2.1 = v, p.2.2 = w
      (if Xs =
        (g ^ (p.1.val + x.val), g ^ (p.2.1.val + y.val * p.2.2.val),
        g ^ ((p.1.val + x.val) * (p.2.1.val + y.val * p.2.2.val))) then
          (#G : ℝ≥0∞)⁻¹
      else 0) = f (f' p) := by
    simp only [f, f']
    rw [← zpow_val_add g hg p.1 x]
    congr 4
    · rw [pow_add, ← zpow_val_mul g hg, ← pow_add, ← zpow_val_add g hg]
    rw [pow_mul, ← zpow_val_add g hg, ← pow_mul,
      mul_comm, pow_mul, pow_add, ← zpow_val_mul g hg,
      ← pow_add, ← zpow_val_add g hg, ← pow_mul, mul_comm]
  -- rewrite the goal using `f` and `f'`
  conv =>
    congr
    · arg 2
      arg 1
      intro p
      rw [h]
    change ∑' (p : ZMod #G × ZMod #G), f p
  clear! h
  -- switch to Finset sum to use `Finset.sum_comp`
  rw [tsum_fintype, Finset.sum_comp]
  simp only [nsmul_eq_mul]
  have hf' (a : ZMod #G ×  ZMod #G) (b : ZMod #G) (q : ZMod #G × ZMod #G) :
      f' (a.1, a.2, b) = q ↔ a = (q.1 - x, q.2 - y * b) := by
    simp only [f']
    constructor <;> aesop
  -- counting the number of tuples `p` such that `f' p = q`
  have hcard (q : ZMod #G × ZMod #G) :
      Finset.card {p : ZMod #G × ZMod #G × ZMod #G | f' p = q} = #G := by
    rw [Finset.card_filter]
    rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
    conv =>
      arg 1
      arg 2
      intro y
      rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    simp_rw [hf', Fintype.sum_ite_eq']
    simp
  simp_rw [hcard]
  rw [← Finset.mul_sum, ← mul_assoc]
  rw [ENNReal.inv_mul_cancel_natCast (by simp), one_mul]
  have f'_surj : Function.Surjective f' := by
    intro q
    use (q.1 - x, q.2, 0)
    simp [f']
  have : Finset.image f' Finset.univ = Finset.univ :=
    Finset.image_univ_of_surjective f'_surj
  simp [this, tsum_fintype]

/-- Re-randomizing a non-DDH tuple yields the uniform distribution. -/
lemma rerand_eq_uniform_of_nonddh (g X Y Z : G) (hg : IsGenerator G g)
    (h : ¬(IsDdh g X Y Z)) :
    rerandTuple g X Y Z = ddhRandomPMF g := by
  /- if `(X, Y, Z) = (g ^ x, g ^ y, g ^ z)`
    then the re-randomized triple is
    `(g ^ (u + x), g ^ (v + y * w), g ^ ((u + x) * v + (y * u + z) * w))` -/
  ext Xs
  simp_rw [rerandTuple, ddhRandomPMF, bind_apply', pure_apply, uniform_zmod_prob,
    mul_ite, mul_one, mul_zero,
    ENNReal.tsum_mul_left, ← ENNReal.tsum_prod]
  congr 2
  rw [not_is_ddh_iff g X Y Z hg] at h
  rcases h with ⟨x, y, z, ⟨hx, hy, hz, hxyz⟩⟩
  -- rewrite the terms inside the if condition
  conv =>
    lhs
    arg 1
    intro p
    rw [hx, hy, hz]
    rw [← pow_add, ← pow_mul, ← pow_add, ← pow_mul,
      ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add,
      ← add_mul, ← mul_assoc, add_assoc, ← add_mul]
  sorry

theorem self_reducible (g X Y Z : G) (hg : IsGenerator G g) :
    rerandTuple g X Y Z = if IsDdh g X Y Z then ddhPMF g else ddhRandomPMF g := by
  by_cases h : IsDdh g X Y Z
  · rw [if_pos h]
    exact rerand_eq_ddhPMF_of_isddh g X Y Z hg h
  rw [if_neg h]
  exact rerand_eq_uniform_of_nonddh g X Y Z hg h

end DDH
