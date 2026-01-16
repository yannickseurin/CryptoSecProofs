/-
Copyright (c) 2026 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import CryptoSecProofs.HardProblems.CyclicGroups
import CryptoSecProofs.Cryptosystems.PKE.Defs

/-!
The ElGamal public key encryption scheme.
-/

open Group PMF

noncomputable section

variable (G : Type) [Group G] [Fintype G] [IsCyclic G] [DecidableEq G]

local notation "#G" => Nat.card G

/-- The ElGamal public key encryption scheme.
It is parameterized by a finite cyclic group `G`.
The following structure fields are inferred:
* public parameters space: `Generator G`
* secret key space: `ZMod #G`
* public key space: `G`
* message space: `G`
* ciphertext space: `G × G`
The algorithms are defined as follows:
* `setup` draws a uniformly random generator `g` of `G` (given as input
to all other three algorithms)
* `keygen` generates a uniformly random secret key `x : ZMod #G`
and the corresponding public key `g ^ x.val`
* `encrypt` takes a public key `pk` and a message `m`, draws a
uniformly random nonce `r : ZMod #G`, and outputs the ciphertext
`c = (g ^ r, pk ^ r * m)`
* `decrypt` takes a secret key `x` and a ciphertext `c = (c.1, c.2)` and
outputs `c.2 * (c.1 ^ x)⁻¹` -/
@[simps]
def elgamal : PKE where
  -- P := G
  -- SK := ZMod #G
  -- PK := G
  -- M := G
  -- C := G × G
  setup := uniformGenerator G
  keygen g := do
    let x ← uniformZMod #G
    PMF.pure (x, g.val ^ x.val)
  encrypt (g : Generator G) (pk m : G) := do
    let r ← uniformZMod #G
    PMF.pure ((g.val ^ r.val, pk ^ r.val * m))
  decrypt (_ : Generator G) (x : ZMod #G) (c : G × G) :=
    some (c.2 * (c.1 ^ x.val)⁻¹)

end

namespace elgamal

noncomputable section Correctness

variable (G : Type) [Group G] [Fintype G] [IsCyclic G] [DecidableEq G]

local notation "#G" => Nat.card G

lemma enc_dec (g : Generator G) (m : G) (x r : ZMod #G) :
    (elgamal G).decrypt g x ((g.val ^ r.val, (g.val ^ x.val) ^ r.val * m)) = some m := by
  simp only [elgamal]
  congr
  rw [← pow_mul, ← pow_mul, mul_comm r.val x.val]
  exact mul_inv_cancel_comm (g.val ^ (x.val * r.val)) m

theorem perfectly_correct : (elgamal G).PerfectlyCorrect := by
  simp [-elgamal_decrypt, PKE.PerfectlyCorrect, PKE.correctnessGame, enc_dec]

end Correctness

noncomputable section IND_CPA_Proof

variable {G : Type} [Group G] [Fintype G] [IsCyclic G] [DecidableEq G]
         (adv : (elgamal G).indCpaAdversary)

local notation "#G" => Nat.card G

def ddhReduc (g : Generator G) (X Y Z : G) : PMF Bool := do
  let (m₀, m₁, st) ← adv.A₁ g X
  let b ← uniformCoin
  let mb : G := if b then m₁ else m₀
  let b' ← adv.A₂ (Y, Z * mb) st
  PMF.pure (if b = b' then true else false)

lemma ind_cpa_to_dddh₀ : PKE.indCpaGame adv = ddhGame₀ (ddhReduc adv) := by
  simp only [PKE.indCpaGame, ddhGame₀, ddhReduc, elgamal_setup,
    elgamal_keygen, elgamal_encrypt, ddhPMF]
  apply bind_skip'
  intro (g : Generator G)
  simp_rw [bind_bind', pure_bind']
  apply bind_skip'
  intro x
  nth_rw 2 [bind_comm']
  apply bind_skip'
  intro (m₀, m₁, st)
  dsimp
  rw [bind_comm']
  apply bind_skip'
  intro y
  apply bind_skip'
  intro b
  simp [pow_mul]

def Game₁ : PMF Bool := do
  let g ← uniformGenerator G
  let x ← uniformZMod #G
  let y ← uniformZMod #G
  let z ← uniformZMod #G
  let (m₀, m₁, st) ← adv.A₁ g (g.val ^ x.val)
  let b ← uniformCoin
  let mb : G := if b then m₁ else m₀
  let b' ← adv.A₂ (g.val ^ y.val, (g.val ^ z.val) * mb) st
  PMF.pure (if b = b' then true else false)

def Game₂ : PMF Bool := do
  let g ← uniformGenerator G
  let x ← uniformZMod #G
  let y ← uniformZMod #G
  let z ← uniformZMod #G
  let (m₀, m₁, st) ← adv.A₁ g (g.val ^ x.val)
  let b ← uniformCoin
  let _ : G := if b then m₁ else m₀
  let b' ← adv.A₂ (g.val ^ y.val, g.val ^ z.val) st
  PMF.pure (if b = b' then true else false)

lemma game₁_to_ddh₁ : Game₁ adv = ddhGame₁ (ddhReduc adv) := by
  simp only [Game₁, ddhGame₁, ddhReduc, ddhRandomPMF]
  simp_rw [bind_bind', pure_bind']

omit [DecidableEq G] in
lemma rewrite_lemma {α : Type} (g mb : G) (p : G → PMF α) :
    (do
      let m ← (do
        let z ← uniformZMod #G
        PMF.pure (g ^ z.val * mb))
      p m) =
    (do
      let z ← uniformZMod #G
      p (g ^ z.val * mb)) := by
  simp

omit [DecidableEq G] in
lemma rewrite_lemma' {α : Type} (g : G) (p : G → PMF α) :
    (do
      let m ← (do
        let z ← uniformZMod #G
        PMF.pure (g ^ z.val))
      p m) =
    (do
      let z ← uniformZMod #G
      p (g ^ z.val)) := by
  simp

lemma game₁_to_game₂ : Game₁ adv = Game₂ adv := by
  simp only [Game₁, Game₂]
  apply bind_skip'
  intro g
  apply bind_skip'
  intro x
  apply bind_skip'
  intro y
  rw [bind_comm']
  nth_rw 2 [bind_comm']
  apply bind_skip'
  intro (m₀, m₁, st)
  dsimp
  rw [bind_comm']
  nth_rw 2 [bind_comm']
  apply bind_skip'
  intro b
  let mb : G := if b then m₁ else m₀
  have : mb = if b then m₁ else m₀ := rfl
  rw [← this]
  let p (m : G) := do
    let b' ← adv.A₂ (g.val ^ y.val, m) st
    PMF.pure (if b = b' then true else false)
  change
    (do
      let z ← uniformZMod #G
      p (g.val ^ z.val * mb)) =
    (do
      let z ← uniformZMod #G
      p (g.val ^ z.val))
  rw [← rewrite_lemma, exp_mul_eq_uniform_group' g.val mb g.property]
  rw [← rewrite_lemma', exp_eq_uniform_group' g.val g.property]

lemma game₂_uniform : Game₂ adv = uniformOfFintype Bool := by
  simp only [Game₂]
  apply bind_skip_const'
  intro g
  apply bind_skip_const'
  intro x
  apply bind_skip_const'
  intro y
  apply bind_skip_const'
  intro z
  apply bind_skip_const'
  intro (m₀, m₁, st)
  dsimp
  rw [bind_comm']
  apply bind_skip_const'
  intro b
  simp only [uniformCoin]
  ext b'
  simp_rw [bind_apply', pure_apply, uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
    mul_ite, mul_one, mul_zero, tsum_bool]
  cases b <;> cases b' <;> simp

theorem ind_cpa : PKE.indCpaAdvantage adv = ddhAdvantage (ddhReduc adv) := by
  simp only [PKE.indCpaAdvantage, ddhAdvantage]
  congr
  · exact ind_cpa_to_dddh₀ adv
  rw [← game₁_to_ddh₁, game₁_to_game₂, game₂_uniform]
  simp

end IND_CPA_Proof

end elgamal
