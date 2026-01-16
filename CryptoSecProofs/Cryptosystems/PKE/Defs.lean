/-
Copyright (c) 2026 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import CryptoSecProofs.Probability

/-!
# Public-Key Encryption Schemes

This file gives definitions for PKE schemes.
-/

/-- A public key encryption (PKE) scheme.
We model randomized algorithm as PMFs over their return type. -/
structure PKE where
  /-- public parameters -/
  {P : Type*}
  /-- secret keys -/
  {SK : Type*}
  /-- public keys -/
  {PK : Type*}
  /-- messages -/
  {M : Type*}
  [dem : DecidableEq M]
  /-- ciphertexts -/
  {C : Type*}
  /-- `setup` takes no input and returns
  public parameters `par` (randomized) -/
  setup : PMF P
  /-- `keygen` takes public parameters `par` and generates a
  secret public key pair `(sk, pk)` (randomized) -/
  keygen : P → PMF (SK × PK)
  /-- `encrypt` takes public parameters `par`, a public key `pk`,
  and a message `m` and returns a ciphertext `c` (randomized) -/
  encrypt : P → PK → M → PMF C
  /-- `decrypt` takes public parameters `par`, a secret key `sk`,
  and a ciphertext `c`, and returns a message `m` or `⊥` indicating
  decryption failure -/
  decrypt : P → SK → C → Option M

attribute [instance] PKE.dem

namespace PKE

/-- The correctness experiment.
Executes the public-key scheme by encrypting and decrypting some message `m`
and returns `true` if the ciphertexts decrypts to `m` and `false` otherwise. -/
noncomputable def correctnessGame (pke : PKE) (m : pke.M) : PMF Bool := do
  let par ← pke.setup
  let (sk, pk) ← pke.keygen par
  let c ← pke.encrypt par pk m
  PMF.pure (if pke.decrypt par sk c = some m then true else false)

/-- A public-key encryption scheme is (perfectly) correct if for every
message `m`, decrypting the encryption of `m` returns `m` with probability 1. -/
def PerfectlyCorrect (pke : PKE) : Prop :=
  ∀ (m : pke.M), pke.correctnessGame m = PMF.pure true

/-- An IND-CPA adversary against a PKE. -/
structure indCpaAdversary (pke : PKE) where
  /-- state passed from `A₁` to `A₂` -/
  A_state : Type*
  /-- First stage: takes public parameters `par`, a public key `pk`,
  and outputs two messages `m₀` and `m₁` and a state. -/
  A₁ : pke.P → pke.PK → PMF (pke.M × pke.M × A_state)
  /-- Second stage: takes a ciphertext `c` (of either `m₀` or `m₁`)
  and a state passed from `A₁` and returns a bit. -/
  A₂ : pke.C → A_state → PMF Bool

/-- The IND-CPA (semantic security) game.
Returns `true` if the adversary `A₂` guesses the correct bit. -/
noncomputable def indCpaGame {pke : PKE} (adv : pke.indCpaAdversary) : PMF Bool := do
  let par ← pke.setup
  let (_, pk) ← pke.keygen par
  let (m₀, m₁, st) ← adv.A₁ par pk
  let b ← PMF.uniformCoin
  let c ← pke.encrypt par pk (if b then m₁ else m₀)
  let b' ← adv.A₂ c st
  PMF.pure (if b = b' then true else false)

/-- The advantage of an IND-CPA adversary against a PKE scheme. -/
noncomputable def indCpaAdvantage {pke : PKE} (adv : pke.indCpaAdversary) : ℝ :=
  |(indCpaGame adv true).toReal - 1 / 2|

end PKE
