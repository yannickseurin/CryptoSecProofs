# CryptoSecProofs

[![Lean Action CI](https://github.com/yannickseurin/CryptoSecProofs/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/yannickseurin/CryptoSecProofs/actions/workflows/lean_action_ci.yml)
[![Dynamic Regex Badge](https://img.shields.io/badge/dynamic/regex?url=https://raw.githubusercontent.com/yannickseurin/CryptoSecProofs/refs/heads/main/lean-toolchain&search=leanprover/lean4:(.*)&replace=$1&label=Lean4)](https://github.com/leanprover/lean4)

A Lean 4 library for cryptographic security proofs.

## Overview

The files in the main *CryptoSecProofs* folder are organized as follows.

### Root files

- [ToMathlib.lean](CryptoSecProofs/ToMathlib.lean): General lemmas that don't fit anywhere else and could potentially be pushed to Mathlib.
- [Negligible.lean](CryptoSecProofs/Negligible.lean): Some results about negligible functions. It includes the proof of a theorem by Bellare about the equivalence of two definitions of negligibility for a family of functions (namely, Theorem 3.2 from https://eprint.iacr.org/1997/004.pdf).
- [Probability.lean](CryptoSecProofs/Probability.lean): General results about probabilities. For example, we prove that if `f : α → β` is bijective, then drawing `a` uniformly from `α`
and applying `f` yields the uniform distribution on `β`.

### *Hard Problems*

This folder contains files defining hardness assumptions:

- [CyclicGroups.lean](CryptoSecProofs/HardProblems/CyclicGroups.lean): Hard problems in cyclic groups (discrete logarithm, CDH, DDH...).

### *Cryptosystems*

This folder contains files defining various cryptographic primitives and schemes and related security proofs.

#### *PKE*

Public key encryption schemes:

- [Defs.lean](CryptoSecProofs/Cryptosystems/PKE/Defs.lean): Basic definitions about public-key encryption schemes (syntax, correctness, IND-CPA security).
- [ElGamal.lean](CryptoSecProofs/Cryptosystems/PKE/ElGamal.lean): The (basic) ElGamal public-key encryption scheme. We prove correctness and IND-CPA security. Inspired from the [cryptolib](https://github.com/JoeyLupo/cryptolib) library by Joey Lupo (which was written in Lean3).

## Prerequisites

First, you need to [install Lean4](https://lean-lang.org/install/) on your machine.

## Setup

Then, clone this repository and, from the root of the project, run

```bash
lake exe cache get
lake build
```

## Lean resources

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [The Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Formalising Mathematics (by Kevin Buzzard)](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/index.html)
- [The Mechanics of Proof (by Heather Macbeth)](https://hrmacbeth.github.io/math2001/index.html#)
- [An introduction to Lean 4 (by E. Cosme Llópez)](https://www.uv.es/coslloen/Arxiu/Fitxers/An-introduction-to-Lean-4.pdf)
- [Common Lean Pitfalls](https://leanprover-community.github.io/extras/pitfalls.html)
- [Style guidelines](https://leanprover-community.github.io/contribute/style.html)
- [Documentation guidelines](https://leanprover-community.github.io/contribute/doc.html) 
