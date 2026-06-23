/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Reduce
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Basic

/-!
# The Arithmetical Hierarchy

This file defines the arithmetical hierarchy of predicates on `ℕ`.

## Main definitions

* `sigma0 n p` : the predicate `p : ℕ → Prop` is Σ⁰ₙ.
* `pi0 n p`    : the predicate `p : ℕ → Prop` is Π⁰ₙ.
* `delta0 n p` : the predicate `p : ℕ → Prop` is Δ⁰ₙ (i.e. both Σ⁰ₙ and Π⁰ₙ).

## Main results

* `sigma0.zero_iff`, `pi0.zero_iff` : Σ⁰₀ and Π⁰₀ are the primitive recursive predicates.
* `sigma0.one_iff_re`  : Σ⁰₁ = recursively enumerable predicates (`REPred`).
* `pi0.one_iff_co_re`  : Π⁰₁ = co-r.e. predicates.
* `delta0.one_iff_computable` : Δ⁰₁ = computable predicates (`ComputablePred`), i.e. Post's theorem.
-/

open Nat (pair unpair)
open Nat.Partrec.Code (eval evaln evaln_complete evaln_sound ofNatCode)

namespace Computability

end Computability
