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

variable {n m : ℕ} {p : ℕ → Prop} {f : ℕ → ℕ}

mutual

/-- `sigma0 n p` states that the predicate `p : ℕ → Prop` is Σ⁰ₙ.

* Level 0 consists of the primitive recursive predicates.
* Level `n+1` predicates are existential projections of `pi0 n` predicates.
-/
def sigma0 : ℕ → (ℕ → Prop) → Prop
  | 0,     p => PrimrecPred p
  | n + 1, p => ∃ q : ℕ → Prop, pi0 n q ∧ p = fun x => ∃ y, q (pair x y)

/-- `pi0 n p` states that the predicate `p : ℕ → Prop` is Π⁰ₙ.

* Level 0 consists of the primitive recursive predicates.
* Level `n+1` predicates are universal projections of `sigma0 n` predicates.
-/
def pi0 : ℕ → (ℕ → Prop) → Prop
  | 0,     p => PrimrecPred p
  | n + 1, p => ∃ q : ℕ → Prop, sigma0 n q ∧ p = fun x => ∀ y, q (pair x y)

end

/-- `delta0 n p` states that the predicate `p : ℕ → Prop` is Δ⁰ₙ,
i.e., both Σ⁰ₙ and Π⁰ₙ. -/
def delta0 (n : ℕ) (p : ℕ → Prop) : Prop := sigma0 n p ∧ pi0 n p


/-! ### Unfolding lemmas -/

@[simp]
theorem sigma0.zero_eq (p : ℕ → Prop) : sigma0 0 p = PrimrecPred p := rfl

@[simp]
theorem sigma0.succ_eq (n : ℕ) (p : ℕ → Prop) :
    sigma0 (n + 1) p = ∃ q : ℕ → Prop, pi0 n q ∧ p = fun x => ∃ y, q (pair x y) := rfl

@[simp]
theorem pi0.zero_eq (p : ℕ → Prop) : pi0 0 p = PrimrecPred p := rfl

@[simp]
theorem pi0.succ_eq (n : ℕ) (p : ℕ → Prop) :
    pi0 (n + 1) p = ∃ q : ℕ → Prop, sigma0 n q ∧ p = fun x => ∀ y, q (pair x y) := rfl


/-! ### Level 0 is exactly `PrimrecPred` -/

/-- A predicate is Σ⁰₀ iff it is primitive recursive. -/
theorem sigma0.zero_iff : sigma0 0 p ↔ PrimrecPred p := by rfl

/-- A predicate is Π⁰₀ iff it is primitive recursive. -/
theorem pi0.zero_iff : pi0 0 p ↔ PrimrecPred p := by rfl

/-- A predicate is Δ⁰₀ iff it is primitive recursive. -/
theorem delta0.zero_iff : delta0 0 p ↔ PrimrecPred p := by
  simp [delta0]


/-! ### Basic properties -/

private theorem mono_aux :
    (∀ p : ℕ → Prop, sigma0 n p → sigma0 (n + 1) p) ∧
    (∀ p : ℕ → Prop, pi0 n p → pi0 (n + 1) p) := by
  induction n with
  | zero =>
    simp only [sigma0.zero_eq, zero_add, sigma0.succ_eq, pi0.zero_eq, pi0.succ_eq]
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · refine ⟨fun z => p z.unpair.1, ?_⟩
      simp only [Nat.unpair_pair, exists_const, and_true]
      exact PrimrecPred.comp hp (Primrec.fst.comp Primrec.unpair)
    · refine ⟨fun z => p z.unpair.1, ?_⟩
      simp only [Nat.unpair_pair, forall_const, and_true]
      exact PrimrecPred.comp hp (Primrec.fst.comp Primrec.unpair)
  | succ n ih =>
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨q, ih.2 q hq, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨q, ih.1 q hq, rfl⟩

theorem sigma0.mono (h : sigma0 n p) : sigma0 (n + 1) p :=
  mono_aux.1 p h

theorem pi0.mono (h : pi0 n p) : pi0 (n + 1) p :=
  mono_aux.2 p h

theorem sigma0.mono_le (hnm : n ≤ m) (h : sigma0 n p) :
    sigma0 m p := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact ih.mono

theorem pi0.mono_le (hnm : n ≤ m) (h : pi0 n p) :
    pi0 m p := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact ih.mono

theorem sigma0.of_primrec (h : PrimrecPred p) : sigma0 n p := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.mono

theorem pi0.of_primrec (h : PrimrecPred p) : pi0 n p := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.mono

private theorem neg_aux :
    (∀ p : ℕ → Prop, sigma0 n p → pi0 n (fun x => ¬ p x)) ∧
    (∀ p : ℕ → Prop, pi0 n p → sigma0 n (fun x => ¬ p x)) := by
  induction n with
  | zero =>
    exact ⟨fun p hp => PrimrecPred.not hp, fun p hp => PrimrecPred.not hp⟩
  | succ n ih =>
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun z => ¬ q z, ih.2 q hq, ?_⟩
      funext x
      simp
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun z => ¬ q z, ih.1 q hq, ?_⟩
      funext x
      simp

theorem pi0.iff_not_sigma0 : pi0 n p ↔ sigma0 n (fun x => ¬ p x) := by
  constructor
  · intro h
    exact neg_aux.2 p h
  · intro h
    have := neg_aux.1 _ h
    simp_all

theorem sigma0.iff_not_pi0 : sigma0 n p ↔ pi0 n (fun x => ¬ p x) := by
  constructor
  · intro h
    exact neg_aux.1 p h
  · intro h
    have := neg_aux.2 _ h
    simp_all

private theorem comp_aux :
    (∀ (p : ℕ → Prop) (f : ℕ → ℕ), sigma0 n p → Primrec f → sigma0 n (fun x => p (f x))) ∧
    (∀ (p : ℕ → Prop) (f : ℕ → ℕ), pi0 n p → Primrec f → pi0 n (fun x => p (f x))) := by
  induction n with
  | zero =>
    exact ⟨fun p f hp hf => PrimrecPred.comp hp hf,
           fun p f hp hf => PrimrecPred.comp hp hf⟩
  | succ n ih =>
    have h_unpack : ∀ f : ℕ → ℕ, Primrec f →
        Primrec (fun z : ℕ => pair (f z.unpair.1) z.unpair.2) := fun f hf =>
      Primrec₂.natPair.comp (hf.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.snd.comp Primrec.unpair)
    refine ⟨fun p f hp hf => ?_, fun p f hp hf => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun z => q (pair (f z.unpair.1) z.unpair.2), ?_, ?_⟩
      · exact ih.2 q _ hq (h_unpack f hf)
      · funext x
        simp
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun z => q (pair (f z.unpair.1) z.unpair.2), ?_, ?_⟩
      · exact ih.1 q _ hq (h_unpack f hf)
      · funext x
        simp

theorem sigma0.comp_primrec (hp : sigma0 n p) (hf : Primrec f) : sigma0 n (fun x => p (f x)) :=
  comp_aux.1 p f hp hf

theorem pi0.comp_primrec (hp : pi0 n p) (hf : Primrec f) : pi0 n (fun x => p (f x)) :=
  comp_aux.2 p f hp hf

theorem sigma0.of_pi0_succ (h : pi0 n p) : sigma0 (n + 1) p := by
  refine ⟨fun z => p z.unpair.1, pi0.comp_primrec h (Primrec.fst.comp Primrec.unpair), ?_⟩
  funext x
  simp

theorem pi0.of_sigma0_succ (h : sigma0 n p) : pi0 (n + 1) p := by
  refine ⟨fun z => p z.unpair.1, sigma0.comp_primrec h (Primrec.fst.comp Primrec.unpair), ?_⟩
  funext x
  simp

private theorem bool_aux :
    (∀ p q : ℕ → Prop, sigma0 n p → sigma0 n q → sigma0 n (fun x => p x ∧ q x)) ∧
    (∀ p q : ℕ → Prop, sigma0 n p → sigma0 n q → sigma0 n (fun x => p x ∨ q x)) ∧
    (∀ p q : ℕ → Prop, pi0 n p → pi0 n q → pi0 n (fun x => p x ∧ q x)) ∧
    (∀ p q : ℕ → Prop, pi0 n p → pi0 n q → pi0 n (fun x => p x ∨ q x)) := by
  induction n with
  | zero =>
    refine ⟨fun p q hp hq => ?_,
            fun p q hp hq => ?_,
            fun p q hp hq => ?_,
            fun p q hp hq => ?_⟩
    · exact PrimrecPred.and hp hq
    · exact PrimrecPred.or hp hq
    · exact PrimrecPred.and hp hq
    · exact PrimrecPred.or hp hq
  | succ n ih =>
    obtain ⟨ihSigmaAnd, ihSigmaOr, ihPiAnd, ihPiOr⟩ := ih
    -- g₁ ⟨x,⟨y₁,y₂⟩⟩ = ⟨x,y₁⟩
    have g₁ : Primrec (fun z : ℕ => pair z.unpair.1 z.unpair.2.unpair.1) :=
      Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    -- g₁ ⟨x,⟨y₁,y₂⟩⟩ = ⟨x,y₂⟩
    have g₂ : Primrec (fun z : ℕ => pair z.unpair.1 z.unpair.2.unpair.2) :=
      Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- sigma0 n conjunction
      rintro p q ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
      refine ⟨fun z => q₁ (pair z.unpair.1 z.unpair.2.unpair.1) ∧
        q₂ (pair z.unpair.1 z.unpair.2.unpair.2), ?_, ?_⟩
      · exact ihPiAnd _ _ (pi0.comp_primrec hq₁ g₁) (pi0.comp_primrec hq₂ g₂)
      · funext x
        apply propext
        constructor
        · rintro ⟨⟨y₁, h₁⟩, ⟨y₂, h₂⟩⟩
          refine ⟨pair y₁ y₂, ?_⟩
          simp_all
        · rintro ⟨y, hy⟩
          simp_all only [Nat.unpair_pair]
          exact ⟨⟨y.unpair.1, hy.1⟩, ⟨y.unpair.2, hy.2⟩⟩
    · -- sigma0 n disjunction
      rintro p q ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
      refine ⟨fun z => q₁ z ∨ q₂ z, ihPiOr _ _ hq₁ hq₂, ?_⟩
      funext x
      simp [exists_or]
    · -- pi0 n conjunction
      rintro p q ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
      refine ⟨fun z => q₁ z ∧ q₂ z, ihSigmaAnd _ _ hq₁ hq₂, ?_⟩
      funext x
      simp [forall_and]
    · -- pi0 n disjunction
      rintro p q ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
      refine ⟨fun z => q₁ (pair z.unpair.1 z.unpair.2.unpair.1) ∨
          q₂ (pair z.unpair.1 z.unpair.2.unpair.2), ?_, ?_⟩
      · exact ihSigmaOr _ _ (sigma0.comp_primrec hq₁ g₁) (sigma0.comp_primrec hq₂ g₂)
      · funext x
        apply propext
        constructor
        · rintro (_ | _) _ <;> simp_all [Nat.unpair_pair]
        · intro h
          by_contra hc
          simp_all only [not_or, not_forall]
          obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
          have hv := h (pair a b)
          simp_all

theorem sigma0.and (hp : sigma0 n p) (hq : sigma0 n q) : sigma0 n (fun x => p x ∧ q x) :=
  bool_aux.1 p q hp hq

theorem sigma0.or (hp : sigma0 n p) (hq : sigma0 n q) : sigma0 n (fun x => p x ∨ q x) :=
  bool_aux.2.1 p q hp hq

theorem pi0.and (hp : pi0 n p) (hq : pi0 n q) : pi0 n (fun x => p x ∧ q x) :=
  bool_aux.2.2.1 p q hp hq

theorem pi0.or (hp : pi0 n p) (hq : pi0 n q) : pi0 n (fun x => p x ∨ q x) :=
  bool_aux.2.2.2 p q hp hq

end Computability
