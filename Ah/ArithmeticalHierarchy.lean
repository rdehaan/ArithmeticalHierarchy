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
-- open Nat.Partrec.Code (eval evaln evaln_complete evaln_sound ofNatCode)

namespace Computability

variable {n m : ℕ} {p q : ℕ → Prop} {f b : ℕ → ℕ} {R S : ℕ → ℕ → Prop}

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


/-! Unfolding lemmas -/

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


/-! ## Basic properties -/

/-! Level 0 coincides with `PrimrecPred` -/

theorem sigma0.zero_iff : sigma0 0 p ↔ PrimrecPred p := by rfl

theorem pi0.zero_iff : pi0 0 p ↔ PrimrecPred p := by rfl

theorem delta0.zero_iff : delta0 0 p ↔ PrimrecPred p := by simp [delta0]

/-! Monotonicity properties -/

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


/-! Closure under primitive recursion -/

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


/-! Trivial (crossing) inclusions -/

theorem sigma0.of_pi0_succ (h : pi0 n p) : sigma0 (n + 1) p := by
  refine ⟨fun z => p z.unpair.1, pi0.comp_primrec h (Primrec.fst.comp Primrec.unpair), ?_⟩
  funext x
  simp

theorem pi0.of_sigma0_succ (h : sigma0 n p) : pi0 (n + 1) p := by
  refine ⟨fun z => p z.unpair.1, sigma0.comp_primrec h (Primrec.fst.comp Primrec.unpair), ?_⟩
  funext x
  simp


/-! ## Helpers -/

/-! Primitive recursive helpers -/

theorem PrimrecPred.lt_pair : PrimrecPred (fun z : ℕ => z.unpair.2 < z.unpair.1) := by
  have h_le : PrimrecRel (fun x y : ℕ => y < x) :=
    Primrec.nat_lt.comp (Primrec.snd) (Primrec.fst)
  exact h_le.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem PrimrecPred.eq_const (k : ℕ) : PrimrecPred (fun n : ℕ => n = k) :=
  Primrec.eq.comp (Primrec.id) (Primrec.const k)

theorem Primrec.pair_zero : Primrec (fun x : ℕ => Nat.pair x 0) :=
  Primrec₂.natPair.comp Primrec.id (Primrec.const 0)

theorem Primrec.pair_swap : Primrec (fun z : ℕ => pair z.unpair.2 z.unpair.1) :=
  Primrec.pair (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair)

theorem Primrec.pair_unpair_repack :
    Primrec (fun z : ℕ => pair z.unpair.1 (pair z.unpair.2 0)) :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))

theorem Primrec.pair_assoc_left :
    Primrec (fun z : ℕ => pair (pair z.unpair.1 z.unpair.2.unpair.1) z.unpair.2.unpair.2) :=
  Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.unpair)
      (Primrec.comp (Primrec.fst) (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    (Primrec.comp (Primrec.snd) (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

theorem Primrec.pair_assoc_right :
    Primrec (fun z : ℕ => pair z.unpair.1.unpair.1 (pair z.unpair.1.unpair.2 z.unpair.2)) :=
  Primrec₂.natPair.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
    (Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))


/-! ## Behavior under Boolean operators -/

/-! Negation duality -/

private theorem neg_aux :
    (∀ p : ℕ → Prop, sigma0 n p → pi0 n (fun x => ¬(p x))) ∧
    (∀ p : ℕ → Prop, pi0 n p → sigma0 n (fun x => ¬(p x))) := by
  induction n with
  | zero =>
    exact ⟨fun p hp => PrimrecPred.not hp, fun p hp => PrimrecPred.not hp⟩
  | succ n ih =>
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun z => ¬(q z), ih.2 q hq, ?_⟩
      funext x
      simp
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun z => ¬(q z), ih.1 q hq, ?_⟩
      funext x
      simp

theorem pi0.iff_not_sigma0 : pi0 n p ↔ sigma0 n (fun x => ¬(p x)) := by
  constructor
  · intro h
    exact neg_aux.2 p h
  · intro h
    have := neg_aux.1 _ h
    simp_all

theorem sigma0.iff_not_pi0 : sigma0 n p ↔ pi0 n (fun x => ¬(p x)) := by
  constructor
  · intro h
    exact neg_aux.1 p h
  · intro h
    have := neg_aux.2 _ h
    simp_all

/-! Closure under and/or -/

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


/-! ## Closure under bounded quantifiers -/

/-! pi0 closed under bounded universal quantification -/

private theorem PrimrecPred.forall_lt_pair (hS : PrimrecPred (fun z : ℕ => S z.unpair.1 z.unpair.2))
    (hb : Primrec b) : PrimrecPred (fun w : ℕ => ∀ y < b w, S w y) := by
  sorry

theorem pi0.forall_lt_primrec : pi0 n (fun z => S z.unpair.1 z.unpair.2) → Primrec b →
    pi0 n (fun w => ∀ y < b w, S w y) := by
  induction n with
  | zero =>
    intro hS hb
    exact PrimrecPred.forall_lt_pair hS hb
  | succ n ih =>
    intro hS hb
    obtain ⟨q, hq, heq⟩ := hS
    refine ⟨fun m => ¬(m.unpair.2.unpair.1 < b m.unpair.1) ∨
      q (pair (pair m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2), ?_, ?_⟩
    · -- sigma0 n
      have hB : PrimrecPred (fun m : ℕ => m.unpair.2.unpair.1 < b m.unpair.1) := by
        sorry
      exact sigma0.or (sigma0.of_primrec (PrimrecPred.not hB))
        (sigma0.comp_primrec hq Primrec.pair_assoc_left)
    · -- function equality
      sorry

theorem pi0.forall_lt (hR : pi0 n (fun z => R z.unpair.1 z.unpair.2)) :
    pi0 n (fun x => ∀ y < x, R x y) := by
  sorry
/-! sigma0 closed under bounded existential quantification -/

theorem sigma0.exists_lt_primrec : sigma0 n (fun z => S z.unpair.1 z.unpair.2) → Primrec b →
    sigma0 n (fun w => ∃ y < b w, S w y) := by
  sorry

theorem sigma0.exists_lt (hR : sigma0 n (fun z => R z.unpair.1 z.unpair.2)) :
    sigma0 n (fun x => ∃ y < x, R x y) := by
  sorry

/-! sigma0 closed under bounded universal quantification -/

theorem sigma0.forall_lt (hR : sigma0 n (fun z => R z.unpair.1 z.unpair.2)) :
    sigma0 n (fun x => ∀ y < x, R x y) := by
  sorry

theorem sigma0.forall_lt_primrec : sigma0 n (fun z => S z.unpair.1 z.unpair.2) → Primrec b →
    sigma0 n (fun w => ∀ y < b w, S w y) := by
  sorry

/-! pi0 closed under bounded existential quantification -/

theorem pi0.exists_lt (hR : pi0 n (fun z => R z.unpair.1 z.unpair.2)) :
    pi0 n (fun x => ∃ y < x, R x y) := by
  sorry

theorem pi0.exists_lt_primrec : pi0 n (fun z => S z.unpair.1 z.unpair.2) → Primrec b →
    pi0 n (fun w => ∃ y < b w, S w y) := by
  sorry

end Computability
