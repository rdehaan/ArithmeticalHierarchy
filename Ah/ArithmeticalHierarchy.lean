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
* TODO

## Main results

* `sigma0.zero_iff`, `pi0.zero_iff` : Σ⁰₀ and Π⁰₀ are the primitive recursive predicates.
* `sigma0.one_iff_re`  : Σ⁰₁ = recursively enumerable predicates (`REPred`).
* `pi0.one_iff_co_re`  : Π⁰₁ = co-r.e. predicates.
* `delta0.one_iff_computable` : Δ⁰₁ = computable predicates (`ComputablePred`), i.e. Post's theorem.
* TODO
-/

open Nat (pair unpair)
open Nat.Partrec.Code (eval evaln evaln_complete evaln_sound ofNatCode)

namespace Computability

variable {n m : ℕ} {p q : ℕ → Prop} {f g : ℕ → ℕ} {r s : ℕ → ℕ → Prop}

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
    · refine ⟨fun m => p m.unpair.1, ?_⟩
      simp only [Nat.unpair_pair, exists_const, and_true]
      exact PrimrecPred.comp hp (Primrec.fst.comp Primrec.unpair)
    · refine ⟨fun m => p m.unpair.1, ?_⟩
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
        Primrec (fun m : ℕ => pair (f m.unpair.1) m.unpair.2) := fun f hf =>
      Primrec₂.natPair.comp (hf.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.snd.comp Primrec.unpair)
    refine ⟨fun p f hp hf => ?_, fun p f hp hf => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun m => q (pair (f m.unpair.1) m.unpair.2), ?_, ?_⟩
      · exact ih.2 q _ hq (h_unpack f hf)
      · funext x
        simp
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun m => q (pair (f m.unpair.1) m.unpair.2), ?_, ?_⟩
      · exact ih.1 q _ hq (h_unpack f hf)
      · funext x
        simp

theorem sigma0.comp_primrec (hp : sigma0 n p) (hf : Primrec f) : sigma0 n (fun x => p (f x)) :=
  comp_aux.1 p f hp hf

theorem pi0.comp_primrec (hp : pi0 n p) (hf : Primrec f) : pi0 n (fun x => p (f x)) :=
  comp_aux.2 p f hp hf

/-! Trivial (crossing) inclusions -/

theorem sigma0.of_pi0_succ (h : pi0 n p) : sigma0 (n + 1) p := by
  refine ⟨fun m => p m.unpair.1, pi0.comp_primrec h (Primrec.fst.comp Primrec.unpair), ?_⟩
  funext x
  simp

theorem pi0.of_sigma0_succ (h : sigma0 n p) : pi0 (n + 1) p := by
  refine ⟨fun m => p m.unpair.1, sigma0.comp_primrec h (Primrec.fst.comp Primrec.unpair), ?_⟩
  funext x
  simp

/-! Quantifier shifting -/

theorem pi0.of_forall_sigma01 (hp : sigma0 1 (fun m => r m.unpair.1 m.unpair.2)) :
    pi0 2 (fun x => ∀ y, r x y) := by
  refine ⟨fun m => r m.unpair.1 m.unpair.2, hp, ?_⟩
  simp

theorem sigma0.of_exists_pi01 (hp : pi0 1 (fun m => r m.unpair.1 m.unpair.2)) :
    sigma0 2 (fun x => ∃ y, r x y) := by
  refine ⟨_, hp, ?_⟩
  simp


/-! ## Helpers -/

/-! Primitive recursive helpers -/

theorem PrimrecPred.lt_pair : PrimrecPred (fun m : ℕ => m.unpair.2 < m.unpair.1) := by
  have h_le : PrimrecRel (fun x y : ℕ => y < x) :=
    Primrec.nat_lt.comp (Primrec.snd) (Primrec.fst)
  exact h_le.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem PrimrecPred.eq_const (k : ℕ) : PrimrecPred (fun n : ℕ => n = k) :=
  Primrec.eq.comp (Primrec.id) (Primrec.const k)

theorem Primrec.pair_zero : Primrec (fun x : ℕ => Nat.pair x 0) :=
  Primrec₂.natPair.comp Primrec.id (Primrec.const 0)

theorem Primrec.pair_swap : Primrec (fun m : ℕ => pair m.unpair.2 m.unpair.1) :=
  Primrec.pair (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair)

theorem Primrec.pair_unpair_repack :
    Primrec (fun m : ℕ => pair m.unpair.1 (pair m.unpair.2 0)) :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))

theorem Primrec.pair_assoc_left :
    Primrec (fun m : ℕ => pair (pair m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2) :=
  Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.unpair)
      (Primrec.comp (Primrec.fst) (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    (Primrec.comp (Primrec.snd) (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

theorem Primrec.pair_assoc_right :
    Primrec (fun m : ℕ => pair m.unpair.1.unpair.1 (pair m.unpair.1.unpair.2 m.unpair.2)) :=
  Primrec₂.natPair.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
    (Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))

private theorem PrimrecPred.forall_lt_pair (hs : PrimrecPred (fun m : ℕ => s m.unpair.1 m.unpair.2))
    (hb : Primrec b) : PrimrecPred (fun w : ℕ => ∀ y < b w, s w y) := by
  have hT : PrimrecRel (fun a b' : ℕ => s b' a) := by
    have h := PrimrecPred.comp hs (Primrec₂.natPair.comp Primrec.snd Primrec.fst)
    have heq : (fun p : ℕ × ℕ => s (Nat.pair p.2 p.1).unpair.1 (Nat.pair p.2 p.1).unpair.2)
        = (fun p : ℕ × ℕ => s p.2 p.1) := by
      funext p; simp
    simp_all [PrimrecRel]
  have hforall := PrimrecRel.forall_lt hT
  exact hforall.comp hb Primrec.id

/-! Finite-sequence coding (needed for sigma0.forall_lt_primrec) -/

private def seqDecode (s y : ℕ) : ℕ :=
  ((Encodable.decode (α := List ℕ) s).getD []).getD y 0

private theorem primrec₂_seqDecode : Primrec₂ seqDecode :=
  (Primrec.list_getD 0).comp ( Primrec.option_getD.comp
    ( Primrec.decode.comp ( Primrec.fst ) ) ( Primrec.const [] ) ) ( Primrec.snd )

private theorem exists_seqDecode (x : ℕ) (w : ℕ → ℕ) :
    ∃ s : ℕ, ∀ y < x, seqDecode s y = w y := by
  unfold seqDecode
  use Encodable.encode (List.map w (List.range x))
  simp_all

private theorem bounded_collection :
    (∀ m < n, ∃ k, r m k) ↔ ∃ s : ℕ, ∀ m < n, r m (seqDecode s m) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := exists_seqDecode n (fun m => if hm : m < n then (h m hm).choose else 0)
    refine ⟨s, fun m hm => ?_⟩
    simp_all [(h m hm).choose_spec]
  · intro ⟨s, hs⟩ m hm
    exact ⟨_, hs m hm⟩


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
      refine ⟨fun m => ¬(q m), ih.2 q hq, ?_⟩
      funext x
      simp
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun m => ¬(q m), ih.1 q hq, ?_⟩
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
    have g₁ : Primrec (fun m : ℕ => pair m.unpair.1 m.unpair.2.unpair.1) :=
      Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    -- g₁ ⟨x,⟨y₁,y₂⟩⟩ = ⟨x,y₂⟩
    have g₂ : Primrec (fun m : ℕ => pair m.unpair.1 m.unpair.2.unpair.2) :=
      Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- sigma0 n conjunction
      rintro p q ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
      refine ⟨fun m => q₁ (pair m.unpair.1 m.unpair.2.unpair.1) ∧
        q₂ (pair m.unpair.1 m.unpair.2.unpair.2), ?_, ?_⟩
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
      refine ⟨fun m => q₁ m ∨ q₂ m, ihPiOr _ _ hq₁ hq₂, ?_⟩
      funext x
      simp [exists_or]
    · -- pi0 n conjunction
      rintro p q ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
      refine ⟨fun m => q₁ m ∧ q₂ m, ihSigmaAnd _ _ hq₁ hq₂, ?_⟩
      funext x
      simp [forall_and]
    · -- pi0 n disjunction
      rintro p q ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
      refine ⟨fun m => q₁ (pair m.unpair.1 m.unpair.2.unpair.1) ∨
          q₂ (pair m.unpair.1 m.unpair.2.unpair.2), ?_, ?_⟩
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


/-! ## Closure under (bounded) quantifiers -/

/-! pi0 is closed under bounded universal quantification -/

theorem pi0.forall_lt_primrec : pi0 n (fun m => s m.unpair.1 m.unpair.2) → Primrec g →
    pi0 n (fun w => ∀ y < g w, s w y) := by
  induction n with
  | zero =>
    intro hs hg
    exact PrimrecPred.forall_lt_pair hs hg
  | succ n ih =>
    intro hs hg
    obtain ⟨q, hq, heq⟩ := hs
    -- pointwise description of s
    have key : ∀ a c : ℕ, s a c ↔ ∀ t, q (pair (pair a c) t) := by
      intro a c
      have := congrFun heq (pair a c)
      simp_all
    refine ⟨fun m => ¬(m.unpair.2.unpair.1 < g m.unpair.1) ∨
      q (pair (pair m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2), ?_, ?_⟩
    · -- show sigma0 n
      have hB : PrimrecPred (fun m : ℕ => m.unpair.2.unpair.1 < g m.unpair.1) := by
        have h1 : Primrec (fun m : ℕ => m.unpair.2.unpair.1) :=
          Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
        have h2 : Primrec (fun m : ℕ => g m.unpair.1) :=
          hg.comp (Primrec.fst.comp Primrec.unpair)
        exact PrimrecRel.comp Primrec.nat_lt h1 h2
      exact sigma0.or (sigma0.of_primrec (PrimrecPred.not hB))
        (sigma0.comp_primrec hq Primrec.pair_assoc_left)
    · -- show function equality
      funext w
      apply propext
      constructor
      · intro h v
        simp only [Nat.unpair_pair]
        by_cases hv : v.unpair.1 < g w
        · right; simp_all
        · left; exact hv
      · intro h y hy
        rw [key w y]
        intro t
        have hv := h (pair y t)
        simp_all

theorem pi0.forall_lt (hr : pi0 n (fun m => r m.unpair.1 m.unpair.2)) :
    pi0 n (fun x => ∀ y < x, r x y) :=
  pi0.forall_lt_primrec hr Primrec.id

/-! sigma0 is closed under bounded existential quantification -/

theorem sigma0.exists_lt_primrec : sigma0 n (fun m => s m.unpair.1 m.unpair.2) → Primrec g →
    sigma0 n (fun w => ∃ y < g w, s w y) := by
  intro hs hg
  -- use negation duality with pi0 and pi0.forall_lt_primrec
  have hs' : pi0 n (fun m => ¬(s m.unpair.1 m.unpair.2)) :=
    sigma0.iff_not_pi0.mp hs
  have hforall : pi0 n (fun w => ∀ y < g w, ¬(s w y)) :=
    pi0.forall_lt_primrec (s := fun x y => ¬(s x y)) hs' hg
  have heq : (fun w => ∀ y < g w, ¬(s w y)) = (fun w : ℕ => ¬ ∃ y < g w, s w y) := by
    funext w
    apply propext
    constructor <;> simp_all
  simp_all [sigma0.iff_not_pi0]

theorem sigma0.exists_lt (hr : sigma0 n (fun m => r m.unpair.1 m.unpair.2)) :
    sigma0 n (fun x => ∃ y < x, r x y) :=
  sigma0.exists_lt_primrec hr Primrec.id

/-! sigma0 is closed under bounded universal quantification -/

theorem sigma0.forall_lt_primrec : sigma0 n (fun m => s m.unpair.1 m.unpair.2) → Primrec g →
    sigma0 n (fun w => ∀ y < g w, s w y) := by
  induction n with
  | zero =>
    intro hs hg
    exact PrimrecPred.forall_lt_pair hs hg
  | succ n ih =>
    intro hs hb
    obtain ⟨q, hq, heq⟩ := hs
    -- pointwise description of s
    have key : ∀ a c : ℕ, s a c ↔ ∃ t, q (pair (pair a c) t) := by
      intro a c
      have := congrFun heq (pair a c)
      simp_all
    have hg : Primrec (fun m : ℕ => pair (pair m.unpair.1.unpair.1 m.unpair.2)
          (seqDecode m.unpair.1.unpair.2 m.unpair.2)) :=
      Primrec₂.natPair.comp
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair))
        (primrec₂_seqDecode.comp
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair))
    refine ⟨fun m => ∀ y < g m.unpair.1,
        q (pair (pair m.unpair.1 y) (seqDecode m.unpair.2 y)), ?_, ?_⟩
    · -- show pi0 n
      exact pi0.forall_lt_primrec
        (s := (fun m y => q (pair (pair m.unpair.1 y) (seqDecode m.unpair.2 y))))
        (pi0.comp_primrec hq hg)
        (hb.comp (Primrec.fst.comp Primrec.unpair))
    · -- show function equality
      funext w
      apply propext
      constructor
      · intro h
        have h' : ∀ y < g w, ∃ t, q (pair (pair w y) t) :=
          fun y hy => (key w y).mp (h y hy)
        obtain ⟨s, hs⟩ := bounded_collection.mp h'
        use s
        simp_all
      · rintro ⟨s, hs⟩
        simp_all only [Nat.pair_unpair]
        aesop

theorem sigma0.forall_lt (hr : sigma0 n (fun m => r m.unpair.1 m.unpair.2)) :
    sigma0 n (fun x => ∀ y < x, r x y) :=
  sigma0.forall_lt_primrec hr Primrec.id

/-! pi0 is closed under bounded existential quantification -/

theorem pi0.exists_lt_primrec : pi0 n (fun m => s m.unpair.1 m.unpair.2) → Primrec g →
    pi0 n (fun w => ∃ y < g w, s w y) := by
  intro hs hg
  -- use negation duality with sigma0 and sigma0.forall_lt_primrec
  have hs' : sigma0 n (fun m => ¬(s m.unpair.1 m.unpair.2)) :=
    pi0.iff_not_sigma0.mp hs
  have hforall : sigma0 n (fun w => ∀ y < g w, ¬(s w y)) :=
    sigma0.forall_lt_primrec (s := fun x y => ¬(s x y)) hs' hg
  have heq : (fun w => ∀ y < g w, ¬(s w y)) = (fun w : ℕ => ¬ ∃ y < g w, s w y) := by
    funext w
    apply propext
    constructor <;> simp_all
  simp_all [sigma0.iff_not_pi0]

theorem pi0.exists_lt (hR : pi0 n (fun m => r m.unpair.1 m.unpair.2)) :
    pi0 n (fun x => ∃ y < x, r x y) :=
  pi0.exists_lt_primrec hR Primrec.id

/-! delta0 is closed under bounded quantifiers -/

theorem delta0.exists_lt (hr : delta0 n (fun m => r m.unpair.1 m.unpair.2)) :
    delta0 n (fun m => ∃ k < m, r m k) :=
  ⟨sigma0.exists_lt hr.1, pi0.exists_lt hr.2⟩

theorem delta0.forall_lt (hr : delta0 n (fun m => r m.unpair.1 m.unpair.2)) :
    delta0 n (fun m => ∀ k < m, r m k) :=
  ⟨sigma0.forall_lt hr.1, pi0.forall_lt hr.2⟩

theorem delta0.exists_lt_primrec : delta0 n (fun m => s m.unpair.1 m.unpair.2) → Primrec g →
    delta0 n (fun m => ∃ k < g m, s m k) := by
  intro hs hg
  exact ⟨sigma0.exists_lt_primrec hs.1 hg, pi0.exists_lt_primrec hs.2 hg⟩

theorem delta0.forall_lt_primrec : delta0 n (fun m => s m.unpair.1 m.unpair.2) → Primrec g →
    delta0 n (fun m => ∀ k < g m, s m k) := by
  intro hs hg
  exact ⟨sigma0.forall_lt_primrec hs.1 hg, pi0.forall_lt_primrec hs.2 hg⟩

/-! sigma0 is closed under unbounded existential quantification -/

theorem sigma0.exists_succ (h : sigma0 (n + 1) q) :
    sigma0 (n + 1) (fun m => ∃ k, q (pair m k)) := by
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨fun m => q (pair (pair m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2),
    pi0.comp_primrec hq Primrec.pair_assoc_left, ?_⟩
  funext m
  apply propext
  constructor
  · rintro ⟨k, k', hk'⟩
    refine ⟨pair k k', ?_⟩
    simp_all
  · rintro ⟨k, hk⟩
    simp_all only [Nat.unpair_pair]
    exact ⟨k.unpair.1, k.unpair.2, hk⟩

/-! pi0 is closed under unbounded universal quantification -/

theorem pi0.forall_succ (h : pi0 (n + 1) q) :
    pi0 (n + 1) (fun m => ∀ k, q (pair m k)) := by
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨fun m => q (pair (pair m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2),
    sigma0.comp_primrec hq Primrec.pair_assoc_left, ?_⟩
  funext m
  apply propext
  constructor
  · intro hall k
    have := hall k.unpair.1 k.unpair.2
    simp_all
  · intro hall k k'
    have := hall (pair k k')
    simp_all


/-! ## Closure under computable substitution and many-one reducibility -/

/-! Closure under computable substitution -/

theorem sigma0.comp_computable (hp : sigma0 (n + 1) p) (hf : Computable f) :
    sigma0 (n + 1) (fun x => p (f x)) := by
  sorry

theorem pi0.comp_computable (hp : pi0 (n + 1) p) (hf : Computable f) :
    pi0 (n + 1) (fun x => p (f x)) := by
  sorry

theorem delta0.comp_computable (hp : delta0 (n + 1) p) (hf : Computable f) :
    delta0 (n + 1) (fun x => p (f x)) :=
  ⟨sigma0.comp_computable hp.1 hf, pi0.comp_computable hp.2 hf⟩

/-! Downward closure under many-one reducibility -/

theorem sigma0.of_manyOneReducible (hred : p ≤₀ q) (hq : sigma0 (n + 1) q) : sigma0 (n + 1) p := by
  obtain ⟨f, hf, hpq⟩ := hred
  have heq : p = fun m => q (f m) := by
    funext m
    apply propext
    simp_all
  rw [heq]
  exact sigma0.comp_computable hq hf

theorem pi0.of_manyOneReducible (hred : p ≤₀ q) (hq : pi0 (n + 1) q) : pi0 (n + 1) p := by
  obtain ⟨f, hf, hpq⟩ := hred
  have heq : p = fun m => q (f m) := by
    funext m
    apply propext
    simp_all
  rw [heq]
  exact pi0.comp_computable hq hf

theorem delta0.of_manyOneReducible (hred : p ≤₀ q) (hq : delta0 (n + 1) q) : delta0 (n + 1) p :=
  ⟨sigma0.of_manyOneReducible hred hq.1, pi0.of_manyOneReducible hred hq.2⟩


/-! ## Characterization of the first level -/

private theorem sigma0.one_to_re (h : sigma0 1 p) : REPred p := by
  sorry

private theorem re_to_sigma0_one (h : REPred p) : sigma0 1 p := by
  sorry

theorem sigma0.one_iff_re : sigma0 1 p ↔ REPred p :=
  ⟨sigma0.one_to_re, re_to_sigma0_one⟩

theorem pi0.one_iff_co_re : pi0 1 p ↔ REPred (fun x => ¬(p x)) := by
  rw [pi0.iff_not_sigma0, sigma0.one_iff_re]

theorem delta0.one_iff_computable : delta0 1 p ↔ ComputablePred p := by
  rw [delta0, sigma0.one_iff_re, pi0.one_iff_co_re]
  exact ComputablePred.computable_iff_re_compl_re'.symm

/-! Computable functions are sigma0 and pi0 for n ≥ 1 -/

theorem sigma0.of_computable (hn : 1 ≤ n) (h : ComputablePred p) : sigma0 n p := by
  rw [← delta0.one_iff_computable, delta0] at h
  exact sigma0.mono_le (n := 1) (m := n) hn h.left

theorem pi0.of_computable (hn : 1 ≤ n) (h : ComputablePred p) : pi0 n p := by
  rw [← delta0.one_iff_computable, delta0] at h
  exact pi0.mono_le (n := 1) (m := n) hn h.right


/-! ## Completeness -/

/-! Definitions and basic infrastructure -/

def sigma0Complete (n : ℕ) (p : ℕ → Prop) : Prop := sigma0 n p ∧ ∀ q : ℕ → Prop, sigma0 n q → q ≤₀ p

def pi0Complete (n : ℕ) (p : ℕ → Prop) : Prop := pi0 n p ∧ ∀ q : ℕ → Prop, pi0 n q → q ≤₀ p

def sigma0Hard (n : ℕ) (p : ℕ → Prop) : Prop := ∀ q : ℕ → Prop, sigma0 n q → q ≤₀ p

def pi0Hard (n : ℕ) (p : ℕ → Prop) : Prop := ∀ q : ℕ → Prop, pi0 n q → q ≤₀ p

theorem sigma0Complete.iff_mem_hard : sigma0Complete n p ↔ sigma0 n p ∧ sigma0Hard n p := by rfl

theorem pi0Complete.iff_mem_hard : pi0Complete n p ↔ pi0 n p ∧ pi0Hard n p := by rfl

theorem sigma0Complete.mk (hmem : sigma0 n p) (hhard : sigma0Hard n p) : sigma0Complete n p :=
  ⟨hmem, hhard⟩

theorem pi0Complete.mk (hmem : pi0 n p) (hhard : pi0Hard n p) : pi0Complete n p :=
  ⟨hmem, hhard⟩

theorem sigma0Hard.of_manyOneReducible (hq : sigma0Hard n q) (hred : q ≤₀ p) : sigma0Hard n p :=
  fun q' hq' => (hq q' hq').trans hred

theorem pi0Hard.of_manyOneReducible (hq : pi0Hard n q) (hred : q ≤₀ p) : pi0Hard n p :=
  fun q' hq' => (hq q' hq').trans hred

theorem sigma0Complete.of_manyOneReducible
    (hq : sigma0Complete n q) (hp : sigma0 n p) (hred : q ≤₀ p) : sigma0Complete n p :=
  ⟨hp, sigma0Hard.of_manyOneReducible hq.2 hred⟩

theorem pi0Complete.of_manyOneReducible
    (hq : pi0Complete n q) (hp : pi0 n p) (hred : q ≤₀ p) : pi0Complete n p :=
  ⟨hp, pi0Hard.of_manyOneReducible hq.2 hred⟩

/-! The halting set -/

mutual

/-- The halting set and its complement set

The program code `m.unpair.1` and the input `m.unpair.2` are kept in the top-level pairing
inside the recursive definition, to simplify bookkeeping. -/
def haltingSet : ℕ → (ℕ → Prop)
  | 0     => fun m => evaln 0 (ofNatCode m.unpair.1) m.unpair.2 ≠ none
  | 1     => fun m => (eval (ofNatCode m.unpair.1) m.unpair.2).Dom
  | n + 2 => fun m => ∃ y, haltingSetCompl (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 y))

def haltingSetCompl : ℕ → (ℕ → Prop)
  | 0     => fun m => evaln 0 (ofNatCode m.unpair.1) m.unpair.2 = none
  | 1     => fun m => ¬ (eval (ofNatCode m.unpair.1) m.unpair.2).Dom
  | n + 2 => fun m => ∀ y, haltingSet (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 y))

end

@[simp]
theorem haltingSet_zero : haltingSet 0 = fun m =>
    evaln 0 (ofNatCode m.unpair.1) m.unpair.2 ≠ none := rfl

@[simp]
theorem haltingSet_one : haltingSet 1 = fun m =>
    (eval (ofNatCode m.unpair.1) m.unpair.2).Dom := rfl

@[simp]
theorem haltingSet_succ_succ (n : ℕ) : haltingSet (n + 2) = fun m =>
      ∃ y, haltingSetCompl (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 y)) := rfl

@[simp]
theorem haltingSetCompl_zero : haltingSetCompl 0 = fun m =>
    evaln 0 (ofNatCode m.unpair.1) m.unpair.2 = none := rfl

@[simp]
theorem haltingSetCompl_one : haltingSetCompl 1 = fun m =>
    ¬(eval (ofNatCode m.unpair.1) m.unpair.2).Dom := rfl

@[simp]
theorem haltingSetCompl_succ_succ (n : ℕ) :
    haltingSetCompl (n + 2) = fun m =>
      ∀ y, haltingSet (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 y)) := rfl

/-! Complementarity of haltingSet and haltingSetCompl -/

theorem haltingSet_compl (n : ℕ) (m : ℕ) : haltingSetCompl n m ↔ ¬(haltingSet n m) := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 =>
    simp only [haltingSetCompl_succ_succ, haltingSet_succ_succ, not_exists]
    refine forall_congr' fun y => ?_
    have := haltingSet_compl (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 y))
    simp_all

/-! Membership in the halting set depends on the code only through eval -/

theorem haltingSet_eval_congr_both (c c' : ℕ) (h : eval (ofNatCode c) = eval (ofNatCode c')) :
    ∀ a : ℕ, (haltingSet (n + 1) (Nat.pair c a) ↔ haltingSet (n + 1) (Nat.pair c' a)) ∧
      (haltingSetCompl (n + 1) (Nat.pair c a) ↔ haltingSetCompl (n + 1) (Nat.pair c' a)) := by
  sorry

theorem haltingSet_eval_congr (c c' : ℕ) (h : eval (ofNatCode c) = eval (ofNatCode c')) (m : ℕ) :
    haltingSet (n + 1) (Nat.pair c m) ↔ haltingSet (n + 1) (Nat.pair c' m) :=
  (haltingSet_eval_congr_both c c' h m).1

theorem haltingSetCompl_eval_congr (c c' : ℕ) (h : eval (ofNatCode c) = eval (ofNatCode c'))
    (m : ℕ) : haltingSetCompl (n + 1) (Nat.pair c m) ↔ haltingSetCompl (n + 1) (Nat.pair c' m) :=
  (haltingSet_eval_congr_both c c' h m).2

/-! Inclusion of halting set and its complement in the corresponding levels of the hierarchy -/

private theorem haltingSet_level : sigma0 n (haltingSet n) ∧ pi0 n (haltingSetCompl n) := by
  sorry

theorem haltingSet_mem_sigma0 (n : ℕ) : sigma0 n (haltingSet n) := haltingSet_level.1

theorem haltingSetCompl_mem_pi0 (n : ℕ) : pi0 n (haltingSetCompl n) := haltingSet_level.2

/-! Completeness of the halting set and its complement for the first level -/

theorem haltingSet_one_sigma0_complete : sigma0Complete 1 (haltingSet 1) := by
  refine ⟨haltingSet_mem_sigma0 1, fun q hq => ?_⟩
  rw [sigma0.one_iff_re] at hq
  obtain ⟨d, hd⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hq.map (Computable.const 0).to₂))
  refine ⟨fun x => Nat.pair (Encodable.encode d) x, ?_, ?_⟩
  · exact (Primrec₂.natPair.comp (Primrec.const (Encodable.encode d)) Primrec.id).to_comp
  · intro m
    rw [haltingSet_one]
    have hof : ofNatCode (Encodable.encode d) = d := by
      rw [← Nat.Partrec.Code.ofNatCode_eq]
      simp_all [Denumerable.ofNat_encode]
    simp only [Nat.unpair_pair, hof, hd]
    constructor
    · intro h
      exact ⟨h, trivial⟩
    · intro h
      exact h.fst

theorem haltingSet_one_not_computable : ¬(ComputablePred (haltingSet 1)) := by
  sorry

theorem haltingSet_one_not_pi0_one : ¬(pi0 1 (haltingSet 1)) := by
  intro h
  apply haltingSet_one_not_computable
  rw [← delta0.one_iff_computable]
  exact ⟨haltingSet_mem_sigma0 1, h⟩

theorem ManyOneReducible.compl (h : p ≤₀ q) : (fun x => ¬ p x) ≤₀ (fun x => ¬ q x) := by
  obtain ⟨f, hf, hpq⟩ := h
  refine ⟨f, hf, ?_⟩
  simp_all

theorem haltingSetCompl_one_pi0_complete : pi0Complete 1 (haltingSetCompl 1) :=
  pi0Complete.mk (haltingSetCompl_mem_pi0 1) (fun q hq => by
    simp_all only [pi0.iff_not_sigma0]
    obtain ⟨f, hf, hfr⟩ := haltingSet_one_sigma0_complete.2 (fun x => ¬(q x)) hq
    refine ⟨f, hf, fun x => ?_⟩
    rw [haltingSet_compl]
    sorry)

theorem haltingSetCompl_one_not_computable : ¬(ComputablePred (haltingSetCompl 1)) := by
  sorry

theorem haltingSetCompl_one_not_sigma0_one : ¬(sigma0 1 (haltingSetCompl 1)) := by
  intro h
  apply haltingSetCompl_one_not_computable
  rw [← delta0.one_iff_computable]
  exact ⟨h, haltingSetCompl_mem_pi0 1⟩

/-! Section completeness of the halting set -/

theorem haltingSet_section :
    (∀ s : ℕ → Prop, sigma0 (n + 1) s →
      ∃ c : ℕ, ∀ m, s m ↔ haltingSet (n + 1) (Nat.pair c m)) ∧
    (∀ s : ℕ → Prop, pi0 (n + 1) s →
      ∃ c : ℕ, ∀ m, s m ↔ haltingSetCompl (n + 1) (Nat.pair c m)) := by
  sorry


/-! ## Completeness for higher levels -/

private theorem haltingSetCompl_pad (hg : Computable g) : ∃ f : ℕ → ℕ, Computable f ∧
      ∀ x, (∃ y, haltingSetCompl (n + 1) (g (pair x y))) ↔ haltingSet (n + 2) (f x) := by
  sorry

private theorem haltingSet_sigma_step (ih : pi0Complete (n + 1) (haltingSetCompl (n + 1)))
    (hq : sigma0 (n + 2) q) : q ≤₀ haltingSet (n + 2) := by
  sorry

private theorem haltingSet_pi_step (ih : sigma0Complete (n + 1) (haltingSet (n + 1)))
    (hq : pi0 (n + 2) q) : q ≤₀ haltingSetCompl (n + 2) := by
  sorry

private theorem haltingSet_complete :
    sigma0Complete (n + 1) (haltingSet (n + 1)) ∧
    pi0Complete (n + 1) (haltingSetCompl (n + 1)) := by
  sorry

theorem haltingSet_sigma0_complete : sigma0Complete (n + 1) (haltingSet (n + 1)) :=
  haltingSet_complete.1

theorem haltingSetCompl_pi0_complete : pi0Complete (n + 1) (haltingSetCompl (n + 1)) :=
  haltingSet_complete.2


/-! ## Strictness of the hierarchy -/

/-! Basic strictness results -/

theorem haltingSet_succ_not_computable : ¬(ComputablePred (haltingSet (n + 1))) := by
  sorry

theorem haltingSet_not_pi0 : ¬(pi0 (n + 1) (haltingSet (n + 1))) := by
  sorry

theorem haltingSetCompl_not_sigma0 : ¬(sigma0 (n + 1) (haltingSetCompl (n + 1))) := by
  sorry

theorem exists_sigma0_not_pi0 : ∃ p : ℕ → Prop, sigma0 (n + 1) p ∧ ¬(pi0 (n + 1) p) := by
  sorry

theorem exists_pi0_not_sigma0 : ∃ p : ℕ → Prop, pi0 (n + 1) p ∧ ¬(sigma0 (n + 1) p) := by
  sorry

theorem sigma0_strict : (∀ p, sigma0 n p → sigma0 (n + 1) p) ∧
    ¬(∀ p, sigma0 (n + 1) p → sigma0 n p) := by
  sorry

theorem pi0_strict : (∀ p, pi0 n p → pi0 (n + 1) p) ∧
    ¬(∀ p, pi0 (n + 1) p → pi0 n p) := by
  sorry

theorem delta0_strict_sigma0 : ∃ p : ℕ → Prop, sigma0 (n + 1) p ∧ ¬(delta0 (n + 1) p) := by
  sorry

theorem delta0_strict_pi0 : ∃ p : ℕ → Prop, pi0 (n + 1) p ∧ ¬(delta0 (n + 1) p) := by
  sorry

theorem sigma0_strict_delt0 : ∃ p : ℕ → Prop, sigma0 (n + 1) p ∧ ¬(delta0 n p) := by
  sorry

theorem pi0_strict_delt0 : ∃ p : ℕ → Prop, pi0 (n + 1) p ∧ ¬(delta0 n p) := by
  sorry

/-! Strictness in terms of (inclusions for) sets of sets -/

theorem sigma0_subset_sigma0_succ : {p : ℕ → Prop | sigma0 n p} ⊆ {p | sigma0 (n + 1) p} :=
  fun _ hp => sigma0.mono_le (Nat.le_succ n) hp

theorem pi0_subset_pi0_succ : {p : ℕ → Prop | pi0 n p} ⊆ {p | pi0 (n + 1) p} :=
  fun _ hp => pi0.mono_le (Nat.le_succ n) hp

theorem sigma0_proper_subset : {p : ℕ → Prop | sigma0 n p} ⊂ {p | sigma0 (n + 1) p} := by
  sorry

theorem pi0_proper_subset : {p : ℕ → Prop | pi0 n p} ⊂ {p | pi0 (n + 1) p} := by
  sorry

/-! Level collapse characterizations -/

theorem sigma0_subset_pi0_iff_collapse : (∀ p, sigma0 n p → pi0 n p) ↔
    (∀ p, sigma0 n p ↔ pi0 n p) := by
  sorry

theorem pi0_subset_sigma0_iff_collapse : (∀ p, pi0 n p → sigma0 n p) ↔
    (∀ p, pi0 n p ↔ sigma0 n p) := by
  sorry

/-! Inseparability of haltingSet and haltingSetCompl by delta0 sets -/

theorem haltingSet_inseparable : ¬(∃ q : ℕ → Prop, delta0 (n + 1) q) ∧
    (∀ x, haltingSet (n + 1) x → q x) ∧
    (∀ x, haltingSetCompl (n + 1) x → ¬(q x)) := by
  sorry


end Computability
