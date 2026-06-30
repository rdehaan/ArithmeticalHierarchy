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

This file defines the arithmetical hierarchy of predicates on an arbitrary `Primcodable`
type `α`. The existential/universal witnesses introduced at each level range over `ℕ`
(the level-`n+1` predicates are built from `α × ℕ → Prop` predicates).

## Main definitions

* `sigma0 n p` : the predicate `p : α → Prop` is Σ⁰ₙ.
* `pi0 n p`    : the predicate `p : α → Prop` is Π⁰ₙ.
* `delta0 n p` : the predicate `p : α → Prop` is Δ⁰ₙ (i.e. both Σ⁰ₙ and Π⁰ₙ).
* TODO

## Main results

* `sigma0.zero_iff`, `pi0.zero_iff` : Σ⁰₀ and Π⁰₀ are the primitive recursive predicates.
* `sigma0.one_iff_re`  : Σ⁰₁ = recursively enumerable predicates (`REPred`).
* `pi0.one_iff_co_re`  : Π⁰₁ = co-r.e. predicates.
* `delta0.one_iff_computable` : Δ⁰₁ = computable predicates (`ComputablePred`).
* TODO

## References
TODO

-/

open Nat (pair unpair)
open Nat.Partrec.Code (eval evaln evaln_complete evaln_sound ofNatCode)

namespace Computability

variable {n m : ℕ}
variable {α : Type*} [Primcodable α] {β : Type*} [Primcodable β]
variable {p q : α → Prop}
variable {g : ℕ → ℕ}
-- variable {r s : α → ℕ → Prop}

mutual

/-- `sigma0 n p` states that the predicate `p : α → Prop` is Σ⁰ₙ.

* Level 0 consists of the primitive recursive predicates.
* Level `n+1` predicates are existential projections of `pi0 n` predicates, where the
  existential witness ranges over `ℕ`.
-/
def sigma0 : ℕ → {α : Type*} → [Primcodable α] → (α → Prop) → Prop
  | 0,     _, _, p => PrimrecPred p
  | n + 1, α, _, p => ∃ q : α × ℕ → Prop, pi0 n q ∧ p = fun x ↦ ∃ k : ℕ, q (x, k)

/-- `pi0 n p` states that the predicate `p : α → Prop` is Π⁰ₙ.

* Level 0 consists of the primitive recursive predicates.
* Level `n+1` predicates are universal projections of `sigma0 n` predicates, where the
  universally quantified variable ranges over `ℕ`.
-/
def pi0 : ℕ → {α : Type*} → [Primcodable α] → (α → Prop) → Prop
  | 0,     _, _, p => PrimrecPred p
  | n + 1, α, _, p => ∃ q : α × ℕ → Prop, sigma0 n q ∧ p = fun x ↦ ∀ k : ℕ, q (x, k)

end

/-- `delta0 n p` states that the predicate `p : α → Prop` is Δ⁰ₙ, i.e., both Σ⁰ₙ and Π⁰ₙ. -/
def delta0 (n : ℕ) {α : Type*} [Primcodable α] (p : α → Prop) : Prop := sigma0 n p ∧ pi0 n p

/-! Unfolding lemmas -/

@[simp]
theorem sigma0.zero_eq : sigma0 0 p = PrimrecPred p := rfl

@[simp]
theorem sigma0.succ_eq : sigma0 (n + 1) p = ∃ q : α × ℕ → Prop,
    pi0 n q ∧ p = fun x ↦ ∃ k : ℕ, q (x, k) := rfl

@[simp]
theorem pi0.zero_eq : pi0 0 p = PrimrecPred p := rfl

@[simp]
theorem pi0.succ_eq : pi0 (n + 1) p = ∃ q : α × ℕ → Prop,
    sigma0 n q ∧ p = fun x ↦ ∀ k : ℕ, q (x, k) := rfl


/-! ## Basic properties -/

/-! Level 0 coincides with `PrimrecPred` -/

theorem sigma0.zero_iff : sigma0 0 p ↔ PrimrecPred p := by rfl

theorem pi0.zero_iff : pi0 0 p ↔ PrimrecPred p := by rfl

theorem delta0.zero_iff : delta0 0 p ↔ PrimrecPred p := by simp [delta0]

/-! Monotonicity properties -/

private lemma mono_aux :
    (sigma0 n p → sigma0 (n + 1) p) ∧
    (pi0 n p → pi0 (n + 1) p) := by
  induction n generalizing α p with
  | zero =>
    simp only [sigma0.zero_eq, zero_add, sigma0.succ_eq, pi0.zero_eq, pi0.succ_eq]
    refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
    · refine ⟨fun x ↦ p x.1, ?_, ?_⟩
      · exact PrimrecPred.comp hp Primrec.fst
      · funext m
        simp
    · refine ⟨fun x ↦ p x.1, ?_, ?_⟩
      · exact PrimrecPred.comp hp Primrec.fst
      · funext m
        simp
  | succ n ih =>
    refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨q, ih.2 hq, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨q, ih.1 hq, rfl⟩

theorem sigma0.mono (h : sigma0 n p) : sigma0 (n + 1) p := mono_aux.1 h
theorem pi0.mono (h : pi0 n p) : pi0 (n + 1) p := mono_aux.2 h

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

private lemma comp_aux {f : β → α} :
    (sigma0 n p → Primrec f → sigma0 n (fun x ↦ p (f x))) ∧
    (pi0 n p → Primrec f → pi0 n (fun x ↦ p (f x))) := by
  induction n generalizing α β p f with
  | zero =>
    exact ⟨fun hp hf ↦ PrimrecPred.comp hp hf,
           fun hp hf ↦ PrimrecPred.comp hp hf⟩
  | succ n ih =>
    refine ⟨fun hp hf ↦ ?_, fun hp hf ↦ ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨fun x ↦ q (f x.1, x.2), ih.2 hq ((hf.comp Primrec.fst).pair Primrec.snd), rfl⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨fun x ↦ q (f x.1, x.2), ih.1 hq ((hf.comp Primrec.fst).pair Primrec.snd), rfl⟩

theorem sigma0.comp_primrec {f : β → α} (hp : sigma0 n p) (hf : Primrec f) :
    sigma0 n (fun x ↦ p (f x)) :=
  comp_aux.1 hp hf

theorem pi0.comp_primrec {f : β → α} (hp : pi0 n p) (hf : Primrec f) :
    pi0 n (fun x ↦ p (f x)) :=
  comp_aux.2 hp hf

theorem sigma0.comp_primrec_rightInverse {f : β → α} {g : α → β} (hg : Primrec g)
    (hfg : ∀ a, f (g a) = a) : sigma0 n (p ∘ f) → sigma0 n p := by
  intro hp
  have : p = (p ∘ f) ∘ g := funext fun a => by simp [hfg]
  rw [this]
  exact hp.comp_primrec hg

theorem pi0.comp_primrec_rightInverse {f : β → α} {g : α → β} (hg : Primrec g)
    (hfg : ∀ a, f (g a) = a) : pi0 n (p ∘ f) → pi0 n p := by
  intro hp
  have : p = (p ∘ f) ∘ g := funext fun a => by simp [hfg]
  rw [this]
  exact hp.comp_primrec hg

/-! Trivial (crossing) inclusions -/

theorem sigma0.of_pi0_succ (h : pi0 n p) : sigma0 (n + 1) p := by
  refine ⟨fun x ↦ p x.1, pi0.comp_primrec h (Primrec.fst), ?_⟩
  funext m
  simp

theorem pi0.of_sigma0_succ (h : sigma0 n p) : pi0 (n + 1) p := by
  refine ⟨fun x ↦ p x.1, sigma0.comp_primrec h (Primrec.fst), ?_⟩
  funext m
  simp

/-! Quantifier shifting -/

theorem pi0.of_forall_sigma01 {r : α → ℕ → Prop} (hp : sigma0 1 (fun (x : α × ℕ) ↦ r x.1 x.2)) :
    pi0 2 (fun x : α ↦ ∀ k, r x k) := by
  refine ⟨fun (x : α × ℕ) ↦ r x.1 x.2, ?_, rfl⟩
  exact sigma0.comp_primrec hp Primrec.id

theorem sigma0.of_exists_pi01 {r : α → ℕ → Prop} (hp : pi0 1 (fun (x : α × ℕ) ↦ r x.1 x.2)) :
    sigma0 2 (fun x : α ↦ ∃ k, r x k) := by
  refine ⟨fun (x : α × ℕ) ↦ r x.1 x.2, ?_, rfl⟩
  exact pi0.comp_primrec hp Primrec.id


/-! ## Helpers -/

/-! Primitive recursive helpers -/

theorem PrimrecPred.lt_pair : PrimrecPred (fun m : ℕ ↦ m.unpair.2 < m.unpair.1) := by
  have h_le : PrimrecRel (fun m k : ℕ ↦ k < m) :=
    Primrec.nat_lt.comp (Primrec.snd) (Primrec.fst)
  exact h_le.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem PrimrecPred.eq_const (k : ℕ) : PrimrecPred (fun n : ℕ ↦ n = k) :=
  Primrec.eq.comp (Primrec.id) (Primrec.const k)

theorem Primrec.pair_zero : Primrec (fun m : ℕ ↦ Nat.pair m 0) :=
  Primrec₂.natPair.comp Primrec.id (Primrec.const 0)

theorem Primrec.pair_swap : Primrec (fun m : ℕ ↦ pair m.unpair.2 m.unpair.1) :=
  Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair)

theorem Primrec.pair_unpair_repack :
    Primrec (fun m : ℕ ↦ pair m.unpair.1 (pair m.unpair.2 0)) :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))

theorem Primrec.pair_assoc_left :
    Primrec (fun m : ℕ ↦ pair (pair m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2) :=
  Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.unpair)
      (Primrec.comp (Primrec.fst) (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    (Primrec.comp (Primrec.snd) (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))

theorem Primrec.pair_assoc_right :
    Primrec (fun m : ℕ ↦ pair m.unpair.1.unpair.1 (pair m.unpair.1.unpair.2 m.unpair.2)) :=
  Primrec₂.natPair.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
    (Primrec₂.natPair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))

theorem PrimrecPred.forall_lt_pair {r : α → ℕ → Prop} {g : α → ℕ}
    (hr : PrimrecPred (fun x : α × ℕ ↦ r x.1 x.2)) (hg : Primrec g) :
    PrimrecPred (fun x : α ↦ ∀ k < g x, r x k) := by
  have hr' : PrimrecRel (fun (k : ℕ) (a : α) ↦ r a k) :=
    PrimrecPred.comp hr (Primrec.snd.pair Primrec.fst)
  have hmem : PrimrecPred (fun a : α ↦ ∀ k ∈ List.range (g a), r a k) :=
    PrimrecRel.comp (PrimrecRel.forall_mem_list hr') (Primrec.list_range.comp hg) Primrec.id
  refine PrimrecPred.of_eq hmem (fun a ↦ ?_)
  constructor
  · intro h k hk
    exact h k (List.mem_range.mpr hk)
  · intro h k hk
    exact h k (List.mem_range.mp hk)

/-! Finite-sequence coding (needed for sigma0.forall_lt_primrec) -/

/-- Finite-sequence decoder:
gives the `k`-th entry of the list coded by `seq` (with default `0`) -/
private def seqDecode (seq k : ℕ) : ℕ :=
  ((Encodable.decode (α := List ℕ) seq).getD []).getD k 0

private lemma primrec₂_seqDecode : Primrec₂ seqDecode :=
  (Primrec.list_getD 0).comp ( Primrec.option_getD.comp
    ( Primrec.decode.comp ( Primrec.fst ) ) ( Primrec.const [] ) ) ( Primrec.snd )

private lemma exists_seqDecode (m : ℕ) (w : ℕ → ℕ) :
    ∃ seq : ℕ, ∀ k < m, seqDecode seq k = w k := by
  unfold seqDecode
  use Encodable.encode (List.map w (List.range m))
  simp_all

private lemma bounded_collection {r : ℕ → ℕ → Prop} :
    (∀ m < n, ∃ k, r m k) ↔ ∃ seq : ℕ, ∀ m < n, r m (seqDecode seq m) := by
  constructor
  · intro h
    obtain ⟨seq, hseq⟩ := exists_seqDecode n (fun m ↦ if hm : m < n then (h m hm).choose else 0)
    refine ⟨seq, fun m hm ↦ ?_⟩
    simp_all [(h m hm).choose_spec]
  · intro ⟨seq, hseq⟩ m hm
    exact ⟨_, hseq m hm⟩


/-! ## Behavior under Boolean operators -/

/-! Negation duality -/

private lemma neg_aux :
    (sigma0 n p → pi0 n (fun x ↦ ¬(p x))) ∧
    (pi0 n p → sigma0 n (fun x ↦ ¬(p x))) := by
  induction n generalizing α p with
  | zero =>
    exact ⟨fun hp ↦ PrimrecPred.not hp, fun hp ↦ PrimrecPred.not hp⟩
  | succ n ih =>
    refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun x ↦ ¬(q x), ih.2 hq, ?_⟩
      funext x
      simp
    · obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨fun x ↦ ¬(q x), ih.1 hq, ?_⟩
      funext x
      simp

theorem pi0.iff_not_sigma0 : pi0 n p ↔ sigma0 n (fun x ↦ ¬(p x)) := by
  constructor
  · intro h
    exact neg_aux.2 h
  · intro h
    have := neg_aux.1 h
    simp_all

theorem sigma0.iff_not_pi0 : sigma0 n p ↔ pi0 n (fun x ↦ ¬(p x)) := by
  constructor
  · intro h
    exact neg_aux.1 h
  · intro h
    have := neg_aux.2 h
    simp_all

/-! Closure under conjunction and disjunction -/

private lemma bool_aux :
    (sigma0 n p → sigma0 n q → sigma0 n (fun x ↦ p x ∧ q x)) ∧
    (sigma0 n p → sigma0 n q → sigma0 n (fun x ↦ p x ∨ q x)) ∧
    (pi0 n p → pi0 n q → pi0 n (fun x ↦ p x ∧ q x)) ∧
    (pi0 n p → pi0 n q → pi0 n (fun x ↦ p x ∨ q x)) := by
  induction n generalizing α p q with
  | zero =>
    refine ⟨fun hp hq ↦ ?_,
            fun hp hq ↦ ?_,
            fun hp hq ↦ ?_,
            fun hp hq ↦ ?_⟩
    · exact PrimrecPred.and hp hq
    · exact PrimrecPred.or hp hq
    · exact PrimrecPred.and hp hq
    · exact PrimrecPred.or hp hq
  | succ n ih =>
    -- g₁ ⟨m, k⟩ = ⟨m, k.unpair.1⟩
    have g₁ : Primrec (fun x : α × ℕ ↦ (x.1, x.2.unpair.1)) :=
      Primrec.fst.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
    -- g₂ ⟨m, k⟩ = ⟨m, k.unpair.2⟩
    have g₂ : Primrec (fun x : α × ℕ ↦ (x.1, x.2.unpair.2)) :=
      Primrec.fst.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
    -- obtain ⟨ih_sigma_and, ih_sigma_or, ih_pi_and, ih_pi_or⟩ := ih
    · -- sigma0 n conjunction
      refine ⟨fun x ↦ q₁ (x.1, x.2.unpair.1) ∧
        q₂ (x.1, x.2.unpair.2), ?_, ?_⟩
      · exact ih.2.2.1 (pi0.comp_primrec hq₁ g₁) (pi0.comp_primrec hq₂ g₂)
      · funext m
        apply propext
        constructor
        · rintro ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩⟩
          refine ⟨pair k₁ k₂, ?_⟩
          simp_all
        · rintro ⟨k, hk⟩
          exact ⟨⟨k.unpair.1, hk.1⟩, ⟨k.unpair.2, hk.2⟩⟩
    · -- sigma0 n disjunction
      refine ⟨fun x ↦ q₁ x ∨ q₂ x, ih.2.2.2 hq₁ hq₂, ?_⟩
      funext x
      simp [exists_or]
    · -- pi0 n conjunction
      refine ⟨fun x ↦ q₁ x ∧ q₂ x, ih.1 hq₁ hq₂, ?_⟩
      funext x
      simp [forall_and]
    · -- pi0 n disjunction
      refine ⟨fun x ↦ q₁ (x.1, x.2.unpair.1) ∨
          q₂ (x.1, x.2.unpair.2), ?_, ?_⟩
      · exact ih.2.1 (sigma0.comp_primrec hq₁ g₁) (sigma0.comp_primrec hq₂ g₂)
      · funext m
        apply propext
        constructor
        · rintro (_ | _) _ <;> simp_all
        · intro h
          by_contra hc
          simp_all only [not_or, not_forall]
          obtain ⟨⟨a, _⟩, ⟨b, _⟩⟩ := hc
          have hv := h (pair a b)
          simp_all

theorem sigma0.and (hp : sigma0 n p) (hq : sigma0 n q) : sigma0 n (fun x ↦ p x ∧ q x) :=
  bool_aux.1 hp hq

theorem sigma0.or (hp : sigma0 n p) (hq : sigma0 n q) : sigma0 n (fun x ↦ p x ∨ q x) :=
  bool_aux.2.1 hp hq

theorem pi0.and (hp : pi0 n p) (hq : pi0 n q) : pi0 n (fun x ↦ p x ∧ q x) :=
  bool_aux.2.2.1 hp hq

theorem pi0.or (hp : pi0 n p) (hq : pi0 n q) : pi0 n (fun x ↦ p x ∨ q x) :=
  bool_aux.2.2.2 hp hq

theorem delta0.and (hp : delta0 n p) (hq : delta0 n q) : delta0 n (fun x ↦ p x ∧ q x) := by
  obtain ⟨hp_sigma, hp_pi⟩ := hp
  obtain ⟨hq_sigma, hq_pi⟩ := hq
  exact ⟨sigma0.and hp_sigma hq_sigma, pi0.and hp_pi hq_pi⟩

theorem delta0.or (hp : delta0 n p) (hq : delta0 n q) : delta0 n (fun x ↦ p x ∨ q x) := by
  obtain ⟨hp_sigma, hp_pi⟩ := hp
  obtain ⟨hq_sigma, hq_pi⟩ := hq
  exact ⟨sigma0.or hp_sigma hq_sigma, pi0.or hp_pi hq_pi⟩

theorem delta0.not (h : delta0 n p) : delta0 n (fun x ↦ ¬(p x)) := by
  obtain ⟨h_sigma, h_pi⟩ := h
  exact ⟨pi0.iff_not_sigma0.mp h_pi, sigma0.iff_not_pi0.mp h_sigma⟩

/-! Closure under finite unions and finite intersections -/

theorem sigma0.finset_union {k : ℕ} {f : Fin k → α → Prop} (hf : ∀ i, sigma0 n (f i)) :
    sigma0 n (fun x ↦ ∃ i, f i x) := by
  induction k with
  | zero =>
    have h_false : sigma0 n (fun _ : α ↦ False) :=
      sigma0.of_primrec (by
        refine PrimrecPred.of_eq (p := fun _ : α ↦ (0 : ℕ) = 1) ?_ ?_
        · exact Primrec.eq.comp (Primrec.const 0) (Primrec.const 1)
        · simp)
    have h_eq : (fun x : α ↦ ∃ i : Fin 0, f i x) = (fun _ : α ↦ False) := by simp_all
    simp_all
  | succ k ih =>
    have key : (fun x : α ↦ ∃ i : Fin (k + 1), f i x)
        = (fun x ↦ f 0 x ∨ ∃ i : Fin k, f i.succ x) := by
      funext x
      apply propext
      exact Fin.exists_fin_succ
    rw [key]
    exact sigma0.or (hf 0) (ih (fun i ↦ hf i.succ))

theorem sigma0.finset_inter {k : ℕ} {f : Fin k → α → Prop} (hf : ∀ i, sigma0 n (f i)) :
    sigma0 n (fun x ↦ ∀ i, f i x) := by
  induction k with
  | zero =>
    have h_true : sigma0 n (fun _ : α ↦ True) :=
      sigma0.of_primrec (by
        refine PrimrecPred.of_eq (p := fun _ : α ↦ (0 : ℕ) = 0) ?_ ?_
        · exact Primrec.eq.comp (Primrec.const 0) (Primrec.const 0)
        · simp)
    have h_eq : (fun x : α ↦ ∀ i : Fin 0, f i x) = (fun _ : α ↦ True) := by simp_all
    simp_all
  | succ k ih =>
    have key : (fun x : α ↦ ∀ i : Fin (k + 1), f i x)
        = (fun x ↦ f 0 x ∧ ∀ i : Fin k, f i.succ x) := by
      funext x
      apply propext
      exact Fin.forall_fin_succ
    rw [key]
    exact sigma0.and (hf 0) (ih (fun i ↦ hf i.succ))

theorem pi0.finset_union {k : ℕ} {f : Fin k → α → Prop} (hf : ∀ i, pi0 n (f i)) :
    pi0 n (fun x ↦ ∃ i, f i x) := by
  induction k with
  | zero =>
    have h_false : pi0 n (fun _ : α ↦ False) :=
      pi0.of_primrec (by
        refine PrimrecPred.of_eq (p := fun _ : α ↦ (0 : ℕ) = 1) ?_ ?_
        · exact Primrec.eq.comp (Primrec.const 0) (Primrec.const 1)
        · simp)
    have h_eq : (fun x : α ↦ ∃ i : Fin 0, f i x) = (fun _ : α ↦ False) := by simp_all
    simp_all
  | succ k ih =>
    have key : (fun x : α ↦ ∃ i : Fin (k + 1), f i x)
        = (fun x ↦ f 0 x ∨ ∃ i : Fin k, f i.succ x) := by
      funext x
      apply propext
      exact Fin.exists_fin_succ
    rw [key]
    exact pi0.or (hf 0) (ih (fun i ↦ hf i.succ))

theorem pi0.finset_inter {k : ℕ} {f : Fin k → α → Prop} (hf : ∀ i, pi0 n (f i)) :
    pi0 n (fun x ↦ ∀ i, f i x) := by
  induction k with
  | zero =>
    have h_true : pi0 n (fun _ : α ↦ True) :=
      pi0.of_primrec (by
        refine PrimrecPred.of_eq (p := fun _ : α ↦ (0 : ℕ) = 0) ?_ ?_
        · exact Primrec.eq.comp (Primrec.const 0) (Primrec.const 0)
        · simp)
    have h_eq : (fun x : α ↦ ∀ i : Fin 0, f i x) = (fun _ : α ↦ True) := by simp_all
    simp_all
  | succ k ih =>
    have key : (fun x : α ↦ ∀ i : Fin (k + 1), f i x)
        = (fun x ↦ f 0 x ∧ ∀ i : Fin k, f i.succ x) := by
      funext x
      apply propext
      exact Fin.forall_fin_succ
    rw [key]
    exact pi0.and (hf 0) (ih (fun i ↦ hf i.succ))

theorem delta0.finset_union {k : ℕ} {f : Fin k → α → Prop}
    (hf : ∀ i, delta0 n (f i)) :
    delta0 n (fun x ↦ ∃ i, f i x) :=
  ⟨sigma0.finset_union (fun i ↦ (hf i).1), pi0.finset_union (fun i ↦ (hf i).2)⟩

theorem delta0.finset_inter {k : ℕ} {f : Fin k → α → Prop}
    (hf : ∀ i, delta0 n (f i)) :
    delta0 n (fun x ↦ ∀ i, f i x) :=
  ⟨sigma0.finset_inter (fun i ↦ (hf i).1), pi0.finset_inter (fun i ↦ (hf i).2)⟩


/-! ## Closure under (bounded) quantifiers -/

/-! pi0 is closed under bounded universal quantification -/

theorem pi0.forall_lt_primrec {r : α → ℕ → Prop} {g : α → ℕ}
    (hr : pi0 n (fun (x : α × ℕ) ↦ r x.1 x.2))
    (hg : Primrec g) : pi0 n (fun x : α ↦ ∀ k < g x, r x k) := by
  induction n with
  | zero =>
    exact PrimrecPred.forall_lt_pair hr hg
  | succ n ih =>
    obtain ⟨q, hq, heq⟩ := hr
    -- pointwise description of s
    have h_key : ∀ a : α, ∀ c : ℕ, r a c ↔ ∀ t, q ((a, c), t) := by
      intro a c
      have := congrFun heq (a, c)
      simp_all
    refine ⟨fun x : α × ℕ ↦ ¬(x.2.unpair.1 < g x.1) ∨ q ((x.1, x.2.unpair.1), x.2.unpair.2), ?_, ?_⟩
    · -- show sigma0 n
      have hb : PrimrecPred (fun x : α × ℕ ↦ x.2.unpair.1 < g x.1) := by
        have h1 : Primrec (fun x : α × ℕ ↦ x.2.unpair.1) :=
          Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
        have h2 : Primrec (fun x : α × ℕ ↦ g x.1) := hg.comp Primrec.fst
        exact PrimrecRel.comp Primrec.nat_lt h1 h2
      exact sigma0.or (sigma0.of_primrec (PrimrecPred.not hb)) (sigma0.comp_primrec hq
        ((Primrec.fst.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).pair
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
    · -- show function equality
      funext m
      apply propext
      constructor
      · intro h v
        by_cases hv : v.unpair.1 < g m
        · right; simp_all
        · left; exact hv
      · intro h k hk
        rw [h_key m k]
        intro t
        have hv := h (pair k t)
        simp_all

theorem pi0.forall_lt {r : ℕ → ℕ → Prop} (hr : pi0 n (fun (x : ℕ × ℕ) ↦ r x.1 x.2)) :
    pi0 n (fun m ↦ ∀ k < m, r m k) :=
  pi0.forall_lt_primrec hr Primrec.id

/-! sigma0 is closed under bounded existential quantification -/

theorem sigma0.exists_lt_primrec {r : α → ℕ → Prop} {g : α → ℕ}
    (hr : sigma0 n (fun (x : α × ℕ) ↦ r x.1 x.2))
    (hg : Primrec g) : sigma0 n (fun x : α ↦ ∃ k < g x, r x k) := by
  -- use negation duality with pi0 and pi0.forall_lt_primrec
  have hs' : pi0 n (fun (x : α × ℕ) ↦ ¬(r x.1 x.2)) :=
    sigma0.iff_not_pi0.mp hr
  have hforall : pi0 n (fun x ↦ ∀ k < g x, ¬(r x k)) :=
    pi0.forall_lt_primrec (r := fun m k ↦ ¬(r m k)) hs' hg
  have heq : (fun x ↦ ∀ k < g x, ¬(r x k)) = (fun x : α ↦ ¬ ∃ k < g x, r x k) := by
    funext m
    apply propext
    constructor <;> simp_all
  simp_all [sigma0.iff_not_pi0]

theorem sigma0.exists_lt {r : ℕ → ℕ → Prop} (hr : sigma0 n (fun (x : ℕ × ℕ) ↦ r x.1 x.2)) :
    sigma0 n (fun m ↦ ∃ k < m, r m k) :=
  sigma0.exists_lt_primrec hr Primrec.id

/-! sigma0 is closed under bounded universal quantification -/

theorem sigma0.forall_lt_primrec {r : α → ℕ → Prop} {g : α → ℕ}
    (hr : sigma0 n (fun (x : α × ℕ) ↦ r x.1 x.2))
    (hg : Primrec g) : sigma0 n (fun x : α ↦ ∀ k < g x, r x k) := by
  induction n with
  | zero =>
    exact PrimrecPred.forall_lt_pair hr hg
  | succ n ih =>
    obtain ⟨q, hq, heq⟩ := hr
    -- pointwise description of s
    have h_key : ∀ a : α, ∀ c : ℕ, r a c ↔ ∃ t, q ((a, c), t) := by
      intro a c
      have := congrFun heq (a, c)
      simp_all
    have hg' : Primrec (fun m : ℕ ↦ pair (pair m.unpair.1.unpair.1 m.unpair.2)
          (seqDecode m.unpair.1.unpair.2 m.unpair.2)) :=
      Primrec₂.natPair.comp
        (Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair))
        (primrec₂_seqDecode.comp
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.snd.comp Primrec.unpair))
    refine ⟨fun x : α × ℕ ↦ ∀ k < g x.1, q ((x.1, k), (seqDecode x.2 k)), ?_, ?_⟩
    · -- show pi0 n
      have hf : Primrec (fun z : (α × ℕ) × ℕ ↦ ((z.1.1, z.2), seqDecode z.1.2 z.2)) :=
        ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair
          (primrec₂_seqDecode.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      exact pi0.forall_lt_primrec (pi0.comp_primrec hq hf) (hg.comp Primrec.fst)
    · -- show function equality
      funext x
      apply propext
      constructor
      · intro h
        have h' : ∀ k < g x, ∃ t, q ((x, k), t) :=
          fun k hk ↦ (h_key x k).mp (h k hk)
        obtain ⟨s, hs⟩ := bounded_collection.mp h'
        use s
      · rintro ⟨s, hs⟩ k hk
        rw [h_key x k]
        exact ⟨seqDecode s k, hs k hk⟩

theorem sigma0.forall_lt {r : ℕ → ℕ → Prop} (hr : sigma0 n (fun (x : ℕ × ℕ) ↦ r x.1 x.2)) :
    sigma0 n (fun m ↦ ∀ k < m, r m k) :=
  sigma0.forall_lt_primrec hr Primrec.id

/-! pi0 is closed under bounded existential quantification -/

theorem pi0.exists_lt_primrec {r : α → ℕ → Prop} {g : α → ℕ}
    (hr : pi0 n (fun (x : α × ℕ) ↦ r x.1 x.2))
    (hg : Primrec g) : pi0 n (fun x : α ↦ ∃ k < g x, r x k) := by
  -- use negation duality with sigma0 and sigma0.forall_lt_primrec
  have hs' : sigma0 n (fun (x : α × ℕ) ↦ ¬(r x.1 x.2)) :=
    pi0.iff_not_sigma0.mp hr
  have hforall : sigma0 n (fun x ↦ ∀ k < g x, ¬(r x k)) :=
    sigma0.forall_lt_primrec hs' hg
  have heq : (fun x ↦ ∀ k < g x, ¬(r x k)) = (fun x : α ↦ ¬ ∃ k < g x, r x k) := by
    funext x
    apply propext
    constructor <;> simp_all
  simp_all [sigma0.iff_not_pi0]

theorem pi0.exists_lt {r : ℕ → ℕ → Prop} (hr : pi0 n (fun (x : ℕ × ℕ) ↦ r x.1 x.2)) :
    pi0 n (fun m ↦ ∃ k < m, r m k) :=
  pi0.exists_lt_primrec hr Primrec.id

/-! delta0 is closed under bounded quantifiers -/

theorem delta0.exists_lt {r : ℕ → ℕ → Prop} (hr : delta0 n (fun (x : ℕ × ℕ) ↦ r x.1 x.2)) :
    delta0 n (fun m ↦ ∃ k < m, r m k) :=
  ⟨sigma0.exists_lt hr.1, pi0.exists_lt hr.2⟩

theorem delta0.forall_lt {r : ℕ → ℕ → Prop} (hr : delta0 n (fun (x : ℕ × ℕ) ↦ r x.1 x.2)) :
    delta0 n (fun m ↦ ∀ k < m, r m k) :=
  ⟨sigma0.forall_lt hr.1, pi0.forall_lt hr.2⟩

theorem delta0.exists_lt_primrec {r : α → ℕ → Prop} {g : α → ℕ}
    (hr : delta0 n (fun (x : α × ℕ) ↦ r x.1 x.2))
    (hg : Primrec g) : delta0 n (fun x : α ↦ ∃ k < g x, r x k) :=
  ⟨sigma0.exists_lt_primrec hr.1 hg, pi0.exists_lt_primrec hr.2 hg⟩

theorem delta0.forall_lt_primrec {r : α → ℕ → Prop} {g : α → ℕ}
    (hr : delta0 n (fun (x : α × ℕ) ↦ r x.1 x.2))
    (hg : Primrec g) : delta0 n (fun x : α ↦ ∀ k < g x, r x k) :=
  ⟨sigma0.forall_lt_primrec hr.1 hg, pi0.forall_lt_primrec hr.2 hg⟩

/-! sigma0 is closed under unbounded existential quantification -/

theorem sigma0.exists_succ {q : α × ℕ → Prop} (h : sigma0 (n + 1) q) :
    sigma0 (n + 1) (fun x ↦ ∃ k, q (x, k)) := by
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨fun x ↦ q ((x.1, x.2.unpair.1), x.2.unpair.2),
    pi0.comp_primrec hq ?_, ?_⟩
  · exact (Primrec.fst.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).pair
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  · funext m
    apply propext
    constructor
    · rintro ⟨k, k', hk'⟩
      refine ⟨pair k k', ?_⟩
      simp_all
    · rintro ⟨k, hk⟩
      exact ⟨k.unpair.1, k.unpair.2, hk⟩

/-! pi0 is closed under unbounded universal quantification -/

theorem pi0.forall_succ {q : α × ℕ → Prop} (h : pi0 (n + 1) q) :
    pi0 (n + 1) (fun x ↦ ∀ k, q (x, k)) := by
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨fun x ↦ q ((x.1, x.2.unpair.1), x.2.unpair.2),
    sigma0.comp_primrec hq ?_, ?_⟩
  · exact (Primrec.fst.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).pair
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  · funext m
    apply propext
    constructor
    · simp_all
    · intro hall k k'
      have := hall (pair k k')
      simpa using this


/-! ## Characterization of the first level -/

/-- `range f` of a `PFun f` is the set consisting of its range. -/
def range (f : α →. β) : β → Prop := fun x ↦ ∃ y, f y = some x

private lemma partrec_range_of_computable_range {p : α → Prop} :
    ((∀ x, ¬ p x) ∨ ∃ (f : ℕ → α), Computable f ∧ p = range (↑f : ℕ →. α)) →
      ∃ (f : ℕ →. α), Partrec f ∧ p = range f := by
  intro h
  cases h with
  | inl h =>
    refine ⟨fun _ ↦ Part.none, Partrec.none, ?_⟩
    funext x
    apply propext
    constructor
    · simp_all
    · rintro ⟨y, hy⟩
      simp_all
  | inr h =>
    obtain ⟨f, hf, hp⟩ := h
    exact ⟨↑f, hf.partrec, hp⟩

private lemma REPred_of_partrec_range {p : α → Prop} :
    (∃ (f : ℕ →. α), Partrec f ∧ p = range f) → REPred p := by
  rintro ⟨f, hf, rfl⟩
  have hf0 : Partrec (fun y ↦ (f y).map (Encodable.encode : α → ℕ)) :=
    hf.map (Computable.encode.comp Computable.snd).to₂
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf0)
  -- `g` is the (primitive recursive) searching function that on input `x (n1, n2)`
  -- outputs `0` if `evaln n2 c n1` outputs `x`, and outputs `none` otherwise
  set g : α → ℕ → Option ℕ :=
    fun x n ↦ if Nat.Partrec.Code.evaln n.unpair.2 c n.unpair.1 = some (Encodable.encode x)
      then some 0 else none with hg_def
  -- `evaln` is primitive recursive
  have h_evaln : Primrec (fun q : α × ℕ ↦
      Nat.Partrec.Code.evaln q.2.unpair.2 c q.2.unpair.1) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).pair (Primrec.const c)).pair
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
  have hg : Computable₂ g := by
    have h_prim : Primrec (fun q : α × ℕ ↦ g q.1 q.2) := by
      apply Primrec.ite ?_ (Primrec.const (some 0)) (Primrec.const none)
      exact Primrec.eq.comp h_evaln (Primrec.option_some.comp (Primrec.encode.comp Primrec.fst))
    exact h_prim.to_comp
  -- the domain of `fun x ↦ rfindOpt (g x)` is exactly the range of `f`.
  refine (Partrec.rfindOpt hg).dom_re.of_eq (fun x ↦ ?_)
  simp only [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨n, a, ha⟩
    by_cases hcond :
        Nat.Partrec.Code.evaln n.unpair.2 c n.unpair.1 = some (Encodable.encode x)
    · have h_mem : Encodable.encode x ∈ Nat.Partrec.Code.evaln n.unpair.2 c n.unpair.1 :=
        Option.mem_def.mpr hcond
      have h_ev := Nat.Partrec.Code.evaln_sound h_mem
      simp only [congrFun hc n.unpair.1, Part.mem_map_iff] at h_ev
      obtain ⟨b, hb, hbe⟩ := h_ev
      have h_bx : b = x := Encodable.encode_injective hbe
      subst h_bx
      refine ⟨n.unpair.1, ?_⟩
      simp only [Part.coe_some]
      exact Part.eq_some_iff.mpr hb
    · simp_all
  · rintro ⟨y, hy⟩
    have h_xmem : x ∈ f y := by
      simp only [hy, Part.coe_some]
      exact Part.mem_some x
    have h_enc_mem : Encodable.encode x ∈ (f y).map (Encodable.encode : α → ℕ) :=
      (Part.mem_map_iff Encodable.encode).mpr ⟨x, h_xmem, rfl⟩
    rw [← congrFun hc y] at h_enc_mem
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h_enc_mem
    refine ⟨Nat.pair y k, 0, ?_⟩
    simp_all

private lemma sigma01_of_REPred {p : α → Prop} : REPred p → sigma0 1 p := by
  intro hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨fun xk ↦ (evaln xk.2 c (Encodable.encode xk.1)).isSome = true, ?_, ?_⟩
  · -- the matrix is primitive recursive
    have h1 : Primrec (fun (xk : α × ℕ) ↦ evaln xk.2 c (Encodable.encode xk.1)) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (((Primrec.snd).pair (Primrec.const c)).pair (Primrec.encode.comp Primrec.fst))
    exact Primrec.eq.comp (Primrec.option_isSome.comp h1) (Primrec.const true)
  · -- `p x` holds iff the computation of `c` on `encode x` is defined
    funext x
    apply propext
    have hdom : p x ↔ (c.eval (Encodable.encode x)).Dom := by
      rw [hc]
      simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_Dom]
      constructor
      · intro h; exact ⟨h, trivial⟩
      · rintro ⟨h, _⟩; exact h
    simp only [hdom, Part.dom_iff_mem]
    constructor
    · rintro ⟨y, hy⟩
      simp only [Nat.Partrec.Code.evaln_complete] at hy
      obtain ⟨k, hk⟩ := hy
      refine ⟨k, ?_⟩
      simp_all
    · rintro ⟨k, hk⟩
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hk
      refine ⟨y, Nat.Partrec.Code.evaln_complete.mpr ⟨k, ?_⟩⟩
      simp_all

private lemma computable_range_of_sigma01 {p : α → Prop} :
    sigma0 1 p → (∀ x, ¬ p x) ∨ ∃ (f : ℕ → α), Computable f ∧ p = range (↑f : ℕ →. α) := by
  rintro ⟨q, ⟨hdec, hqp⟩, hp⟩
  by_cases hne : ∀ x, ¬ p x
  · left
    assumption
  · right
    push Not at hne
    obtain ⟨x0, hx0⟩ := hne
    -- construct the (computable) function f that on input x,
    -- outputs x if q (x.1 x.2) holds and outputs x0 otherwise
    let f0 := (fun x : α × ℕ ↦ if q x then x.1 else x0)
    let f1 := (fun n : ℕ ↦ Option.map f0 (Encodable.decode (α := α × ℕ) n))
    set f : ℕ → α := fun n ↦ (f1 n).getD x0 with hf
    have h_inner : Primrec f0 := by
      convert Primrec.ite ⟨hdec, hqp⟩ Primrec.fst (Primrec.const x0)
    have h_f1_prim : Primrec f1 :=
      Primrec.option_map Primrec.decode (h_inner.comp Primrec.snd)
    have h_f_prim : Primrec f :=
      Primrec.option_getD.comp h_f1_prim (Primrec.const x0)
    refine ⟨f, h_f_prim.to_comp, ?_⟩
    -- show that p = range ↑f
    funext x
    apply propext
    rw [hp]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨Encodable.encode (x, k), ?_⟩
      simp_all [f0, f1, f]
    · rintro ⟨y, hy⟩
      rw [PFun.coe_val] at hy
      replace hy : f y = x := Part.some_inj.mp hy
      rw [hp] at hx0
      simp only [hf, f1, f0] at hy
      cases hd : Encodable.decode (α := α × ℕ) y with
      | none =>
        simp_all
      | some ak =>
        rw [hd] at hy
        simp only [Option.map_some, Option.getD_some] at hy
        by_cases hqak : q ak
        · rw [if_pos hqak] at hy
          refine ⟨ak.2, ?_⟩
          rw [← hy]
          simpa using hqak
        · simp_all

theorem REPred_iff_exists_computable_range {p : α → Prop} :
    REPred p ↔ (∀ x, ¬ p x) ∨ ∃ (f : ℕ → α), Computable f ∧ p = range (↑f : ℕ →. α) :=
  ⟨fun h ↦ computable_range_of_sigma01 (sigma01_of_REPred h),
   fun h ↦ REPred_of_partrec_range (partrec_range_of_computable_range h)⟩

theorem REPred_iff_exists_partrec_range {p : α → Prop} :
    REPred p ↔ ∃ (f : ℕ →. α), Partrec f ∧ p = range f :=
  ⟨fun h ↦ partrec_range_of_computable_range (computable_range_of_sigma01 (sigma01_of_REPred h)),
   fun h ↦ REPred_of_partrec_range h⟩

theorem sigma0.one_iff_re : sigma0 1 p ↔ REPred p :=
  ⟨fun h ↦ REPred_of_partrec_range (partrec_range_of_computable_range
    (computable_range_of_sigma01 h)), fun h ↦ sigma01_of_REPred h⟩

theorem pi0.one_iff_co_re : pi0 1 p ↔ REPred (fun x ↦ ¬(p x)) := by
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


/-! ## Characterization of the graph of computable functions -/

/-- The graph of a partial function `f` is the set of all numbers coding pairs `(k,l)`
such that `f k = l` -/
def graph_of (f : ℕ →. ℕ) : (ℕ → Prop) := (fun m : ℕ ↦ f m.unpair.1 = Part.some m.unpair.2)

theorem sigma0.graph_of_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) : sigma0 1 (graph_of f) := by
  -- sigma0 1 coincides with REPred
  rw [sigma0.one_iff_re]
  have h_key : graph_of f = fun m ↦ (m.unpair.2 : ℕ) ∈ f m.unpair.1 := by
    funext m
    simp [graph_of, Part.eq_some_iff]
  rw [h_key]
  -- construct the partial recursive function g that halts on input m
  -- iff f(m.unpair.1) = m.unpair.2,
  -- i.e. iff the pair coded by m belongs to the graph of f
  let g : ℕ →. Unit := fun m ↦ (f m.unpair.1).bind
        (fun x ↦ if x = m.unpair.2 then Part.some () else Part.none)
  have hg : Partrec g := by
    have hf1 : Partrec (fun m : ℕ ↦ f m.unpair.1) :=
      (Partrec.nat_iff.mpr hf).comp (Computable.fst.comp Computable.unpair)
    have hf2 : PrimrecPred (fun x : ℕ × ℕ ↦ x.2 = x.1.unpair.2) := by
      exact Primrec.eq.comp Primrec.snd (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
    have hf3 : Computable (fun x : ℕ × ℕ ↦ decide (x.2 = x.1.unpair.2)) := hf2.decide.to_comp
    have hbranch : Partrec₂
        (fun (m1 m2 : ℕ) ↦ if m2 = m1.unpair.2 then Part.some () else Part.none) := by
      refine Partrec.of_eq (Partrec.cond hf3 (Partrec.const' (Part.some ())) Partrec.none)
        (fun x ↦ ?_)
      exact Bool.cond_decide (x.2 = x.1.unpair.2) (Part.some ()) Part.none
    exact Partrec.bind hf1 hbranch
  -- the graph of f equals the domain of g
  have h_dom : (fun m ↦ (m.unpair.2 : ℕ) ∈ f m.unpair.1) = fun m ↦ (g m).Dom := by
    funext m
    simp only [Part.bind_dom, eq_iff_iff, g]
    constructor
    · rintro ⟨hd, h_val⟩
      refine ⟨hd, ?_⟩
      simp_all
    · rintro ⟨hd, h_dom⟩
      by_cases h_val : (f m.unpair.1).get hd = m.unpair.2
      · rw [← h_val]
        exact Part.get_mem hd
      · rw [if_neg h_val] at h_dom
        exact h_dom.elim
  rw [h_dom]
  exact hg.dom_re

/-- There is a code of a function that halts exactly on the graph of f,
if `graph_of f` is `sigma0 1` -/
private lemma exists_code_of_graph {f : ℕ →. ℕ} (h : sigma0 1 (graph_of f)) :
    ∃ c : Nat.Partrec.Code, ∀ z, graph_of f z ↔ (Nat.Partrec.Code.eval c z).Dom := by
  have h_re : REPred (graph_of f) := Computability.sigma0.one_iff_re.mp h
  -- get a partial function `ℕ →. ℕ`
  have hf : Partrec (fun z ↦ Part.map (fun _ ↦ (0 : ℕ))
      (Part.assert (graph_of f z) fun _ ↦ Part.some ())) :=
    h_re.map (Computable.const (0 : ℕ)).to₂
  -- the domains are the same
  have h_fdom : ∀ x, graph_of f x ↔ (Part.map (fun _ ↦ (0 : ℕ))
      (Part.assert (graph_of f x) fun _ ↦ Part.some ())).Dom :=
    fun x ↦ ⟨fun hp ↦ ⟨hp, trivial⟩, fun hp ↦ hp.1⟩
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨c, fun x ↦ ?_⟩
  simp_all

/-- The search function used in the proof of `partrec_of_sigma01_graph` is partial recursive -/
private lemma rfindOpt_graph_partrec (c : Nat.Partrec.Code) :
    Nat.Partrec (fun m1 ↦ Nat.rfindOpt (fun m2 ↦
      (Nat.Partrec.Code.evaln m2.unpair.2 c (Nat.pair m1 m2.unpair.1)).map
        (fun _ ↦ m2.unpair.1))) := by
  rw [← Partrec.nat_iff]
  apply Partrec.rfindOpt
  apply Computable.option_map
  · have hprim : Primrec (fun x : ℕ × ℕ ↦
        Nat.Partrec.Code.evaln x.2.unpair.2 c (Nat.pair x.1 x.2.unpair.1)) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).pair (Primrec.const c)).pair
          (Primrec₂.natPair.comp Primrec.fst (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
    exact hprim.to_comp
  · exact Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))

/-- The search function used in the proof of `partrec_of_sigma01_graph` computes `f` -/
private lemma rfindOpt_graph_eq {f : ℕ →. ℕ} (c : Nat.Partrec.Code)
    (hc : ∀ z, graph_of f z ↔ (Nat.Partrec.Code.eval c z).Dom) (m : ℕ) :
      Nat.rfindOpt (fun k ↦ (Nat.Partrec.Code.evaln k.unpair.2 c (Nat.pair m k.unpair.1)).map
        (fun _ ↦ k.unpair.1)) = f m := by
  -- name the search function
  set g := fun k : ℕ ↦ (Nat.Partrec.Code.evaln k.unpair.2 c (Nat.pair m k.unpair.1)).map
    (fun _ ↦ k.unpair.1) with hg_def
  -- forward: any value found by the search lies in `f m`.
  have h_sound : ∀ l, l ∈ Nat.rfindOpt g → l ∈ f m := by
    intro l hmem
    obtain ⟨s, hs⟩ := Nat.rfindOpt_spec hmem
    obtain ⟨x, heval, hval⟩ := Option.mem_map.mp hs
    have hgraph : graph_of f (Nat.pair m s.unpair.1) :=
      (hc _).mpr (Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound heval⟩)
    rw [graph_of, Nat.unpair_pair, hval] at hgraph
    exact Part.eq_some_iff.mp hgraph
  -- backward: if a value lies in `f m`, the search will find it
  refine Part.ext fun l ↦ ⟨h_sound l, fun hmem ↦ ?_⟩
  have h_graph : graph_of f (Nat.pair m l) := by
    simp [graph_of, Part.eq_some_iff.mpr hmem]
  obtain ⟨x, heval⟩ := Part.dom_iff_mem.mp ((hc _).mp h_graph)
  obtain ⟨t, hstep⟩ := Nat.Partrec.Code.evaln_complete.mp heval
  have h_witness : l ∈ g (Nat.pair l t) := by simp_all
  obtain ⟨l', hl'⟩ := Part.dom_iff_mem.mp (Nat.rfindOpt_dom.mpr ⟨Nat.pair l t, l, h_witness⟩)
  exact Part.mem_unique (h_sound l' hl') hmem ▸ hl'

theorem partrec_of_sigma01_graph {f : ℕ →. ℕ} (h : sigma0 1 (graph_of f)) : Nat.Partrec f := by
  obtain ⟨c, hc⟩ := exists_code_of_graph h
  exact Nat.Partrec.of_eq (rfindOpt_graph_partrec c) (fun m ↦ rfindOpt_graph_eq c hc m)

theorem computable_iff_delta01_graph {f : ℕ → ℕ} : Computable f ↔ delta0 1 (graph_of f) := by
  constructor
  · intro hf
    refine delta0.one_iff_computable.mpr ?_
    have h1 : Computable (fun m : ℕ ↦ f m.unpair.1) :=
      hf.comp (Computable.fst.comp Computable.unpair)
    have h2 : Computable (fun m : ℕ ↦ m.unpair.2) := Computable.snd.comp Computable.unpair
    have h_eq : Computable₂ (fun a b : ℕ ↦ decide (a = b)) := Primrec.eq.decide.to_comp
    have h_comp : ComputablePred (fun m : ℕ ↦ f m.unpair.1 = m.unpair.2) :=
      ⟨inferInstance, h_eq.comp h1 h2⟩
    refine ComputablePred.of_eq h_comp (fun m ↦ ?_)
    change (f m.unpair.1 = m.unpair.2) ↔ ((↑f : ℕ →. ℕ) m.unpair.1 = Part.some m.unpair.2)
    simp_all
  · intro hd
    exact Partrec.nat_iff.mpr (partrec_of_sigma01_graph hd.1)


/-! ## Closure under computable substitution and many-one reducibility -/

/-! Closure under computable substitution -/

theorem sigma0.comp_computable {f : β → α} (hp : sigma0 (n + 1) p) (hf : Computable f) :
    sigma0 (n + 1) (fun x ↦ p (f x)) := by
  rcases isEmpty_or_nonempty α with _ | h
  · -- vacuous case
    haveI : IsEmpty β := Function.isEmpty f
    refine ⟨fun _ ↦ True, pi0.of_primrec ⟨inferInstance, Primrec.const true⟩, ?_⟩
    funext x
    exact isEmptyElim x
  · -- pick a default element `d : α`
    obtain ⟨d⟩ := h
    classical
    -- A: the graph relation `decode k = some (f x)`, is computable
    have ha_comp : Computable (fun y : β × ℕ ↦ decide (Encodable.decode y.2 = some (f y.1))) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Computable.decode.comp Computable.snd)
        (Computable.option_some.comp (hf.comp Computable.fst))
    have ha : ComputablePred (fun y : β × ℕ ↦ Encodable.decode y.2 = some (f y.1)) :=
      ⟨inferInstance, ha_comp⟩
    have ha_sigma : sigma0 (n + 1) (fun z : β × ℕ ↦ Encodable.decode z.2 = some (f z.1)) :=
      sigma0.of_computable (Nat.le_add_left 1 n) ha
    -- B: `p` applied to the decoded value, is `sigma0 (n + 1)`
    have hg_prim : Primrec (fun y : β × ℕ ↦ (Encodable.decode y.2 : Option α).getD d) :=
      Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const d)
    have hb_sigma : sigma0 (n + 1)
        (fun z : β × ℕ ↦ p ((Encodable.decode z.2 : Option α).getD d)) :=
      sigma0.comp_primrec hp hg_prim
    -- A ∧ B is equivalent to `p (f x)`
    have h_eq : (fun x ↦ p (f x)) = fun x : β ↦ ∃ k : ℕ,
        Encodable.decode k = some (f x) ∧ p ((Encodable.decode k : Option α).getD d) := by
      funext x
      apply propext
      constructor
      · intro _
        refine ⟨Encodable.encode (f x), ?_, ?_⟩ <;> simp_all
      · rintro ⟨k, hk, h_pk⟩
        simp_all
    rw [h_eq]
    -- A ∧ B is `sigma0 (n + 1)`
    exact sigma0.exists_succ (sigma0.and ha_sigma hb_sigma)

theorem pi0.comp_computable {f : β → α} (hp : pi0 (n + 1) p) (hf : Computable f) :
    pi0 (n + 1) (fun x ↦ p (f x)) :=
  have : sigma0 (n + 1) (fun x ↦ ¬ p (f x)) :=
    (sigma0.comp_computable (p := fun x : α ↦ ¬(p x)) (pi0.iff_not_sigma0.mp hp) hf)
  pi0.iff_not_sigma0.mpr this

theorem delta0.comp_computable {f : β → α} (hp : delta0 (n + 1) p) (hf : Computable f) :
    delta0 (n + 1) (fun x ↦ p (f x)) :=
  ⟨sigma0.comp_computable hp.1 hf, pi0.comp_computable hp.2 hf⟩

/-! Downward closure under many-one reducibility -/

theorem sigma0.of_manyOneReducible (hred : p ≤₀ q) (hq : sigma0 (n + 1) q) : sigma0 (n + 1) p := by
  obtain ⟨f, hf, hpq⟩ := hred
  have heq : p = fun x ↦ q (f x) := by
    funext x
    apply propext
    simp_all
  rw [heq]
  exact sigma0.comp_computable hq hf

theorem pi0.of_manyOneReducible (hred : p ≤₀ q) (hq : pi0 (n + 1) q) : pi0 (n + 1) p := by
  obtain ⟨f, hf, hpq⟩ := hred
  have heq : p = fun x ↦ q (f x) := by
    funext x
    apply propext
    simp_all
  rw [heq]
  exact pi0.comp_computable hq hf

theorem delta0.of_manyOneReducible (hred : p ≤₀ q) (hq : delta0 (n + 1) q) : delta0 (n + 1) p :=
  ⟨sigma0.of_manyOneReducible hred hq.1, pi0.of_manyOneReducible hred hq.2⟩


/-! ## Completeness -/

/-! Definitions and basic infrastructure -/

/-- A set is `sigma0 n`-complete if
(i) it is `sigma0 n`, and
(ii) every `sigma0 n` set many-one reduces to it -/
def sigma0Complete (n : ℕ) (p : α → Prop) : Prop := sigma0 n p ∧ ∀ q : ℕ → Prop, sigma0 n q → q ≤₀ p

/-- A set is `pi0 n`-complete if
(i) it is `pi0 n`, and
(ii) every `pi0 n` set many-one reduces to it -/
def pi0Complete (n : ℕ) (p : α → Prop) : Prop := pi0 n p ∧ ∀ q : ℕ → Prop, pi0 n q → q ≤₀ p

/-- A set is `sigma0 n`-hard if every `sigma0 n` set many-one reduces to it -/
def sigma0Hard (n : ℕ) (p : α → Prop) : Prop := ∀ q : ℕ → Prop, sigma0 n q → q ≤₀ p

/-- A set is `pi0 n`-hard if every `pi0 n` set many-one reduces to it -/
def pi0Hard (n : ℕ) (p : α → Prop) : Prop := ∀ q : ℕ → Prop, pi0 n q → q ≤₀ p

theorem sigma0Complete.iff_mem_hard : sigma0Complete n p ↔ sigma0 n p ∧ sigma0Hard n p := by rfl

theorem pi0Complete.iff_mem_hard : pi0Complete n p ↔ pi0 n p ∧ pi0Hard n p := by rfl

theorem sigma0Complete.mk (hmem : sigma0 n p) (hhard : sigma0Hard n p) : sigma0Complete n p :=
  ⟨hmem, hhard⟩

theorem pi0Complete.mk (hmem : pi0 n p) (hhard : pi0Hard n p) : pi0Complete n p :=
  ⟨hmem, hhard⟩

theorem sigma0Hard.of_manyOneReducible (hq : sigma0Hard n q) (hred : q ≤₀ p) : sigma0Hard n p :=
  fun q' hq' ↦ (hq q' hq').trans hred

theorem pi0Hard.of_manyOneReducible (hq : pi0Hard n q) (hred : q ≤₀ p) : pi0Hard n p :=
  fun q' hq' ↦ (hq q' hq').trans hred

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
  | 0     => fun m ↦ evaln 0 (ofNatCode m.unpair.1) m.unpair.2 ≠ none
  | 1     => fun m ↦ (eval (ofNatCode m.unpair.1) m.unpair.2).Dom
  | n + 2 => fun m ↦ ∃ k, haltingSetCompl (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 k))

def haltingSetCompl : ℕ → (ℕ → Prop)
  | 0     => fun m ↦ evaln 0 (ofNatCode m.unpair.1) m.unpair.2 = none
  | 1     => fun m ↦ ¬ (eval (ofNatCode m.unpair.1) m.unpair.2).Dom
  | n + 2 => fun m ↦ ∀ k, haltingSet (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 k))

end

@[simp]
theorem haltingSet_zero : haltingSet 0 = fun m ↦
    evaln 0 (ofNatCode m.unpair.1) m.unpair.2 ≠ none := rfl

@[simp]
theorem haltingSet_one : haltingSet 1 = fun m ↦
    (eval (ofNatCode m.unpair.1) m.unpair.2).Dom := rfl

@[simp]
theorem haltingSet_succ_succ (n : ℕ) : haltingSet (n + 2) = fun m ↦
      ∃ k, haltingSetCompl (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 k)) := rfl

@[simp]
theorem haltingSetCompl_zero : haltingSetCompl 0 = fun m ↦
    evaln 0 (ofNatCode m.unpair.1) m.unpair.2 = none := rfl

@[simp]
theorem haltingSetCompl_one : haltingSetCompl 1 = fun m ↦
    ¬(eval (ofNatCode m.unpair.1) m.unpair.2).Dom := rfl

@[simp]
theorem haltingSetCompl_succ_succ (n : ℕ) :
    haltingSetCompl (n + 2) = fun m ↦
      ∀ k, haltingSet (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 k)) := rfl

/-! Complementarity of haltingSet and haltingSetCompl -/

theorem haltingSet_compl (n : ℕ) (m : ℕ) : haltingSetCompl n m ↔ ¬(haltingSet n m) := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 =>
    simp only [haltingSetCompl_succ_succ, haltingSet_succ_succ, not_exists]
    refine forall_congr' fun k ↦ ?_
    have := haltingSet_compl (n + 1) (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 k))
    simp_all

/-! Membership in the halting set depends on the code only through eval -/

theorem haltingSet_eval_congr_both (c c' : ℕ) (h : eval (ofNatCode c) = eval (ofNatCode c')) :
    ∀ a : ℕ, (haltingSet (n + 1) (Nat.pair c a) ↔ haltingSet (n + 1) (Nat.pair c' a)) ∧
      (haltingSetCompl (n + 1) (Nat.pair c a) ↔ haltingSetCompl (n + 1) (Nat.pair c' a)) := by
  induction n with
  | zero =>
    simp_all
  | succ n ih =>
    intro _
    constructor <;> simp_all

theorem haltingSet_eval_congr (c c' : ℕ) (h : eval (ofNatCode c) = eval (ofNatCode c')) (m : ℕ) :
    haltingSet (n + 1) (Nat.pair c m) ↔ haltingSet (n + 1) (Nat.pair c' m) :=
  (haltingSet_eval_congr_both c c' h m).1

theorem haltingSetCompl_eval_congr (c c' : ℕ) (h : eval (ofNatCode c) = eval (ofNatCode c'))
    (m : ℕ) : haltingSetCompl (n + 1) (Nat.pair c m) ↔ haltingSetCompl (n + 1) (Nat.pair c' m) :=
  (haltingSet_eval_congr_both c c' h m).2

/-! Inclusion of halting set and its complement in the corresponding levels of the hierarchy -/

private lemma haltingSet_level : ∀ n, sigma0 n (haltingSet n) ∧ pi0 n (haltingSetCompl n)
  | 0 => by
    have h_code_primrec : Primrec (fun e : ℕ ↦ ofNatCode e) := by
      have h := Primrec.ofNat Nat.Partrec.Code
      rwa [Nat.Partrec.Code.ofNatCode_eq] at h
    have h_evaln_none : PrimrecPred
        (fun m : ℕ ↦ evaln 0 (ofNatCode m.unpair.1) m.unpair.2 = none) :=
      Primrec.eq.comp
        (Nat.Partrec.Code.primrec_evaln.comp
          (Primrec.pair (Primrec.pair (Primrec.const 0)
            (h_code_primrec.comp (Primrec.fst.comp Primrec.unpair)))
              (Primrec.snd.comp Primrec.unpair)))
        (Primrec.const none)
    refine ⟨?_, ?_⟩
    · rw [haltingSet_zero, sigma0.zero_iff]
      exact h_evaln_none.not
    · rw [haltingSetCompl_zero, pi0.zero_iff]
      exact h_evaln_none
  | 1 => by
    have h_code_comp : Computable (fun e : ℕ ↦ ofNatCode e) := by
      have h := (Primrec.ofNat Nat.Partrec.Code).to_comp
      simp_all [Nat.Partrec.Code.ofNatCode_eq]
    have h_eval_dom_re : REPred (fun z : ℕ ↦ (eval (ofNatCode z.unpair.1) z.unpair.2).Dom) :=
      (Nat.Partrec.Code.eval_part.comp (h_code_comp.comp (Computable.fst.comp Computable.unpair))
        (Computable.snd.comp Computable.unpair)).dom_re
    refine ⟨?_, ?_⟩
    · rw [haltingSet_one, sigma0.one_iff_re]
      simp_all
    · rw [pi0.iff_not_sigma0, sigma0.one_iff_re]
      simp_all
  | n + 2 => by
    have ih := haltingSet_level (n + 1)
    refine ⟨?_, ?_⟩
    · rw [sigma0.succ_eq]
      refine ⟨fun w : ℕ × ℕ ↦ haltingSetCompl (n + 1)
          (Nat.pair w.1.unpair.1 (Nat.pair w.1.unpair.2 w.2)), ?_, by simp_all⟩
      exact pi0.comp_primrec ih.2 Primrec.pair_assoc_right
    · rw [pi0.succ_eq]
      refine ⟨fun w : ℕ × ℕ ↦ haltingSet (n + 1)
          (Nat.pair w.1.unpair.1 (Nat.pair w.1.unpair.2 w.2)), ?_, by simp_all⟩
      exact sigma0.comp_primrec ih.1 Primrec.pair_assoc_right

theorem haltingSet_mem_sigma0 (n : ℕ) : sigma0 n (haltingSet n) := (haltingSet_level n).1
theorem haltingSetCompl_mem_pi0 (n : ℕ) : pi0 n (haltingSetCompl n) := (haltingSet_level n).2

/-! Completeness of the halting set and its complement for the first level -/

theorem haltingSet_one_sigma0_complete : sigma0Complete 1 (haltingSet 1) := by
  refine ⟨haltingSet_mem_sigma0 1, fun q hq ↦ ?_⟩
  rw [sigma0.one_iff_re] at hq
  obtain ⟨d, hd⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hq.map (Computable.const 0).to₂))
  refine ⟨fun m ↦ Nat.pair (Encodable.encode d) m, ?_, ?_⟩
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
  intro h
  apply ComputablePred.halting_problem 0
  have h_red : (fun c : Nat.Partrec.Code ↦ (eval c 0).Dom) ≤₀ haltingSet 1 := by
    refine ⟨fun c ↦ Nat.pair (Encodable.encode c) 0,
      (Primrec₂.natPair.comp Primrec.encode (Primrec.const 0)).to_comp, fun c ↦ ?_⟩
    have : ofNatCode (Encodable.encode c) = c := by
      rw [← Nat.Partrec.Code.ofNatCode_eq]
      exact Denumerable.ofNat_encode c
    simp_all
  exact ComputablePred.computable_of_manyOneReducible h_red h

theorem haltingSet_one_not_pi0_one : ¬(pi0 1 (haltingSet 1)) := by
  intro h
  apply haltingSet_one_not_computable
  rw [← delta0.one_iff_computable]
  exact ⟨haltingSet_mem_sigma0 1, h⟩

theorem ManyOneReducible.compl (h : p ≤₀ q) : (fun x ↦ ¬ p x) ≤₀ (fun x ↦ ¬ q x) := by
  obtain ⟨f, hf, hpq⟩ := h
  refine ⟨f, hf, ?_⟩
  simp_all

theorem haltingSetCompl_one_pi0_complete : pi0Complete 1 (haltingSetCompl 1) :=
  pi0Complete.mk (haltingSetCompl_mem_pi0 1) (fun q hq ↦ by
    simp_all only [pi0.iff_not_sigma0]
    obtain ⟨f, hf, h_compl_iff⟩ := haltingSet_one_sigma0_complete.2 (fun x ↦ ¬(q x)) hq
    refine ⟨f, hf, fun x ↦ ?_⟩
    rw [haltingSet_compl]
    rw [← h_compl_iff x, not_not])

theorem haltingSetCompl_one_not_computable : ¬(ComputablePred (haltingSetCompl 1)) := by
  intro h
  apply haltingSet_one_not_computable
  have : ComputablePred (fun x ↦ ¬ haltingSetCompl 1 x) := h.not
  simp_all

theorem haltingSetCompl_one_not_sigma0_one : ¬(sigma0 1 (haltingSetCompl 1)) := by
  intro h
  apply haltingSetCompl_one_not_computable
  rw [← delta0.one_iff_computable]
  exact ⟨h, haltingSetCompl_mem_pi0 1⟩

/-! Section completeness of the halting set -/

/-- Lemma used for the proof of `haltingSet_section_one`
(and thus indirectly for `haltingSet_section`) -/
private lemma sigma0_one_nat_section (q : ℕ → Prop) (hq : sigma0 1 q) :
    ∃ c : ℕ, ∀ x, q x ↔ haltingSet 1 (Nat.pair c x) := by
  rw [sigma0.one_iff_re] at hq
  have h_re_code : Partrec (fun x : ℕ ↦
      (Part.assert (q x) fun _ ↦ Part.some ()).map (fun _ ↦ (0 : ℕ))) :=
    hq.map (Computable.const 0).to₂
  obtain ⟨d, hd⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h_re_code)
  have h_code : ofNatCode (Encodable.encode d) = d := by
    rw [← Nat.Partrec.Code.ofNatCode_eq]
    exact Denumerable.ofNat_encode d
  refine ⟨Encodable.encode d, fun x ↦ ?_⟩
  rw [haltingSet_one]
  simp_all only [Nat.unpair_pair]
  constructor
  · intro h
    exact ⟨h, trivial⟩
  · intro h
    exact h.fst

/-- Lemma used for the proof of `haltingSet_section`, for the base case -/
private lemma haltingSet_section_one :
    (sigma0 1 q → ∃ k : ℕ, ∀ m, q m ↔ haltingSet 1 (Nat.pair k (Encodable.encode m))) ∧
    (pi0 1 q → ∃ k : ℕ, ∀ m, q m ↔ haltingSetCompl 1 (Nat.pair k (Encodable.encode m))) := by
  rcases isEmpty_or_nonempty α with _ | ⟨⟨d⟩⟩
  · exact ⟨fun _ ↦ ⟨0, fun m ↦ isEmptyElim m⟩, fun _ ↦ ⟨0, fun m ↦ isEmptyElim m⟩⟩
  · have hf_comp : Computable (fun m : ℕ ↦ (Encodable.decode m : Option α).getD d) :=
      (Primrec.option_getD.comp Primrec.decode (Primrec.const d)).to_comp
    have h_primrec_isSome : PrimrecPred (fun m : ℕ ↦ (Encodable.decode m : Option α).isSome) :=
      Primrec.eq.comp (Primrec.option_isSome.comp Primrec.decode) (Primrec.const true)
    constructor
    · intro hq
      have hq_sigma : sigma0 1 (fun m : ℕ ↦ q ((Encodable.decode m : Option α).getD d) ∧
            (Encodable.decode m : Option α).isSome = true) :=
        sigma0.and (sigma0.comp_computable hq hf_comp) (sigma0.of_primrec h_primrec_isSome)
      obtain ⟨c, hc⟩ := sigma0_one_nat_section _ hq_sigma
      refine ⟨c, fun m ↦ ?_⟩
      rw [← hc (Encodable.encode m)]
      simp
    · intro hq
      have hq_pi : pi0 1 (fun m : ℕ ↦ q ((Encodable.decode m : Option α).getD d) ∧
          (Encodable.decode m : Option α).isSome = true) :=
        pi0.and (pi0.comp_computable hq hf_comp) (pi0.of_primrec h_primrec_isSome)
      obtain ⟨c, hc⟩ := sigma0_one_nat_section
        (fun m ↦ ¬ (q ((Encodable.decode m : Option α).getD d) ∧
          (Encodable.decode m : Option α).isSome = true))
        (pi0.iff_not_sigma0.mp hq_pi)
      refine ⟨c, fun m ↦ ?_⟩
      rw [haltingSet_compl 1 (Nat.pair c (Encodable.encode m)), ← hc (Encodable.encode m)]
      simp

theorem haltingSet_section (q : α → Prop) :
    (sigma0 (n + 1) q → ∃ k : ℕ, ∀ m, q m ↔ haltingSet (n + 1)
      (Nat.pair k (Encodable.encode m))) ∧
    (pi0 (n + 1) q → ∃ k : ℕ, ∀ m, q m ↔ haltingSetCompl (n + 1)
      (Nat.pair k (Encodable.encode m))) := by
  induction n generalizing α q with
  | zero => exact haltingSet_section_one
  | succ n ih =>
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨k, hk⟩ := (ih r).2 hr
      refine ⟨k, fun m ↦ ?_⟩
      simp_all
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨k, hk⟩ := (ih r).1 hr
      refine ⟨k, fun m ↦ ?_⟩
      simp_all


/-! ## Completeness for higher levels -/

/-- Lemma used in the proof of `haltingSet_sigma_step` -/
private lemma haltingSetCompl_pad (hg : Computable g) : ∃ f : ℕ → ℕ, Computable f ∧
      ∀ m, (∃ k, haltingSetCompl (n + 1) (g (pair m k))) ↔ haltingSet (n + 2) (f m) := by
  have h_pi : pi0 (n + 1) (fun w ↦ haltingSetCompl (n + 1) (g w)) :=
    pi0.comp_computable (haltingSetCompl_mem_pi0 (n + 1)) hg
  have h_sigma : sigma0 (n + 2) (fun m ↦ ∃ k, haltingSetCompl (n + 1) (g (pair m k))) :=
    ⟨fun w : ℕ × ℕ ↦ haltingSetCompl (n + 1) (g (pair w.1 w.2)),
     h_pi.comp_primrec (Primrec₂.natPair.comp Primrec.fst Primrec.snd),
     funext fun x ↦ propext (exists_congr fun k ↦ by simp)⟩
  -- extract c from section completeness
  obtain ⟨c, hc⟩ :=
    (haltingSet_section (fun m ↦ ∃ k, haltingSetCompl (n + 1) (g (pair m k)))).1 h_sigma
  -- use `pair c m` as reduction function `f`
  exact ⟨fun m ↦ Nat.pair c m,
    (Primrec₂.natPair.comp (Primrec.const c) Primrec.id).to_comp, fun k ↦ hc k⟩

/-- Lemma used in the inductive step of the proof of `haltingSet_complete` -/
private lemma haltingSet_sigma_step (ih : pi0Complete (n + 1) (haltingSetCompl (n + 1)))
    {q : ℕ → Prop} (hq : sigma0 (n + 2) q) : q ≤₀ haltingSet (n + 2) := by
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℕ × ℕ → Prop, pi0 (n + 1) r ∧ q = fun m ↦ ∃ k, r (m, k) := hq
  obtain ⟨g, hg_comp, hg⟩ := ih.2 (fun z ↦ r z.unpair) (hr.comp_primrec Primrec.unpair)
  obtain ⟨f, hf_comp, hf⟩ := haltingSetCompl_pad hg_comp
  refine ⟨f, hf_comp, fun m ↦ ?_⟩
  rw [← hf m]
  refine exists_congr fun k ↦ ?_
  simpa [Nat.unpair_pair] using hg (Nat.pair m k)

/-- Lemma used in the inductive step of the proof of `haltingSet_complete` -/
private lemma haltingSet_pi_step (ih : sigma0Complete (n + 1) (haltingSet (n + 1)))
    {q : ℕ → Prop} (hq : pi0 (n + 2) q) : q ≤₀ haltingSetCompl (n + 2) := by
  have ih_compl : pi0Complete (n + 1) (haltingSetCompl (n + 1)) := by
    refine ⟨haltingSetCompl_mem_pi0 (n + 1), fun p hp ↦ ?_⟩
    have := ManyOneReducible.compl (ih.2 (fun m ↦ ¬(p m)) (pi0.iff_not_sigma0.mp hp))
    simp_all [← haltingSet_compl]
  have hred := ManyOneReducible.compl (haltingSet_sigma_step ih_compl (pi0.iff_not_sigma0.mp hq))
  simp_all [not_not, haltingSet_compl]

private lemma haltingSet_complete :
    sigma0Complete (n + 1) (haltingSet (n + 1)) ∧
    pi0Complete (n + 1) (haltingSetCompl (n + 1)) := by
  induction n with
  | zero => exact ⟨haltingSet_one_sigma0_complete, haltingSetCompl_one_pi0_complete⟩
  | succ n ih =>
    obtain ⟨ih_sigma, ih_pi⟩ := ih
    exact ⟨⟨haltingSet_mem_sigma0 _, fun _ ↦ haltingSet_sigma_step ih_pi⟩,
      ⟨haltingSetCompl_mem_pi0 _, fun _ ↦ haltingSet_pi_step ih_sigma⟩⟩

theorem haltingSet_sigma0_complete : sigma0Complete (n + 1) (haltingSet (n + 1)) :=
  haltingSet_complete.1

theorem haltingSetCompl_pi0_complete : pi0Complete (n + 1) (haltingSetCompl (n + 1)) :=
  haltingSet_complete.2


/-! ## Strictness of the hierarchy -/

/-! Basic strictness results -/

theorem haltingSet_succ_not_computable : ¬(ComputablePred (haltingSet (n + 1))) := by
  intro h
  apply haltingSet_one_not_computable
  have h_sigma : sigma0 (n + 1) (haltingSet 1) :=
    sigma0.mono_le (Nat.le_add_left 1 n) (haltingSet_mem_sigma0 1)
  exact ComputablePred.computable_of_manyOneReducible
    (haltingSet_sigma0_complete.2 (haltingSet 1) h_sigma) h

theorem haltingSet_not_pi0 : ¬(pi0 (n + 1) (haltingSet (n + 1))) := by
  intro h_pi
  let d := fun m ↦ ¬(haltingSet (n + 1) (Nat.pair m m))
  have h_pair : Primrec (fun m : ℕ ↦ Nat.pair m m) :=
    Primrec₂.natPair.comp Primrec.id Primrec.id
  have h_halt_pair : pi0 (n + 1) (fun m ↦ haltingSet (n + 1) (Nat.pair m m)) :=
    pi0.comp_primrec h_pi h_pair
  have h_sigma : sigma0 (n + 1) d := pi0.iff_not_sigma0.mp h_halt_pair
  obtain ⟨c, hc⟩ := (haltingSet_section d).1 h_sigma
  exact iff_not_self (hc c).symm

theorem haltingSetCompl_not_sigma0 : ¬(sigma0 (n + 1) (haltingSetCompl (n + 1))) := by
  intro h
  refine haltingSet_not_pi0 (n := n) ?_
  rw [pi0.iff_not_sigma0]
  convert h using 1
  ext x
  exact (haltingSet_compl (n + 1) x).symm

theorem exists_sigma0_not_pi0 : ∃ p : ℕ → Prop, sigma0 (n + 1) p ∧ ¬(pi0 (n + 1) p) :=
  ⟨haltingSet (n + 1), haltingSet_mem_sigma0 (n + 1), haltingSet_not_pi0⟩

theorem exists_pi0_not_sigma0 : ∃ p : ℕ → Prop, pi0 (n + 1) p ∧ ¬(sigma0 (n + 1) p) :=
  ⟨haltingSetCompl (n + 1), haltingSetCompl_mem_pi0 (n + 1), haltingSetCompl_not_sigma0⟩

theorem sigma0_strict : (∀ p : α → Prop, sigma0 n p → sigma0 (n + 1) p) ∧
    ¬(∀ p : ℕ → Prop, sigma0 (n + 1) p → sigma0 n p) := by
  refine ⟨fun p hp ↦ sigma0.mono_le (Nat.le_succ n) hp, ?_⟩
  intro h
  have h_sigma : sigma0 n (haltingSet (n + 1)) := h _ (haltingSet_mem_sigma0 (n + 1))
  exact haltingSet_not_pi0 (pi0.of_sigma0_succ h_sigma)

theorem pi0_strict : (∀ p : α → Prop, pi0 n p → pi0 (n + 1) p) ∧
    ¬(∀ p : ℕ → Prop, pi0 (n + 1) p → pi0 n p) := by
  refine ⟨fun p hp ↦ pi0.mono_le (Nat.le_succ n) hp, ?_⟩
  intro h
  have h_pi : pi0 n (haltingSetCompl (n + 1)) := h _ (haltingSetCompl_mem_pi0 (n + 1))
  exact haltingSetCompl_not_sigma0 (sigma0.of_pi0_succ h_pi)

theorem delta0_strict_sigma0 : ∃ p : ℕ → Prop, sigma0 (n + 1) p ∧ ¬(delta0 (n + 1) p) :=
  ⟨haltingSet (n + 1), haltingSet_mem_sigma0 (n + 1),
    fun ⟨_, h_pi⟩ ↦ haltingSet_not_pi0 h_pi⟩

theorem delta0_strict_pi0 : ∃ p : ℕ → Prop, pi0 (n + 1) p ∧ ¬(delta0 (n + 1) p) :=
  ⟨haltingSetCompl (n + 1), haltingSetCompl_mem_pi0 (n + 1),
    fun ⟨h_sigma, _⟩ ↦ haltingSetCompl_not_sigma0 h_sigma⟩

theorem sigma0_strict_delta0 : ∃ p : ℕ → Prop, sigma0 (n + 1) p ∧ ¬(delta0 n p) :=
  ⟨haltingSet (n + 1), haltingSet_mem_sigma0 (n + 1), fun ⟨_, h_pi⟩ ↦
    haltingSet_not_pi0 (pi0.mono_le (Nat.le_succ n) h_pi)⟩

theorem pi0_strict_delta0 : ∃ p : ℕ → Prop, pi0 (n + 1) p ∧ ¬(delta0 n p) :=
  ⟨haltingSetCompl (n + 1), haltingSetCompl_mem_pi0 (n + 1), fun ⟨h_sigma, _⟩ ↦
    haltingSetCompl_not_sigma0 (sigma0.mono_le (Nat.le_succ n) h_sigma)⟩

/-! Strictness in terms of (inclusions for) sets of sets -/

theorem sigma0_subset_sigma0_succ : {p : ℕ → Prop | sigma0 n p} ⊆ {p | sigma0 (n + 1) p} :=
  fun _ hp ↦ sigma0.mono_le (Nat.le_succ n) hp

theorem pi0_subset_pi0_succ : {p : ℕ → Prop | pi0 n p} ⊆ {p | pi0 (n + 1) p} :=
  fun _ hp ↦ pi0.mono_le (Nat.le_succ n) hp

theorem sigma0_proper_subset : {p : ℕ → Prop | sigma0 n p} ⊂ {p | sigma0 (n + 1) p} := by
  rw [Set.ssubset_iff_of_subset sigma0_subset_sigma0_succ]
  refine ⟨haltingSet (n + 1), haltingSet_mem_sigma0 (n + 1), ?_⟩
  intro h
  exact haltingSet_not_pi0 (pi0.of_sigma0_succ h)

theorem pi0_proper_subset : {p : ℕ → Prop | pi0 n p} ⊂ {p | pi0 (n + 1) p} := by
  rw [Set.ssubset_iff_of_subset pi0_subset_pi0_succ]
  refine ⟨haltingSetCompl (n + 1), haltingSetCompl_mem_pi0 (n + 1), ?_⟩
  intro h
  exact haltingSetCompl_not_sigma0 (sigma0.of_pi0_succ h)

/-! Level collapse characterizations -/

theorem sigma0_subset_pi0_iff_collapse : (∀ p : α → Prop, sigma0 n p → pi0 n p) ↔
    (∀ p : α → Prop, sigma0 n p ↔ pi0 n p) := by
  constructor
  · intro h p
    refine ⟨h p, ?_⟩
    intro h_pi
    have : sigma0 n (fun x => ¬(p x)) := pi0.iff_not_sigma0.mp h_pi
    have : pi0 n (fun x => ¬(p x)) := h _ this
    have : sigma0 n (fun x => ¬¬(p x)) := pi0.iff_not_sigma0.mp this
    have h_eq : (fun x => ¬¬(p x)) = p := funext fun x => propext not_not
    simp_all
  · intro h p hp
    exact (h p).mp hp

theorem pi0_subset_sigma0_iff_collapse : (∀ p : α → Prop, pi0 n p → sigma0 n p) ↔
    (∀ p : α → Prop, sigma0 n p ↔ pi0 n p) := by
  constructor
  · intro h p
    refine ⟨?_, h p⟩
    intro h_sigma
    have : pi0 n (fun x => ¬(p x)) := sigma0.iff_not_pi0.mp h_sigma
    have : sigma0 n (fun x => ¬(p x)) := h _ this
    have : pi0 n (fun x => ¬¬(p x)) := sigma0.iff_not_pi0.mp this
    have h_eq : (fun x => ¬¬(p x)) = p := funext fun x => propext not_not
    simp_all
  · intro h p hp
    exact (h p).mpr hp

private lemma collapse_sigma_pi_nat_iff_alpha (e : ℕ ≃ α) (he : Primrec e) (he' : Primrec e.symm) :
    (∀ p : ℕ → Prop, sigma0 n p → pi0 n p) ↔ (∀ p : α → Prop, sigma0 n p → pi0 n p) := by
  constructor
  · intro h p hp
    have : sigma0 n (fun m : ℕ ↦ p (e m)) := sigma0.comp_primrec hp he
    have : pi0 n (fun m : ℕ ↦ p (e m)) := h _ this
    have : pi0 n (fun a : α ↦ p (e (e.symm a))) :=
      pi0.comp_primrec (p := fun m : ℕ ↦ p (e m)) this he'
    simp_all
  · intro h p hp
    have : sigma0 n (fun a : α ↦ p (e.symm a)) := sigma0.comp_primrec hp he'
    have : pi0 n (fun a : α ↦ p (e.symm a)) := h _ this
    have : pi0 n (fun m : ℕ ↦ p (e.symm (e m))) :=
      pi0.comp_primrec (p := fun a : α ↦ p (e.symm a)) this he
    simp_all

private lemma collapse_pi_sigma_nat_iff_alpha (e : ℕ ≃ α) (he : Primrec e) (he' : Primrec e.symm) :
    (∀ p : ℕ → Prop, pi0 n p → sigma0 n p) ↔ (∀ p : α → Prop, pi0 n p → sigma0 n p) := by
  constructor
  · intro h p hp
    have : pi0 n (fun m : ℕ ↦ p (e m)) := pi0.comp_primrec hp he
    have : sigma0 n (fun m : ℕ ↦ p (e m)) := h _ this
    have : sigma0 n (fun a : α ↦ p (e (e.symm a))) :=
      sigma0.comp_primrec (p := fun m : ℕ ↦ p (e m)) this he'
    simp_all
  · intro h p hp
    have : pi0 n (fun a : α ↦ p (e.symm a)) := pi0.comp_primrec hp he'
    have : sigma0 n (fun a : α ↦ p (e.symm a)) := h _ this
    have : sigma0 n (fun m : ℕ ↦ p (e.symm (e m))) :=
      sigma0.comp_primrec (p := fun a : α ↦ p (e.symm a)) this he
    simp_all

theorem sigma0_subset_pi0_iff_collapse' (e : ℕ ≃ α) (he : Primrec e) (he' : Primrec e.symm) :
    (∀ p : ℕ → Prop, sigma0 n p → pi0 n p) ↔ (∀ p : α → Prop, sigma0 n p ↔ pi0 n p) :=
  (collapse_sigma_pi_nat_iff_alpha e he he').trans sigma0_subset_pi0_iff_collapse

theorem pi0_subset_sigma0_iff_collapse' (e : ℕ ≃ α) (he : Primrec e) (he' : Primrec e.symm) :
    (∀ p : ℕ → Prop, pi0 n p → sigma0 n p) ↔ (∀ p : α → Prop, sigma0 n p ↔ pi0 n p) :=
  (collapse_pi_sigma_nat_iff_alpha e he he').trans pi0_subset_sigma0_iff_collapse


/-! Inseparability of haltingSet and haltingSetCompl by delta0 sets -/

theorem haltingSet_inseparable : ¬(∃ q : ℕ → Prop, delta0 (n + 1) q ∧
    (∀ m, haltingSet (n + 1) m → q m) ∧
    (∀ m, haltingSetCompl (n + 1) m → ¬(q m))) := by
  rintro ⟨c, hc_delta0, hq_covers_halt, hq_excludes_compl⟩
  have : haltingSet (n + 1) = c := by
    funext x
    apply propext
    refine ⟨hq_covers_halt x, ?_⟩
    intro h_cx
    by_contra hx_not_halt
    exact hq_excludes_compl x ((haltingSet_compl (n + 1) x).mpr hx_not_halt) h_cx
  have h_halt_delta0 : delta0 (n + 1) (haltingSet (n + 1)) := by simp_all
  exact haltingSet_not_pi0 h_halt_delta0.2


/-! ## Kleene normal form -/

/-! Auxiliary definitions and basic results -/

/-- Explicit quantifier alternation -/
def altQ : Bool → ℕ → (ℕ → Prop) → Prop
  | true,  0,     P => ∃ s, P s
  | false, 0,     P => ∀ s, ¬ P s
  | true,  n + 1, P => ∃ k, altQ false n (fun s ↦ P (Nat.pair k s))
  | false, n + 1, P => ∀ k, altQ true  n (fun s ↦ P (Nat.pair k s))

@[simp]
theorem altQ_true_zero {p : ℕ → Prop} : altQ true 0 p = ∃ k, p k := rfl

@[simp]
theorem altQ_false_zero {p : ℕ → Prop} : altQ false 0 p = ∀ k, ¬(p k) := rfl

@[simp]
theorem altQ_true_succ {p : ℕ → Prop} :
    altQ true (n + 1) p = ∃ k, altQ false n (fun m ↦ p (Nat.pair k m)) := rfl

@[simp]
theorem altQ_false_succ {p : ℕ → Prop} :
    altQ false (n + 1) p = ∀ k, altQ true n (fun m ↦ p (Nat.pair k m)) := rfl

theorem altQ_congr {p q : ℕ → Prop} (b : Bool) (h : ∀ m, p m ↔ q m) :
    altQ b n p ↔ altQ b n q := by
  induction n generalizing b p q with
  | zero =>
    cases b with
    | true => exact exists_congr fun m ↦ h m
    | false => exact forall_congr' fun m ↦ not_congr (h m)
  | succ n ih =>
    cases b with
    | true =>
      simp only [altQ_true_succ]
      exact exists_congr fun m ↦ ih false fun k ↦ h (Nat.pair m k)
    | false =>
      simp only [altQ_false_succ]
      exact forall_congr' fun m ↦ ih true fun k ↦ h (Nat.pair m k)

/-! Auxiliary functions -/

private def kleene_matrix (m : ℕ) : Option ℕ := evaln (m.unpair.2.unpair.2) (ofNatCode m.unpair.1)
    (m.unpair.2.unpair.1)

theorem kleene_matrix_primrec : PrimrecPred (fun m ↦ kleene_matrix m ≠ none) := by
  have h_prim_code : Primrec (fun e : ℕ => ofNatCode e) := by
    have h := Primrec.ofNat Nat.Partrec.Code; rwa [Nat.Partrec.Code.ofNatCode_eq] at h
  have h_prim : Primrec (fun m : ℕ =>
      (evaln m.unpair.2.unpair.2 (ofNatCode m.unpair.1) m.unpair.2.unpair.1).isSome) :=
    Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
            (h_prim_code.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
  refine PrimrecPred.of_eq (p := fun m => (evaln m.unpair.2.unpair.2 (ofNatCode m.unpair.1)
    m.unpair.2.unpair.1).isSome = true) ?_ ?_
  · exact Primrec.eq.comp h_prim (Primrec.const true)
  · intro w
    simp [Option.isSome_iff_ne_none, kleene_matrix]

private def kleene_repack (m : ℕ) : ℕ := Nat.pair (m.unpair.1) (Nat.pair
    (Nat.pair m.unpair.2.unpair.1 m.unpair.2.unpair.2.unpair.1) m.unpair.2.unpair.2.unpair.2)

theorem kleene_repack_primrec : Primrec kleene_repack := by
  have hprim_code : Primrec (fun m : ℕ => m.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hprim_input : Primrec (fun m : ℕ => m.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hprim_steps : Primrec (fun m : ℕ => m.unpair.2.unpair.2.unpair.1) :=
    Primrec.fst.comp
      (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hprim_rest : Primrec (fun m : ℕ => m.unpair.2.unpair.2.unpair.2) :=
    Primrec.snd.comp
      (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  exact Primrec₂.natPair.comp hprim_code
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp hprim_input hprim_steps) hprim_rest)

/-! Kleene normal forms for haltingSet and haltingSetCompl -/

theorem Code.dom_iff_evaln (c : Nat.Partrec.Code) (m : ℕ) :
    (eval c m).Dom ↔ ∃ s, evaln s c m ≠ none := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp h
    rw [evaln_complete] at hk
    obtain ⟨s, hs⟩ := hk
    exact ⟨s, Option.ne_none_iff_exists.mpr ⟨k, (Option.mem_def.mp hs).symm⟩⟩
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists.mp hs
    apply Part.dom_iff_mem.mpr
    exact ⟨k, evaln_sound (Option.mem_def.mpr hk.symm)⟩

private lemma kleene_normal_form : ∃ r, PrimrecPred r ∧
    (∀ m k, haltingSet (n + 1) (Nat.pair m k) ↔
      altQ true n (fun l ↦ r (Nat.pair m (Nat.pair k l)))) ∧
    (∀ m k, haltingSetCompl (n + 1) (Nat.pair m k) ↔
      altQ false n (fun l ↦ r (Nat.pair m (Nat.pair k l)))) := by
  induction n with
  | zero =>
    refine ⟨fun m ↦ evaln m.unpair.2.unpair.2 (ofNatCode m.unpair.1) m.unpair.2.unpair.1 ≠ none,
      kleene_matrix_primrec, ?_, ?_⟩ <;> intros <;> simp_all [Code.dom_iff_evaln]
  | succ n ih =>
    obtain ⟨r, hr, h_halt, h_halt_compl⟩ := ih
    refine ⟨fun m ↦ r (Nat.pair m.unpair.1
        (Nat.pair (Nat.pair m.unpair.2.unpair.1 m.unpair.2.unpair.2.unpair.1)
          m.unpair.2.unpair.2.unpair.2)),
            hr.comp kleene_repack_primrec, ?_, ?_⟩
    · intro c m
      simp_all [haltingSet_succ_succ]
    · intro c a
      simp_all [haltingSetCompl_succ_succ]

theorem haltingSet_kleene_nf : ∃ r, PrimrecPred r ∧ (∀ m k, haltingSet (n + 1) (Nat.pair m k) ↔
    altQ true n (fun l ↦ r (Nat.pair m (Nat.pair k l)))) := by
  obtain ⟨r, hr, hk, _⟩ := kleene_normal_form
  exact ⟨r, hr, hk⟩

theorem haltingSetCompl_kleene_nf : ∃ r, PrimrecPred r ∧ (∀ m k, haltingSetCompl (n + 1)
    (Nat.pair m k) ↔ altQ false n (fun l ↦ r (Nat.pair m (Nat.pair k l)))) := by
  obtain ⟨r, hr, _, hk⟩ := kleene_normal_form
  exact ⟨r, hr, hk⟩

private lemma kleene_normal_form_unpair : ∃ r, PrimrecPred r ∧
    (∀ m, haltingSet (n + 1) m ↔
      altQ true n (fun l ↦ r (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 l)))) ∧
    (∀ m, haltingSetCompl (n + 1) m ↔
      altQ false n (fun l ↦ r (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 l)))) := by
  obtain ⟨r, hr, h_halt, h_halt_compl⟩ := kleene_normal_form
  refine ⟨r, hr, ?_, ?_⟩
  · intro m
    have h := h_halt m.unpair.1 m.unpair.2
    rwa [Nat.pair_unpair] at h
  · intro m
    have h := h_halt_compl m.unpair.1 m.unpair.2
    rwa [Nat.pair_unpair] at h

theorem haltingSet_kleene_nf_unpair : ∃ r, PrimrecPred r ∧ (∀ m, haltingSet (n + 1) m ↔
    altQ true n (fun l ↦ r (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 l)))) := by
  obtain ⟨r, hr, hk, _⟩ := kleene_normal_form_unpair
  exact ⟨r, hr, hk⟩

theorem haltingSetCompl_kleene_nf_unpair : ∃ r, PrimrecPred r ∧ (∀ m, haltingSetCompl (n + 1) m ↔
      altQ false n (fun l ↦ r (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 l)))) := by
  obtain ⟨r, hr, _, hk⟩ := kleene_normal_form_unpair
  exact ⟨r, hr, hk⟩


/-! ## Rice's theorem -/

def extensional (p : (α →. β) → Prop) : Prop := ∀ f g : α →. β, (∀ x, f x = g x) → (p f ↔ p g)

def nontrivial (p : (α →. β) → Prop) : Prop :=
  (∃ f : α →. β, Partrec f ∧ p f) ∧ (∃ g : α →. β, Partrec g ∧ ¬(p g))

/-- `evalIndex e` is the partial function `α →. β` computed by the program with index `e` -/
noncomputable def evalIndex (e : ℕ) : α →. β :=
  fun a ↦ (eval (ofNatCode e) (Encodable.encode a)).bind
    (fun m ↦ ((Encodable.decode m : Option β) : Part β))

/-- `propIndex p e` is the property `p` lifted to program indices. -/
def propIndex (p : (α →. β) → Prop) (e : ℕ) : Prop := p (evalIndex e)

/-- Any partial computable function `f : α →. β` can be uniformly encoded.
Used in the proof of `rice_reduce`. -/
private lemma rice_smn (f : α →. β) (hf : Partrec f) :
    ∃ h : ℕ → ℕ, Computable h ∧ ∀ (m : ℕ) (k : α), evalIndex (h m) k
      = (eval (ofNatCode m.unpair.1) m.unpair.2).bind (fun _ ↦ f k) := by
  have h_decode : Computable (fun m : ℕ ↦ ofNatCode m) := by
    rw [← Nat.Partrec.Code.ofNatCode_eq]
    exact Computable.ofNat Nat.Partrec.Code
  let univ : ℕ →. ℕ := fun m ↦ eval (ofNatCode m.unpair.1) m.unpair.2
  have h_univ : Partrec univ :=
    Nat.Partrec.Code.eval_part.comp
      (h_decode.comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp Computable.unpair)
  let fpart : ℕ →. ℕ :=
    fun m ↦ ((Encodable.decode m : Option α) : Part α).bind (fun a ↦ (f a).map Encodable.encode)
  have h_fpart : Partrec fpart := Partrec.nat_iff.mpr hf
  have hg : Partrec (fun m : ℕ ↦
      (univ m.unpair.1).bind (fun _ ↦ fpart m.unpair.2)) := by
    apply Partrec.bind
    · exact h_univ.comp (Computable.fst.comp Computable.unpair)
    · exact h_fpart.comp (Computable.snd.comp (Computable.unpair.comp Computable.fst))
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hg)
  let h : ℕ → ℕ := fun m ↦ Encodable.encode (Nat.Partrec.Code.curry c m)
  refine ⟨h, ?_, ?_⟩
  · exact Computable.encode.comp
      ((Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const c) Primrec.id).to_comp)
  · intro m k
    have h_code : ofNatCode (h m) = Nat.Partrec.Code.curry c m := by
      rw [← Nat.Partrec.Code.ofNatCode_eq]
      exact Denumerable.ofNat_encode _
    have h_round : ((f k).map Encodable.encode).bind
        (fun m ↦ ((Encodable.decode m : Option β) : Part β)) = f k := by simp_all
    change (eval (ofNatCode (h m)) (Encodable.encode k)).bind
        (fun m ↦ ((Encodable.decode m : Option β) : Part β)) = (univ m).bind (fun _ ↦ f k)
    simp_all [fpart, Part.bind_assoc]

/-- If `p` holds of some computable `f` but not of the everywhere-undefined function,
then the halting set many-one reduces to `propIndex p`. -/
private lemma rice_reduce (p : (α →. β) → Prop) (h_ext : extensional p)
    (f : α →. β) (hf : Partrec f) (hpf : p f) (_ : ¬(p (fun _ ↦ Part.none))) :
    haltingSet 1 ≤₀ propIndex p := by
  obtain ⟨h, hh, heq⟩ := rice_smn f hf
  refine ⟨h, hh, fun m ↦ ?_⟩
  rw [haltingSet_one]
  by_cases hm : (eval (ofNatCode m.unpair.1) m.unpair.2).Dom
  · have h_agree : ∀ k, evalIndex (h m) k = f k := fun k ↦ by
      rw [heq m k, ← Part.some_get hm, Part.bind_some]
    have : propIndex p (h m) ↔ p f := by
      unfold propIndex
      exact h_ext _ _ h_agree
    simp_all
  · have h_agree : ∀ k, evalIndex (h m) k = (fun _ : α ↦ Part.none) k := fun k ↦ by
      rw [heq m k, Part.eq_none_iff'.mpr hm, Part.bind_none]
    have : propIndex p (h m) ↔ p (fun _ ↦ Part.none) := by
      unfold propIndex
      exact h_ext _ _ h_agree
    simp_all

/-- Rice's theorem: no nontrivial extensional property of partial computable functions
`α →. β` is decidable. -/
theorem rice (p : (α →. β) → Prop) (h_ext : extensional p) (h_nontriv : nontrivial p) :
    ¬(ComputablePred (propIndex p)) := by
  intro h_comp
  by_cases hp_bot : p (fun _ : α ↦ Part.none)
  · -- `rice_reduce` applies to the complement
    obtain ⟨f, hf, hpf⟩ := h_nontriv.2
    have h_ext' : extensional (fun f ↦ ¬(p f)) :=
      fun f g hfg ↦ not_congr (h_ext f g hfg)
    have h_red := rice_reduce _ h_ext' f hf hpf (by simpa using hp_bot)
    have h_halt_comp : ComputablePred (haltingSet 1) :=
      ComputablePred.computable_of_manyOneReducible h_red
        (h_comp.not.of_eq (fun _ ↦ by simp [propIndex]))
    exact haltingSet_one_not_computable h_halt_comp
  · -- `rice_reduce` applies directly
    obtain ⟨f, hf, hpf⟩ := h_nontriv.1
    exact haltingSet_one_not_computable
      (ComputablePred.computable_of_manyOneReducible (rice_reduce p h_ext f hf hpf hp_bot) h_comp)


end Computability
