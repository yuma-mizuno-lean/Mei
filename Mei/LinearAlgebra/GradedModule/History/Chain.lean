/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.DirectSum.Map
public import Mei.Algebra.DirectSum.Component
public import TauCeti.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Homogeneous histories along chains of decomposed modules

A *chain* is a finite sequence of linear maps `T j : M (j + 1) → M j` between
modules with their own internal direct-sum decompositions `ℳ k : ι k → Submodule R (M k)`.
The degree types may differ from one module to the next. Index zero is the final
operation, so `chainComp T = T 0 ∘ T 1 ∘ ⋯` sends `M n` to `M 0`.

Inserting the homogeneous projection to a chosen degree after every map gives the
*chain history* of that degree sequence. It retains whole homogeneous
decorations: a nonzero final value forces every intermediate decoration to be
nonzero. This is the finite component expansion of transfer compositions between
graded chamber modules. For a fixed input only finitely many histories are
nonzero, and they sum to the composite; no finiteness of the degree types is
needed. A finite set containing the contributing histories of every input in the
range of a linear map gives an identity of linear maps. The input module and
the gradings may be infinite, and finite generation of the input range is a
sufficient condition.

Chamber maps `r k : M k → N k` that intertwine two chains and carry homogeneous
pieces along degree maps `σ k` preserve the expansion. A target history is the sum
of the images of the source histories over it, where several source degrees can merge
and cancel. Injective degree maps give componentwise naturality.
When the final chamber map is injective, it reflects selected linear-map
identities from the target expansion to the source.

The single-module histories `homogeneousHistory` of `History/Basic.lean` are the
constant chains.

The finiteness and regrouping arguments use `DirectSum.sum_support_decompose`,
`DirectSum.decompose_map_eq_sum` and Tau Ceti's `DirectSum.map_decompose_shift`.
-/

public noncomputable section

namespace Mei

universe u v w

section Index

/-! The modules and degree types of a chain are indexed by `ℕ`, and its tail is the shifted
family `fun k => M (k + 1)`. The positions `0` and `Fin.succ j` of Mathlib's `Fin` API have
values `↑(0 : Fin (n + 1))` and `↑j.succ`, which are not reducibly `0` and `↑j + 1`. Terms
such as `ℳ 0 (p 0)` or `T 0` applied to an element of `M (0 + 1)` are then type-correct
only up to unfolding, and rewriting, simp and instance search fail on them. The two
positions below are the same elements of `Fin (n + 1)` with literal values, so these types
agree reducibly. Degree sequences are prepended with `Fin.cons`. -/

/-- The position `0` of a nonempty chain, with literal value zero. -/
abbrev chainHead (n : ℕ) : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩

/-- The position `Fin.succ j`, with literal value `j + 1`. -/
abbrev chainSucc {n : ℕ} (j : Fin n) : Fin (n + 1) := ⟨j + 1, Nat.succ_lt_succ j.isLt⟩

variable {ι : ℕ → Type w} {n : ℕ}

/-- `Fin.cons` for a degree sequence whose tail is typed by the shifted family. -/
abbrev chainCons (i : ι 0) (p : (j : Fin n) → ι (j + 1)) : (j : Fin (n + 1)) → ι j :=
  Fin.cons (α := fun j : Fin (n + 1) => ι j) i p

@[simp]
theorem chainCons_zero (i : ι 0) (p : (j : Fin n) → ι (j + 1)) :
    chainCons i p 0 = i :=
  Fin.cons_zero (α := fun j : Fin (n + 1) => ι j) i p

@[simp]
theorem chainCons_succ (i : ι 0) (p : (j : Fin n) → ι (j + 1)) (j : Fin n) :
    chainCons i p (chainSucc j) = p j :=
  Fin.cons_succ (α := fun j : Fin (n + 1) => ι j) i p j

/-- `Fin.forall_fin_succ` at the literal positions. -/
theorem chainHead_forall {P : Fin (n + 1) → Prop} :
    (∀ j, P j) ↔ P (chainHead n) ∧ ∀ j : Fin n, P (chainSucc j) :=
  Fin.forall_fin_succ

end Index

variable {R : Type u} [Semiring R]

/-- The composite `T 0 ∘ T 1 ∘ ⋯ ∘ T (n - 1)` of a chain of linear maps
`T j : M (j + 1) → M j`. The step with index zero acts last. -/
def chainComp : {n : ℕ} → {M : ℕ → Type v} → [∀ k, AddCommMonoid (M k)] →
    [∀ k, Module R (M k)] → ((j : Fin n) → M (j + 1) →ₗ[R] M j) → M n →ₗ[R] M 0
  | 0, _, _, _, _ => LinearMap.id
  | n + 1, M, _, _, T =>
    (T (chainHead n)).comp (chainComp (M := fun k => M (k + 1)) fun j => T (chainSucc j))

/-- Propagation along a chain, keeping only the chosen homogeneous component after
each step. The degree `p j` is the degree selected in `M j`, the output of `T j`.
The empty chain leaves the input unchanged. -/
def chainHistory : {n : ℕ} → {M : ℕ → Type v} → [∀ k, AddCommMonoid (M k)] →
    [∀ k, Module R (M k)] → {ι : ℕ → Type w} → [∀ k, DecidableEq (ι k)] →
    (ℳ : ∀ k, ι k → Submodule R (M k)) → [∀ k, DirectSum.Decomposition (ℳ k)] →
    ((j : Fin n) → M (j + 1) →ₗ[R] M j) → ((j : Fin n) → ι j) → M n →ₗ[R] M 0
  | 0, _, _, _, _, _, _, _, _, _ => LinearMap.id
  | n + 1, M, _, _, ι, _, ℳ, _, T, p =>
    (homogeneousComponent (ℳ 0) (p (chainHead n))).comp
      ((T (chainHead n)).comp (chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
        (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) (fun j => p (chainSucc j))))

section Composite

variable {M : ℕ → Type v} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]

/-- The empty chain has identity composite. -/
@[simp]
theorem chainComp_zero (T : (j : Fin 0) → M (j + 1) →ₗ[R] M j) :
    chainComp T = LinearMap.id := (rfl)

/-- A nonempty chain composite applies its final step after the remaining chain. -/
theorem chainComp_succ {n : ℕ} (T : (j : Fin (n + 1)) → M (j + 1) →ₗ[R] M j) :
    chainComp T =
      (T (chainHead n)).comp (chainComp (M := fun k => M (k + 1)) fun j => T (chainSucc j)) :=
  (rfl)

/-- On a constant chain the composite is the ordered product of endomorphisms. -/
theorem chainComp_const {N : Type v} [AddCommMonoid N] [Module R N] {n : ℕ}
    (T : Fin n → Module.End R N) :
    chainComp (M := fun _ => N) T = (List.ofFn T).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ← ih fun j => T j.succ]
    rfl

end Composite

variable {M : ℕ → Type v} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]
  {ι : ℕ → Type w} [∀ k, DecidableEq (ι k)] (ℳ : ∀ k, ι k → Submodule R (M k))
  [∀ k, DirectSum.Decomposition (ℳ k)]

/-- No propagation steps give the identity map. -/
@[simp]
theorem chainHistory_zero (T : (j : Fin 0) → M (j + 1) →ₗ[R] M j)
    (p : (j : Fin 0) → ι j) :
    chainHistory ℳ T p = LinearMap.id := (rfl)

/-- One more step applies its map to the remaining history and selects the entire
output component of the recorded degree. -/
theorem chainHistory_succ_apply {n : ℕ} (T : (j : Fin (n + 1)) → M (j + 1) →ₗ[R] M j)
    (p : (j : Fin (n + 1)) → ι j) (a : M (n + 1)) :
    chainHistory ℳ T p a =
      (DirectSum.decompose (ℳ 0) (T (chainHead n) (chainHistory (M := fun k => M (k + 1))
        (ι := fun k => ι (k + 1)) (fun k => ℳ (k + 1)) (fun j => T (chainSucc j))
        (fun j => p (chainSucc j)) a)) (p (chainHead n)) : M 0) := by
  simp only [chainHistory, homogeneousComponent_apply, LinearMap.comp_apply]

/-- The output of a nonempty history lies in its last selected homogeneous piece. -/
theorem chainHistory_mem {n : ℕ} (T : (j : Fin (n + 1)) → M (j + 1) →ₗ[R] M j)
    (p : (j : Fin (n + 1)) → ι j) (a : M (n + 1)) :
    chainHistory ℳ T p a ∈ ℳ 0 (p (chainHead n)) := by
  rw [chainHistory_succ_apply]
  exact Subtype.property _

/-- A vanished intermediate decoration cannot yield a nonzero final history. -/
theorem chainHistory_tail_ne_zero {n : ℕ} (T : (j : Fin (n + 1)) → M (j + 1) →ₗ[R] M j)
    (p : (j : Fin (n + 1)) → ι j) {a : M (n + 1)} (ha : chainHistory ℳ T p a ≠ 0) :
    chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
      (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) (fun j => p (chainSucc j)) a ≠ 0 := by
  intro hz
  apply ha
  rw [chainHistory_succ_apply, hz, map_zero, DirectSum.decompose_zero]
  rfl

section Finite

/-- Only finitely many degree histories have nonzero whole decorations for a fixed
input. Neither the degree types nor the homogeneous supports of the modules need
to be finite. -/
theorem finite_support_chainHistory {n : ℕ} (T : (j : Fin n) → M (j + 1) →ₗ[R] M j)
    (a : M n) :
    (Function.support fun p : (j : Fin n) → ι j => chainHistory ℳ T p a).Finite := by
  classical
  induction n generalizing M ι with
  | zero => exact Set.toFinite _
  | succ n ih =>
    have hS := ih (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
      (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) a
    let B := fun p' : (j : Fin n) → ι (j + 1) => (DirectSum.decompose (ℳ 0) (T (chainHead n)
      (chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
        (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) p' a))).support
    apply (Finset.finite_toSet (hS.toFinset.biUnion fun p' => (B p').image
      fun i => (chainCons i p' : (j : Fin (n + 1)) → ι j))).subset
    intro p hp
    have hc : p (chainHead n) ∈ B (fun j => p (chainSucc j)) := by
      apply DFinsupp.mem_support_iff.mpr
      intro he
      have hp' : chainHistory ℳ T p a ≠ 0 := hp
      apply hp'
      rw [chainHistory_succ_apply]
      exact congrArg Subtype.val he
    exact Finset.mem_biUnion.mpr ⟨fun j => p (chainSucc j),
      (Set.Finite.mem_toFinset _).mpr (chainHistory_tail_ne_zero ℳ T p hp),
      Finset.mem_image.mpr ⟨p (chainHead n), hc, Fin.cons_self_tail p⟩⟩

/-- The finite set of degree histories whose final whole decoration is nonzero. -/
def chainHistorySupport {n : ℕ} (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (a : M n) :
    Finset ((j : Fin n) → ι j) :=
  (finite_support_chainHistory ℳ T a).toFinset

/-- Membership retains precisely the histories with nonzero decoration. -/
@[simp]
theorem mem_chainHistorySupport {n : ℕ} (T : (j : Fin n) → M (j + 1) →ₗ[R] M j)
    (a : M n) (p : (j : Fin n) → ι j) :
    p ∈ chainHistorySupport ℳ T a ↔ chainHistory ℳ T p a ≠ 0 :=
  Set.Finite.mem_toFinset _

/-- Zero input has no contributing histories. -/
@[simp]
theorem chainHistorySupport_zero {n : ℕ} (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) :
    chainHistorySupport ℳ T 0 = ∅ := by
  ext p
  simp

open Classical in
/-- Extend each contributing history of the remaining chain by precisely the
nonzero output components of the final map. -/
theorem chainHistorySupport_succ {n : ℕ} (T : (j : Fin (n + 1)) → M (j + 1) →ₗ[R] M j)
    (a : M (n + 1)) :
    chainHistorySupport ℳ T a =
      (chainHistorySupport (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
        (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) a).biUnion fun p' =>
        (DirectSum.decompose (ℳ 0) (T (chainHead n) (chainHistory (M := fun k => M (k + 1))
          (ι := fun k => ι (k + 1)) (fun k => ℳ (k + 1)) (fun j => T (chainSucc j))
            p' a))).support.image
          fun i => (chainCons i p' : (j : Fin (n + 1)) → ι j) := by
  ext p
  simp only [mem_chainHistorySupport, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro hp
    refine ⟨fun j => p (chainSucc j), chainHistory_tail_ne_zero ℳ T p hp, p (chainHead n), ?_,
      Fin.cons_self_tail p⟩
    rw [chainHistory_succ_apply] at hp
    exact DFinsupp.mem_support_iff.mpr fun he => hp (congrArg Subtype.val he)
  · rintro ⟨q, _, i, hi, rfl⟩
    rw [chainHistory_succ_apply]
    intro hz
    apply DFinsupp.mem_support_iff.mp hi
    exact Subtype.val_injective hz

open Classical in
private theorem chainHistorySupport_extensions_disjoint {n : ℕ}
    (T : (j : Fin (n + 1)) → M (j + 1) →ₗ[R] M j) (a : M (n + 1)) :
    Set.PairwiseDisjoint
      (↑(chainHistorySupport (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
        (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) a) : Set ((j : Fin n) → ι (j + 1)))
      fun p' => (DirectSum.decompose (ℳ 0) (T (chainHead n) (chainHistory (M := fun k => M (k + 1))
        (ι := fun k => ι (k + 1)) (fun k => ℳ (k + 1)) (fun j => T (chainSucc j))
          p' a))).support.image
          fun i => (chainCons i p' : (j : Fin (n + 1)) → ι j) := by
  intro p _ q _ hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, he⟩ := Finset.mem_image.mp hy
  exact hpq (Fin.cons_inj.mp he).2.symm

/-- Summing exactly the nonzero histories recovers the composite of the chain. -/
@[simp]
theorem sum_chainHistory {n : ℕ} (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (a : M n) :
    ∑ p ∈ chainHistorySupport ℳ T a, chainHistory ℳ T p a = chainComp T a := by
  classical
  induction n generalizing M ι with
  | zero =>
    by_cases ha : a = 0
    · simp [ha]
    · have hs : chainHistorySupport ℳ T a = {fun j => Fin.elim0 j} := by
        ext p
        simp [ha, Subsingleton.elim p (fun j => Fin.elim0 j)]
      simp [hs]
  | succ n ih =>
    rw [chainHistorySupport_succ, Finset.sum_biUnion
      (chainHistorySupport_extensions_disjoint ℳ T a)]
    trans ∑ p' ∈ chainHistorySupport (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
        (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) a,
        T (chainHead n) (chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
          (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) p' a)
    · refine Finset.sum_congr rfl fun p' _ => ?_
      rw [Finset.sum_image (g := fun i => chainCons i p') fun i _ j _ hij =>
        (Fin.cons_inj.mp hij).1]
      simp only [chainHistory_succ_apply, chainCons_succ]
      exact DirectSum.sum_support_decompose (ℳ 0) _
    · rw [← map_sum, ih (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
        (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) a]
      rfl

end Finite

section Regrading

variable {N : ℕ → Type*} [∀ k, AddCommMonoid (N k)] [∀ k, Module R (N k)]
  {κ : ℕ → Type*} [∀ k, DecidableEq (κ k)] (𝓝 : ∀ k, κ k → Submodule R (N k))
  [∀ k, DirectSum.Decomposition (𝓝 k)]
  (r : ∀ k, M k →ₗ[R] N k) (σ : ∀ k, ι k → κ k)
  (hr : ∀ k i x, x ∈ ℳ k i → r k x ∈ 𝓝 k (σ k i))

include hr

/-- Along injective degree maps, intertwining chamber maps send each whole history
to the history with the reindexed degrees. -/
theorem map_chainHistory_of_injective (hσ : ∀ k, Function.Injective (σ k)) {n : ℕ}
    (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (U : (j : Fin n) → N (j + 1) →ₗ[R] N j)
    (hT : ∀ j : Fin n, (r j).comp (T j) = (U j).comp (r (j + 1)))
    (p : (j : Fin n) → ι j) (a : M n) :
    r 0 (chainHistory ℳ T p a) = chainHistory 𝓝 U (fun j => σ j (p j)) (r n a) := by
  induction n generalizing M ι N κ with
  | zero => rfl
  | succ n ih =>
    have hcomm := LinearMap.congr_fun (hT (chainHead n)) (chainHistory (M := fun k => M (k + 1))
      (ι := fun k => ι (k + 1)) (fun k => ℳ (k + 1)) (fun j => T (chainSucc j))
      (fun j => p (chainSucc j)) a)
    have htail := ih (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
      (N := fun k => N (k + 1)) (κ := fun k => κ (k + 1)) (fun k => ℳ (k + 1))
      (fun k => 𝓝 (k + 1)) (fun k => r (k + 1)) (fun k => σ (k + 1)) (fun k => hr (k + 1))
      (fun k => hσ (k + 1)) (fun j => T (chainSucc j)) (fun j => U (chainSucc j))
      (fun j => hT (chainSucc j)) (fun j => p (chainSucc j)) a
    simp only [LinearMap.comp_apply] at hcomm
    rw [chainHistory_succ_apply]
    refine (DirectSum.map_decompose_shift (ℳ 0) (𝓝 0) (r 0).toAddMonoidHom (σ 0) (hσ 0)
      (hr 0) _ _).trans ?_
    rw [LinearMap.toAddMonoidHom_coe, hcomm, chainHistory_succ_apply 𝓝 U]
    exact congrArg (fun x => (DirectSum.decompose (𝓝 0) (U (chainHead n) x)
      (σ 0 (p (chainHead n))) : N 0)) htail

open Classical in
/-- A target history is the finite sum of the images of its source refinements.
Neither the degree maps nor their fibers need be finite, and refinements with the
same image are added before the target component is formed. -/
theorem chainHistory_map_eq_sum {n : ℕ}
    (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (U : (j : Fin n) → N (j + 1) →ₗ[R] N j)
    (hT : ∀ j : Fin n, (r j).comp (T j) = (U j).comp (r (j + 1)))
    (q : (j : Fin n) → κ j) (a : M n) :
    chainHistory 𝓝 U q (r n a) =
      ∑ p ∈ chainHistorySupport ℳ T a,
        if ∀ j : Fin n, σ j (p j) = q j then r 0 (chainHistory ℳ T p a) else 0 := by
  induction n generalizing M ι N κ with
  | zero =>
    simp only [Fin.forall_fin_zero, ↓reduceIte]
    rw [← map_sum, sum_chainHistory]
    simp
  | succ n ih =>
    have htail := ih (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
      (N := fun k => N (k + 1)) (κ := fun k => κ (k + 1)) (fun k => ℳ (k + 1))
      (fun k => 𝓝 (k + 1)) (fun k => r (k + 1)) (fun k => σ (k + 1)) (fun k => hr (k + 1))
      (fun j => T (chainSucc j)) (fun j => U (chainSucc j)) (fun j => hT (chainSucc j))
      (fun j => q (chainSucc j)) a
    beta_reduce at htail
    rw [chainHistory_succ_apply, htail]
    simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    rw [chainHistorySupport_succ, Finset.sum_biUnion
      (chainHistorySupport_extensions_disjoint ℳ T a)]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [Finset.sum_image (g := fun i => chainCons i p') fun i _ j _ hij => (Fin.cons_inj.mp hij).1]
    simp only [chainHead_forall, chainCons_succ, chainHistory_succ_apply]
    by_cases hp : ∀ j : Fin n, σ (j + 1) (p' j) = q (chainSucc j)
    · simp only [hp, implies_true, and_true, ↓reduceIte]
      have hcomm := LinearMap.congr_fun (hT (chainHead n)) (chainHistory (M := fun k => M (k + 1))
        (ι := fun k => ι (k + 1)) (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) p' a)
      simp only [LinearMap.comp_apply] at hcomm
      rw [← hcomm]
      have h := DirectSum.decompose_map_eq_sum (ℳ 0) (𝓝 0) (r 0).toAddMonoidHom (σ 0) (hr 0)
        (T (chainHead n) (chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
          (fun k => ℳ (k + 1)) (fun j => T (chainSucc j)) p' a)) (q (chainHead n))
      rw [Finset.sum_filter] at h
      exact h
    · simp only [hp, and_false, ↓reduceIte, Finset.sum_const_zero]
      rw [map_zero, DirectSum.decompose_zero]
      rfl

open Classical in
/-- Refinements killed by the chamber map are omitted from the regrouped sum.
The remaining finite set retains entire decorations. -/
theorem chainHistory_map_eq_sum_surviving {n : ℕ}
    (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (U : (j : Fin n) → N (j + 1) →ₗ[R] N j)
    (hT : ∀ j : Fin n, (r j).comp (T j) = (U j).comp (r (j + 1)))
    (q : (j : Fin n) → κ j) (a : M n) :
    chainHistory 𝓝 U q (r n a) =
      ∑ p ∈ (chainHistorySupport ℳ T a).filter
          (fun p => (∀ j : Fin n, σ j (p j) = q j) ∧ r 0 (chainHistory ℳ T p a) ≠ 0),
        r 0 (chainHistory ℳ T p a) := by
  rw [chainHistory_map_eq_sum ℳ 𝓝 r σ hr T U hT q a, ← Finset.sum_filter]
  simpa only [Finset.filter_filter] using
    (Finset.sum_filter_ne_zero (f := fun p => r 0 (chainHistory ℳ T p a))
      ((chainHistorySupport ℳ T a).filter fun p => ∀ j : Fin n, σ j (p j) = q j)).symm

/-- A nonzero target history admits a source refinement whose whole decoration
survives the chamber map. -/
theorem exists_chainHistory_ne_zero_of_map_ne_zero {n : ℕ}
    (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (U : (j : Fin n) → N (j + 1) →ₗ[R] N j)
    (hT : ∀ j : Fin n, (r j).comp (T j) = (U j).comp (r (j + 1)))
    (q : (j : Fin n) → κ j) {a : M n} (ha : chainHistory 𝓝 U q (r n a) ≠ 0) :
    ∃ p : (j : Fin n) → ι j, (∀ j : Fin n, σ j (p j) = q j) ∧ r 0 (chainHistory ℳ T p a) ≠ 0 := by
  classical
  rw [chainHistory_map_eq_sum ℳ 𝓝 r σ hr T U hT q a] at ha
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  split_ifs at hp with h
  · exact ⟨p, h, hp⟩
  · exact (hp rfl).elim

open Classical in
/-- Selecting target histories commutes with the chamber maps when source histories
are selected by their regraded history. Source histories with the same image are
added before vanishing target histories are discarded. -/
theorem map_sum_ite_chainHistory {n : ℕ}
    (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (U : (j : Fin n) → N (j + 1) →ₗ[R] N j)
    (hT : ∀ j : Fin n, (r j).comp (T j) = (U j).comp (r (j + 1)))
    (E : ((j : Fin n) → κ j) → Prop) (a : M n) :
    r 0 (∑ p ∈ chainHistorySupport ℳ T a,
      if E (fun j => σ j (p j)) then chainHistory ℳ T p a else 0) =
      ∑ q ∈ chainHistorySupport 𝓝 U (r n a),
        if E q then chainHistory 𝓝 U q (r n a) else 0 := by
  let S := chainHistorySupport ℳ T a
  let Q := S.image fun p (j : Fin n) => σ j (p j)
  have hsub : chainHistorySupport 𝓝 U (r n a) ⊆ Q := by
    intro q hq
    obtain ⟨p, hp, hn⟩ := exists_chainHistory_ne_zero_of_map_ne_zero ℳ 𝓝 r σ hr T U hT q
      ((mem_chainHistorySupport ..).mp hq)
    exact Finset.mem_image.mpr ⟨p,
      (mem_chainHistorySupport ..).mpr fun hz => hn (by simp [hz]), funext hp⟩
  rw [map_sum]
  calc
    _ = ∑ q ∈ Q, ∑ p ∈ S with (fun j : Fin n => σ j (p j)) = q,
        r 0 (if E (fun j => σ j (p j)) then chainHistory ℳ T p a else 0) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image_of_mem (fun p (j : Fin n) => σ j (p j)) hp) _).symm
    _ = ∑ q ∈ Q, if E q then chainHistory 𝓝 U q (r n a) else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [chainHistory_map_eq_sum ℳ 𝓝 r σ hr T U hT q a, Finset.sum_filter]
      by_cases hq : E q
      · simp only [hq, ↓reduceIte]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hp : (fun j : Fin n => σ j (p j)) = q
        · have hp' : ∀ j : Fin n, σ j (p j) = q j := congrFun hp
          simp [hp', hq]
        · have hp' : ¬ ∀ j : Fin n, σ j (p j) = q j := fun h => hp (funext h)
          simp [hp, hp']
      · simp only [hq, ↓reduceIte]
        refine Finset.sum_eq_zero fun p _ => ?_
        by_cases hp : (fun j : Fin n => σ j (p j)) = q <;> simp [hp, hq]
    _ = _ := (Finset.sum_subset hsub fun q _ hq => by
      have hz : chainHistory 𝓝 U q (r n a) = 0 := by
        simpa only [mem_chainHistorySupport, not_not] using hq
      simp [hz]).symm

end Regrading

section Uniform

variable {E : Type*} [AddCommMonoid E] [Module R E]
  {n : ℕ} (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (a : E →ₗ[R] M n)

/-- A uniform support of history maps contains the pointwise support of every input. -/
theorem chainHistorySupport_subset_of_comp_eq_zero (S : Finset ((j : Fin n) → ι j))
    (hS : ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0) (x : E) :
    chainHistorySupport ℳ T (a x) ⊆ S := by
  intro p hp
  by_contra h
  exact (mem_chainHistorySupport ℳ T (a x) p).mp hp (LinearMap.congr_fun (hS p h) x)

/-- Uniform finite contributing support on the input range gives the expansion as an
identity of linear maps. No finiteness of the gradings is required. -/
theorem sum_chainHistory_comp_eq (S : Finset ((j : Fin n) → ι j))
    (hS : ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0) :
    ∑ p ∈ S, (chainHistory ℳ T p).comp a = (chainComp T).comp a := by
  ext x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← sum_chainHistory ℳ T (a x)]
  exact (Finset.sum_subset (chainHistorySupport_subset_of_comp_eq_zero ℳ T a S hS x)
    fun p _ hp => by simpa using hp).symm

/-- A finite generating set of inputs gives a uniform finite history support on
its entire span. -/
theorem exists_uniform_chainHistory_support_of_fg (P : Submodule R (M n)) (hP : P.FG) :
    ∃ S : Finset ((j : Fin n) → ι j), ∀ p ∉ S, ∀ x ∈ P, chainHistory ℳ T p x = 0 := by
  classical
  obtain ⟨s, hs⟩ := hP
  refine ⟨s.biUnion (chainHistorySupport ℳ T), fun p hp x hx => ?_⟩
  have hker : P ≤ LinearMap.ker (chainHistory ℳ T p) := by
    rw [← hs]
    refine Submodule.span_le.mpr fun y hy => LinearMap.mem_ker.mpr ?_
    by_contra hne
    exact hp (Finset.mem_biUnion.mpr ⟨y, hy, (mem_chainHistorySupport ℳ T y p).mpr hne⟩)
  exact hker hx

/-- Finite generation of the input range, not of the graded modules, ensures the
uniform support needed for the linear-map expansion. -/
theorem exists_uniform_chainHistory_support (ha : (LinearMap.range a).FG) :
    ∃ S : Finset ((j : Fin n) → ι j), ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0 := by
  obtain ⟨S, hS⟩ := exists_uniform_chainHistory_support_of_fg ℳ T _ ha
  exact ⟨S, fun p hp => LinearMap.ext fun x => hS p hp (a x) (LinearMap.mem_range_self a x)⟩

open Classical in
/-- Selecting histories in a uniform support gives the same value as selecting in
the pointwise nonzero support. Zero terms are retained in the linear-map sum. -/
theorem sum_ite_chainHistory_comp_apply (S : Finset ((j : Fin n) → ι j))
    (hS : ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0)
    (P : ((j : Fin n) → ι j) → Prop) (x : E) :
    (∑ p ∈ S, if P p then (chainHistory ℳ T p).comp a else 0) x =
      ∑ p ∈ chainHistorySupport ℳ T (a x),
        if P p then chainHistory ℳ T p (a x) else 0 := by
  trans ∑ p ∈ S, if P p then chainHistory ℳ T p (a x) else 0
  · simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> rfl
  exact (Finset.sum_subset (chainHistorySupport_subset_of_comp_eq_zero ℳ T a S hS x)
    fun p _ hp => by
      have hz : chainHistory ℳ T p (a x) = 0 := by simpa using hp
      simp [hz]).symm

open Classical in
/-- Selected linear-map sums agree over any two uniform supports. -/
theorem sum_ite_chainHistory_comp_eq (S S' : Finset ((j : Fin n) → ι j))
    (hS : ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0)
    (hS' : ∀ p ∉ S', (chainHistory ℳ T p).comp a = 0)
    (P : ((j : Fin n) → ι j) → Prop) :
    (∑ p ∈ S, if P p then (chainHistory ℳ T p).comp a else 0) =
      ∑ p ∈ S', if P p then (chainHistory ℳ T p).comp a else 0 := by
  ext x
  rw [sum_ite_chainHistory_comp_apply ℳ T a S hS, sum_ite_chainHistory_comp_apply ℳ T a S' hS']

section Regrading

variable {N : ℕ → Type*} [∀ k, AddCommMonoid (N k)] [∀ k, Module R (N k)]
  {κ : ℕ → Type*} [∀ k, DecidableEq (κ k)] (𝓝 : ∀ k, κ k → Submodule R (N k))
  [∀ k, DirectSum.Decomposition (𝓝 k)]
  (r : ∀ k, M k →ₗ[R] N k) (σ : ∀ k, ι k → κ k)
  (hr : ∀ k i x, x ∈ ℳ k i → r k x ∈ 𝓝 k (σ k i))
  (U : (j : Fin n) → N (j + 1) →ₗ[R] N j)
  (hT : ∀ j : Fin n, (r j).comp (T j) = (U j).comp (r (j + 1)))

include hr hT

/-- A source uniform support gives a target uniform support by regrading. -/
theorem chainHistory_comp_eq_zero_of_notMem_image (S : Finset ((j : Fin n) → ι j))
    (hS : ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0)
    (q : (j : Fin n) → κ j) (hq : q ∉ S.image fun p (j : Fin n) => σ j (p j)) :
    (chainHistory 𝓝 U q).comp ((r n).comp a) = 0 := by
  ext x
  by_contra hx
  obtain ⟨p, hp, hne⟩ := exists_chainHistory_ne_zero_of_map_ne_zero ℳ 𝓝 r σ hr T U hT q hx
  have hmem : p ∈ S := by
    by_contra h
    have hz := LinearMap.congr_fun (hS p h) x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    exact hne (by rw [hz, map_zero])
  exact hq (Finset.mem_image.mpr ⟨p, hmem, funext hp⟩)

open Classical in
/-- Grouped regrading of selected histories as an identity of linear maps. Neither
the degree maps nor the chamber maps need be injective, and groups whose total
coefficient cancels are allowed. -/
theorem map_sum_ite_chainHistory_comp
    (S : Finset ((j : Fin n) → ι j)) (S' : Finset ((j : Fin n) → κ j))
    (hS : ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0)
    (hS' : ∀ q ∉ S', (chainHistory 𝓝 U q).comp ((r n).comp a) = 0)
    (P : ((j : Fin n) → κ j) → Prop) :
    (r 0).comp (∑ p ∈ S, if P (fun j => σ j (p j)) then (chainHistory ℳ T p).comp a else 0) =
      ∑ q ∈ S', if P q then (chainHistory 𝓝 U q).comp ((r n).comp a) else 0 := by
  ext x
  simp only [LinearMap.comp_apply]
  rw [sum_ite_chainHistory_comp_apply ℳ T a S hS,
    sum_ite_chainHistory_comp_apply 𝓝 U ((r n).comp a) S' hS']
  simpa only [LinearMap.comp_apply] using map_sum_ite_chainHistory ℳ 𝓝 r σ hr T U hT P (a x)

open Classical in
/-- Grouped regrading needs only a source uniform support: its finite image supplies
the target index set, including groups with zero total weight. -/
theorem map_sum_ite_chainHistory_comp_image (S : Finset ((j : Fin n) → ι j))
    (hS : ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0)
    (P : ((j : Fin n) → κ j) → Prop) :
    (r 0).comp (∑ p ∈ S, if P (fun j => σ j (p j)) then (chainHistory ℳ T p).comp a else 0) =
      ∑ q ∈ S.image (fun p (j : Fin n) => σ j (p j)),
        if P q then (chainHistory 𝓝 U q).comp ((r n).comp a) else 0 :=
  map_sum_ite_chainHistory_comp ℳ T a 𝓝 r σ hr U hT S _ hS
    (chainHistory_comp_eq_zero_of_notMem_image ℳ T a 𝓝 r σ hr U hT S hS) P

open Classical in
/-- An injective final chamber map reflects selected expansion identities: a source
sum of histories equals `X` once the regrouped target sum equals the image of `X`.
The target identity can be proved in a coarser grading where histories merge. -/
theorem sum_ite_chainHistory_comp_eq_of_injective (hr0 : Function.Injective (r 0))
    (S : Finset ((j : Fin n) → ι j)) (S' : Finset ((j : Fin n) → κ j))
    (hS : ∀ p ∉ S, (chainHistory ℳ T p).comp a = 0)
    (hS' : ∀ q ∉ S', (chainHistory 𝓝 U q).comp ((r n).comp a) = 0)
    (P : ((j : Fin n) → κ j) → Prop) (X : E →ₗ[R] M 0)
    (hX : ∑ q ∈ S', (if P q then (chainHistory 𝓝 U q).comp ((r n).comp a) else 0) =
      (r 0).comp X) :
    ∑ p ∈ S, (if P (fun j => σ j (p j)) then (chainHistory ℳ T p).comp a else 0) = X := by
  apply LinearMap.ext
  intro x
  apply hr0
  have h := LinearMap.congr_fun
    ((map_sum_ite_chainHistory_comp ℳ T a 𝓝 r σ hr U hT S S' hS hS' P).trans hX) x
  simpa only [LinearMap.comp_apply] using h

end Regrading

end Uniform

end Mei
