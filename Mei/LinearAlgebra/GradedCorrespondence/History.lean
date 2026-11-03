/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Hom
public import Mei.LinearAlgebra.GradedModule.History.Chain

/-!
# Component expansions of zero-extended transfers

The *total transfer* of a graded correspondence is its total left lift followed by
the right leg. On an admissible homogeneous piece it is the lift across the span,
whose homogeneous components are the transfers; it vanishes on inadmissible pieces.
It is linear on mixed inputs, so a sequence of correspondences `C k` from `M (k + 1)`
to `M k` forms a chain of linear maps between differently graded chamber modules.

The chain histories of total transfers are the finite component expansion of
transfer compositions. Each step selects one transfer component of the whole previous
decoration, and the step is zero when that decoration has inadmissible degree. For a fixed
input the nonzero histories are finite and sum to the composite of total transfers, by
`sum_chainHistory`.

Correspondence morphisms with common chamber maps at incident steps intertwine total
transfers provided target total lifts kill the images of inadmissible source pieces.
Reflecting admissible degrees suffices. Then the regrading theorems for `chainHistory`
apply to transfer histories: a target history is the grouped sum of its source
refinements, and injective degree maps give componentwise naturality, for example
under coefficient truncation.

The single-step formulas are `decompose_right_liftLeftTotal_of_mem` and
`Hom.middle_comp_liftLeftTotal_iff`.
-/

public noncomputable section

namespace Mei.GradedCorrespondence

section TotalTransfer

variable {R B U V B' U' V' ι κ ι' κ' : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid V] [Module R V]
  [AddCommMonoid B'] [Module R B'] [AddCommMonoid U'] [Module R U']
  [AddCommMonoid V'] [Module R V']
  {𝒰 : ι → Submodule R U} {𝒱 : κ → Submodule R V} {I : Set ι} {J : Set κ}
  {𝒰' : ι' → Submodule R U'} {𝒱' : κ' → Submodule R V'} {I' : Set ι'} {J' : Set κ'}
  [DecidableEq ι] [DirectSum.Decomposition 𝒰]

/-- Lift each admissible homogeneous component across the span and forget the
inadmissible ones. -/
def totalTransfer (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) : U →ₗ[R] V :=
  C.right.comp C.liftLeftTotal

theorem totalTransfer_apply (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) (a : U) :
    C.totalTransfer a = C.right (C.liftLeftTotal a) := (rfl)

/-- On an admissible piece the total transfer is the image of the chosen lift. -/
@[simp]
theorem totalTransfer_coe (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) (i : I) (a : 𝒰 i) :
    C.totalTransfer a = C.right (C.liftLeft i a) := by
  rw [totalTransfer_apply, liftLeftTotal_coe]

/-- An inadmissible homogeneous input has zero total transfer. -/
theorem totalTransfer_of_not_mem (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    {i : ι} (hi : i ∉ I) {a : U} (ha : a ∈ 𝒰 i) : C.totalTransfer a = 0 := by
  rw [totalTransfer_apply, C.liftLeftTotal_of_not_mem hi ha, map_zero]

/-- The homogeneous components of the total transfer of a homogeneous input are its
transfers, or zero when the input degree is inadmissible. -/
theorem decompose_totalTransfer_of_mem [DecidableEq κ] [DirectSum.Decomposition 𝒱]
    (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) {i : ι} [Decidable (i ∈ I)] {a : U}
    (ha : a ∈ 𝒰 i) (j : κ) :
    DirectSum.decompose 𝒱 (C.totalTransfer a) j =
      if hi : i ∈ I then C.transfer ⟨i, hi⟩ j ⟨a, ha⟩ else 0 :=
  C.decompose_right_liftLeftTotal_of_mem ha j

/-- The total transfer of a graph correspondence is its equivalence. -/
@[simp]
theorem graph_totalTransfer (e : U ≃ₗ[R] V) :
    (graph 𝒰 𝒱 e).totalTransfer = e.toLinearMap := by
  rw [totalTransfer, graph_liftLeftTotal, graph_right, LinearMap.comp_id]

variable [DecidableEq ι'] [DirectSum.Decomposition 𝒰']
  {C : GradedCorrespondence (B := B) 𝒰 𝒱 I J} {D : GradedCorrespondence (B := B') 𝒰' 𝒱' I' J'}
  {σ : ι → ι'} {τ : κ → κ'}

/-- A morphism intertwines total transfers once target total lifts kill the images
of inadmissible source pieces. -/
theorem Hom.right_comp_totalTransfer (f : Hom C D σ τ)
    (hzero : ∀ i, i ∉ I → ∀ a : 𝒰 i, D.liftLeftTotal (f.left a) = 0) :
    f.right.comp C.totalTransfer = D.totalTransfer.comp f.left := by
  rw [totalTransfer, totalTransfer, ← LinearMap.comp_assoc, f.right_comm, LinearMap.comp_assoc,
    f.middle_comp_liftLeftTotal_iff.mpr hzero, LinearMap.comp_assoc]

/-- Reflecting admissible degrees suffices for naturality of total transfers. -/
theorem Hom.right_comp_totalTransfer_of_reflects_admissible (f : Hom C D σ τ)
    (hI : ∀ i, σ i ∈ I' → i ∈ I) :
    f.right.comp C.totalTransfer = D.totalTransfer.comp f.left := by
  rw [totalTransfer, totalTransfer, ← LinearMap.comp_assoc, f.right_comm, LinearMap.comp_assoc,
    f.middle_comp_liftLeftTotal_of_reflects_admissible hI, LinearMap.comp_assoc]

end TotalTransfer

section Chain

variable {R : Type*} [Semiring R]
  {M : ℕ → Type*} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]
  {ι : ℕ → Type*} [∀ k, DecidableEq (ι k)] (ℳ : ∀ k, ι k → Submodule R (M k))
  [∀ k, DirectSum.Decomposition (ℳ k)]
  {B : ℕ → Type*} [∀ k, AddCommMonoid (B k)] [∀ k, Module R (B k)]
  {I : ∀ k, Set (ι (k + 1))} {J : ∀ k, Set (ι k)}
  (C : ∀ k, GradedCorrespondence (B := B k) (ℳ (k + 1)) (ℳ k) (I k) (J k))

/-- Each step of a transfer history selects one transfer component of the whole
previous decoration. A decoration of inadmissible degree contributes zero. -/
theorem chainHistory_totalTransfer_succ_apply {n : ℕ} (p : (j : Fin (n + 1)) → ι j)
    (a : M (n + 1)) {i : ι 1} [Decidable (i ∈ I 0)]
    (hx : chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
      (fun k => ℳ (k + 1)) (fun j => (C (j + 1)).totalTransfer) (fun j => p (chainSucc j)) a ∈
        ℳ 1 i) :
    chainHistory ℳ (fun j => (C j).totalTransfer) p a =
      if hi : i ∈ I 0 then ((C 0).transfer ⟨i, hi⟩ (p (chainHead n)) ⟨_, hx⟩ : M 0) else 0 := by
  rw [chainHistory_succ_apply, decompose_totalTransfer_of_mem (C 0) hx]
  split_ifs <;> rfl

/-- A transfer history whose decoration before the final crossing has inadmissible
degree vanishes. -/
theorem chainHistory_totalTransfer_eq_zero_of_not_mem {n : ℕ} (p : (j : Fin (n + 1)) → ι j)
    (a : M (n + 1)) {i : ι 1} (hi : i ∉ I 0)
    (hx : chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
      (fun k => ℳ (k + 1)) (fun j => (C (j + 1)).totalTransfer) (fun j => p (chainSucc j)) a ∈
        ℳ 1 i) :
    chainHistory ℳ (fun j => (C j).totalTransfer) p a = 0 := by
  classical
  rw [chainHistory_totalTransfer_succ_apply ℳ C p a hx, dite_eq_right hi]

section Naturality

variable {N : ℕ → Type*} [∀ k, AddCommMonoid (N k)] [∀ k, Module R (N k)]
  {κ : ℕ → Type*} [∀ k, DecidableEq (κ k)] (𝓝 : ∀ k, κ k → Submodule R (N k))
  [∀ k, DirectSum.Decomposition (𝓝 k)]
  {B' : ℕ → Type*} [∀ k, AddCommMonoid (B' k)] [∀ k, Module R (B' k)]
  {I' : ∀ k, Set (κ (k + 1))} {J' : ∀ k, Set (κ k)}
  (D : ∀ k, GradedCorrespondence (B := B' k) (𝓝 (k + 1)) (𝓝 k) (I' k) (J' k))
  (r : ∀ k, M k →ₗ[R] N k) (σ : ∀ k, ι k → κ k)
  (f : ∀ k, Hom (C k) (D k) (σ (k + 1)) (σ k))
  (hl : ∀ k, (f k).left = r (k + 1)) (hv : ∀ k, (f k).right = r k)
  (hzero : ∀ k, ∀ i, i ∉ I k → ∀ a : ℳ (k + 1) i, (D k).liftLeftTotal (r (k + 1) a) = 0)

include f hl hv hzero

/-- Chamber maps of correspondence morphisms intertwine every step of the chain of
total transfers. -/
theorem comp_totalTransfer_of_hom (k : ℕ) :
    (r k).comp (C k).totalTransfer = (D k).totalTransfer.comp (r (k + 1)) := by
  rw [← hv k, ← hl k]
  exact (f k).right_comp_totalTransfer fun i hi a => by rw [hl k]; exact hzero k i hi a

open Classical in
/-- A target transfer history is the grouped sum of its source refinements. Source
degrees merging under the degree maps are added before taking the target component. -/
theorem chainHistory_totalTransfer_map_eq_sum {n : ℕ} (q : (j : Fin n) → κ j) (a : M n) :
    chainHistory 𝓝 (fun j : Fin n => (D j).totalTransfer) q (r n a) =
      ∑ p ∈ chainHistorySupport ℳ (fun j : Fin n => (C j).totalTransfer) a,
        if ∀ j : Fin n, σ j (p j) = q j then
          r 0 (chainHistory ℳ (fun j : Fin n => (C j).totalTransfer) p a) else 0 :=
  chainHistory_map_eq_sum ℳ 𝓝 r σ
    (fun k i x hx => by rw [← hv k]; exact (f k).right_mem i x hx) _ _
    (fun j => comp_totalTransfer_of_hom ℳ C 𝓝 D r σ f hl hv hzero j) q a

/-- Along injective degree maps, for example coefficient truncations, the chamber maps
send each transfer history to the reindexed target transfer history. -/
theorem map_chainHistory_totalTransfer_of_injective (hσ : ∀ k, Function.Injective (σ k))
    {n : ℕ} (p : (j : Fin n) → ι j) (a : M n) :
    r 0 (chainHistory ℳ (fun j : Fin n => (C j).totalTransfer) p a) =
      chainHistory 𝓝 (fun j : Fin n => (D j).totalTransfer) (fun j => σ j (p j)) (r n a) :=
  map_chainHistory_of_injective ℳ 𝓝 r σ
    (fun k i x hx => by rw [← hv k]; exact (f k).right_mem i x hx) hσ _ _
    (fun j => comp_totalTransfer_of_hom ℳ C 𝓝 D r σ f hl hv hzero j) p a

end Naturality

end Chain

end Mei.GradedCorrespondence
