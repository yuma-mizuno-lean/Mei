/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.GroupTheory.CompletedGroup.Map
public import Mei.Data.Finset.Sort
public import Mathlib.Algebra.Notation.Support

/-!
# Ordered products in completed groups

A linearly ordered family in a completed group has a product whenever only finitely
many factors are nonidentity at each order. The smallest index is the leftmost
factor. The product is characterized by its finite-order projections, and any finite
set containing the support at that order can be used to compute it.

Increasing reindexing may delete identity factors, and maps of reindexed towers
preserve these products. No commutativity, surjectivity of transitions, or topology
on the tower groups is required. The construction uses the compatible-family
carrier `Mei.completedGroup`, Mathlib's sorted finite sets and `map_list_prod`.
-/

public section

open CategoryTheory Opposite

universe u

namespace Mei.CompletedGroup

variable {F G : ℕᵒᵖ ⥤ GrpCat.{u}} {ι κ : Type*}

/-- A family has finite support at each order if only finitely many factors have
nonidentity projection to any fixed tower group. -/
abbrev HasFiniteSupport (x : ι → completedGroup F) : Prop :=
  ∀ k, (Function.mulSupport fun i => projection k (x i)).Finite

namespace HasFiniteSupport

/-- A subfamily indexed by an injection still has finite support at each order. -/
theorem comp {x : ι → completedGroup F} (hx : HasFiniteSupport x)
    {e : κ → ι} (he : Function.Injective e) : HasFiniteSupport (x ∘ e) :=
  fun k => (hx k).preimage he.injOn

/-- A map of reindexed towers preserves finite support at each order. -/
theorem map {x : ι → completedGroup F} (hx : HasFiniteSupport x)
    (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G) :
    HasFiniteSupport (fun i => CompletedGroup.map ρ f (x i)) := by
  intro k
  apply (hx (ρ k)).subset
  intro i hi
  simp only [Function.mem_mulSupport, projection_map] at hi ⊢
  intro h
  exact hi (by simp [h])

end HasFiniteSupport

variable [LinearOrder ι]

/-- The ordered product of a family with finite support at every order, with the
smallest index leftmost. -/
noncomputable def orderedProduct (x : ι → completedGroup F) (hx : HasFiniteSupport x) :
    completedGroup F := by
  classical
  refine ⟨fun k => ((hx k).toFinset.sort.map fun i => projection k (x i)).prod, ?_⟩
  apply (mem_completedGroup_iff F _).mpr
  intro k l h
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, map_projection]
  apply Finset.prod_map_sort_eq_of_ne_one
  intro i hi
  simp only [Set.Finite.mem_toFinset, Function.mem_mulSupport]
  refine iff_of_true ?_ hi
  intro hil
  apply hi
  rw [← map_projection k l h (x i), hil, map_one]

/-- The projection of an ordered product is the sorted product of its nonidentity
factors at that order. -/
@[simp]
theorem projection_orderedProduct (x : ι → completedGroup F) (hx : HasFiniteSupport x)
    (k : ℕ) :
    projection k (orderedProduct x hx) =
      ((hx k).toFinset.sort.map fun i => projection k (x i)).prod := by
  rw [projection_apply]
  rfl

/-- Any finite set containing the order-`k` support computes that projection. -/
theorem projection_orderedProduct_eq_prod (x : ι → completedGroup F)
    (hx : HasFiniteSupport x) (k : ℕ) (s : Finset ι)
    (hs : ∀ i, projection k (x i) ≠ 1 → i ∈ s) :
    projection k (orderedProduct x hx) = (s.sort.map fun i => projection k (x i)).prod := by
  classical
  rw [projection_orderedProduct]
  apply Finset.prod_map_sort_eq_of_ne_one
  intro i hi
  exact iff_of_true ((hx k).mem_toFinset.mpr hi) (hs i hi)

/-- The finite-order formulas uniquely determine the ordered product. -/
theorem orderedProduct_unique (x : ι → completedGroup F) (hx : HasFiniteSupport x)
    (y : completedGroup F)
    (hy : ∀ k, projection k y =
      ((hx k).toFinset.sort.map fun i => projection k (x i)).prod) :
    y = orderedProduct x hx := by
  ext k
  exact (hy k).trans (projection_orderedProduct x hx k).symm

/-- A family supported on a fixed finite set is multiplied in increasing order. -/
theorem orderedProduct_eq_prod (x : ι → completedGroup F) (hx : HasFiniteSupport x)
    (s : Finset ι) (hs : ∀ i, x i ≠ 1 → i ∈ s) :
    orderedProduct x hx = (s.sort.map x).prod := by
  ext k
  rw [projection_orderedProduct_eq_prod x hx k s (fun i hi => hs i (by
    intro h; apply hi; rw [h, map_one])), map_list_prod, List.map_map]
  rfl

/-- The ordered product of identity factors is the identity, including the empty family. -/
@[simp]
theorem orderedProduct_one (hx : HasFiniteSupport (fun _ : ι => (1 : completedGroup F))) :
    orderedProduct (fun _ : ι => (1 : completedGroup F)) hx = 1 := by
  apply (orderedProduct_eq_prod _ hx ∅ (by simp)).trans
  simp

variable [LinearOrder κ]

/-- Increasing reindexing preserves the product if all omitted factors are identities.
In particular this applies to order isomorphisms and to deleting identity factors. -/
theorem orderedProduct_comp (x : ι → completedGroup F) (hx : HasFiniteSupport x)
    (e : κ ↪o ι) (he : ∀ i, x i ≠ 1 → i ∈ Set.range e) :
    orderedProduct (x ∘ e) (hx.comp e.injective) = orderedProduct x hx := by
  classical
  ext k
  let s := ((hx.comp e.injective) k).toFinset
  rw [projection_orderedProduct, projection_orderedProduct_eq_prod x hx k
    (s.map e.toEmbedding) (by
      intro i hi
      obtain ⟨j, rfl⟩ := he i (by intro h; apply hi; rw [h, map_one])
      exact Finset.mem_map.mpr ⟨j, (hx.comp e.injective k).mem_toFinset.mpr hi, rfl⟩)]
  rw [← StrictMonoOn.map_finsetSort e.toEmbedding s (e.strictMono.strictMonoOn _), List.map_map]
  rfl

/-- A map of reindexed towers carries an ordered product to the ordered product
of the images, with the same ordering of factors. -/
theorem map_orderedProduct (x : ι → completedGroup F) (hx : HasFiniteSupport x)
    (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G) :
    map ρ f (orderedProduct x hx) =
      orderedProduct (fun i => map ρ f (x i)) (hx.map ρ f) := by
  classical
  ext k
  rw [projection_map, projection_orderedProduct_eq_prod _ (hx.map ρ f) k
    (hx (ρ k)).toFinset (by
      intro i hi
      apply (hx (ρ k)).mem_toFinset.mpr
      intro h
      apply hi
      simp [h])]
  rw [projection_orderedProduct, map_list_prod, List.map_map]
  simp only [Function.comp_def, projection_map]

end Mei.CompletedGroup
