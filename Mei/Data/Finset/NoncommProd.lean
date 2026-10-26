/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Finset.NoncommProd

/-!
# Reindexing and inversion of products of commuting elements

Mathlib's `Finset.noncommProd` multiplies a finite commuting family in an arbitrary
monoid. Here embeddings reindex these products, and inversion in a group inverts
each factor. These formulas allow unordered simultaneous wall crossings to be
transported and reversed without choosing an order on the walls.
-/

public section

namespace Finset

variable {α β G : Type*}

/-- Reindex a product of commuting elements along an embedding. -/
theorem noncommProd_map [Monoid G] (s : Finset α) (e : α ↪ β) (f : β → G)
    (comm : (s.map e : Set β).Pairwise (fun a b => Commute (f a) (f b))) :
    (s.map e).noncommProd f comm = s.noncommProd (fun a => f (e a))
      (fun a ha b hb hab => comm (mem_map.mpr ⟨a, ha, rfl⟩)
        (mem_map.mpr ⟨b, hb, rfl⟩) (e.injective.ne hab)) := by
  simp only [noncommProd, map_val, Multiset.map_map, Function.comp_def]

/-- Inverting every member of a commuting family inverts its unordered product. -/
theorem noncommProd_inv [DivisionMonoid G] (s : Finset α) (f : α → G)
    (comm : (s : Set α).Pairwise (fun a b => Commute (f a) (f b))) :
    s.noncommProd (fun a => (f a)⁻¹) (fun _ ha _ hb hab => (comm ha hb hab).inv_inv) =
      (s.noncommProd f comm)⁻¹ := by
  induction s using Finset.cons_induction_on with
  | empty => exact (noncommProd_empty _ _).trans (inv_one.symm)
  | cons a s ha ih =>
    have hc : (s : Set α).Pairwise (fun a b => Commute (f a) (f b)) :=
      comm.mono (fun _ => mem_cons_of_mem)
    calc
      _ = (f a)⁻¹ * s.noncommProd (fun a => (f a)⁻¹)
          (fun _ hx _ hy hxy => (hc hx hy hxy).inv_inv) := noncommProd_cons _ _ _ _ _
      _ = (f a)⁻¹ * (s.noncommProd f hc)⁻¹ := by rw [ih]
      _ = (s.noncommProd f hc)⁻¹ * (f a)⁻¹ :=
        (noncommProd_commute s f hc (f a)
          (fun b hb => comm.forall₂ (mem_cons_self _ _) (mem_cons_of_mem hb))).inv_inv.eq
      _ = _ := by rw [noncommProd_cons, mul_inv_rev]

end Finset
