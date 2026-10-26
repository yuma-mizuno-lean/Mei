/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product
public import Mei.Geometry.Convex.Polyhedron.Path.Sum
public import Mei.Algebra.Lie.BCH.Subgroup

/-!
# Logarithms of polygonal wall transport

The logarithm of wall transport differs from the signed sum of the individual
wall logarithms by brackets. More precisely, if the crossed labels belong to the
BCH subgroup of a Lie subalgebra, the difference lies in any submodule containing
its brackets. Only labels actually encountered by the path are constrained.
Simultaneous coplanar crossings retain all indexed factors.

The proof uses `LieSubalgebra.log_list_prod_sub_sum_mem` on the finite factors of
each segment and `LieSubalgebra.bch_sub_add_mem` on concatenations. The geometric
products and additive sums are the existing `Quiver.Path.wallPathProduct` and
`Quiver.Path.wallCrossingSum`.
-/

public section

noncomputable section

open Mei Mei.Convex WallComplement BCHGroup

namespace LieSubalgebra

variable {V ι R L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [LieRing.IsNilpotent L]
  {W : ι → Set V} {x y : WallComplement W}

/-- The logarithm of polygonal transport is its signed linear crossing sum modulo
any submodule containing the brackets of the Lie subalgebra of crossed labels. -/
theorem log_wallPathProduct_sub_crossingSum_mem (K : LieSubalgebra R L) (J : Submodule R L)
    (hJ : ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ J)
    (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → BCHGroup L)
    (comm : ∀ a b, affineSpan ℝ (W a) = affineSpan ℝ (W b) →
      Commute (label a) (label b)) (p : AdmissiblePLPath x y)
    (hp : ∀ S ∈ p.signedCrossingEvents ν, ∀ a ∈ S, label a.1 ∈ K.bchSubgroup) :
    log (p.wallPathProduct ν label comm) -
      p.wallCrossingSum ν (fun j => log (label j)) ∈ J := by
  classical
  -- First flatten the finite signed factors of one segment.
  have segment {u v : WallComplement W} (e : u ⟶ v)
      (he : ∀ S ∈ segmentCrossingEvents ν e, ∀ a ∈ S, label a.1 ∈ K.bchSubgroup) :
      segmentPathProduct ν label comm e ∈ K.bchSubgroup ∧
        log (segmentPathProduct ν label comm e) -
          e.toPath.wallCrossingSum ν (fun j => log (label j)) ∈ J := by
    let factors (t : ℝ) := (signedCrossingEvent ν u v t).toList.map
      (fun a => label a.1 ^ a.2)
    let l := (orderedCrossingTimes e).reverse.flatMap factors
    have hl : ∀ g ∈ l, g ∈ K.bchSubgroup := by
      intro g hg
      obtain ⟨t, ht, hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      exact K.bchSubgroup.zpow_mem
        (he _ (by simpa [segmentCrossingEvents_def] using
          List.mem_map.mpr ⟨t, List.mem_reverse.mp ht, rfl⟩) _ (Finset.mem_toList.mp ha)) _
    have hprod : segmentPathProduct ν label comm e = l.prod := by
      rw [segmentPathProduct_def]
      simp only [l, List.flatMap_def, List.prod_flatten, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t _
      exact crossingEventProduct_eq_prod ν label comm e t _
        (Finset.nodup_toList _) (fun _ => Finset.mem_toList)
    -- Reversal affects multiplication order but not the additive logarithmic sum.
    have hsum : (l.map log).sum = e.toPath.wallCrossingSum ν (fun j => log (label j)) := by
      simp only [l, factors, List.flatMap_def, List.map_flatten, List.sum_flatten,
        List.map_map, List.map_reverse, List.sum_reverse,
        Quiver.Path.wallCrossingSum_def, segmentCrossingEvents_def, Quiver.Hom.toPath,
        Quiver.Path.signedCrossingEvents_cons, Quiver.Path.signedCrossingEvents_nil,
        List.nil_append]
      congr 1
      apply List.map_congr_left
      intro t _
      simp [Function.comp_def, log_zpow]
    rw [hprod]
    exact ⟨K.bchSubgroup.list_prod_mem hl, hsum ▸ K.log_list_prod_sub_sum_mem J hJ hl⟩
  -- Concatenation adds one BCH bracket remainder and the two existing remainders.
  have main : p.wallPathProduct ν label comm ∈ K.bchSubgroup ∧
      log (p.wallPathProduct ν label comm) -
        p.wallCrossingSum ν (fun j => log (label j)) ∈ J := by
    induction p with
    | nil => simp
    | @cons y z p e ih =>
      simp only [Quiver.Path.signedCrossingEvents_cons, List.mem_append] at hp
      have hp' := fun S hS a ha => hp S (Or.inl hS) a ha
      have he := segment e (fun S hS a ha => hp S (Or.inr hS) a ha)
      obtain ⟨hpmem, hprest⟩ := ih hp'
      refine ⟨by simpa using K.bchSubgroup.mul_mem he.1 hpmem, ?_⟩
      have h := J.add_mem (J.add_mem
        (K.bch_sub_add_mem J hJ (mem_bchSubgroup K _ |>.mp he.1)
          (mem_bchSubgroup K _ |>.mp hpmem)) he.2) hprest
      rw [Quiver.Path.wallPathProduct_cons, log_mul,
        ← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.wallCrossingSum_comp]
      convert h using 1; abel
  exact main.2

end LieSubalgebra
