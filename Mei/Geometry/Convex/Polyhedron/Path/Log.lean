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

The proof uses `Quiver.Path.wallPathProduct_eq_prod_signedCrossingEvents` to enumerate the
signed factors and `LieSubalgebra.log_list_prod_sub_sum_mem` to estimate their
product. The geometric products and additive sums are the existing
`Quiver.Path.wallPathProduct` and `Quiver.Path.wallCrossingSum`.
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
  let factors (S : Finset (ι × ℤ)) := S.toList.map (fun a => label a.1 ^ a.2)
  let l := (p.signedCrossingEvents ν).reverse.flatMap factors
  have hl : ∀ g ∈ l, g ∈ K.bchSubgroup := by
    intro g hg
    obtain ⟨S, hS, hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact K.bchSubgroup.zpow_mem
      (hp S (List.mem_reverse.mp hS) a (Finset.mem_toList.mp ha)) _
  have hprod : p.wallPathProduct ν label comm = l.prod := by
    rw [Quiver.Path.wallPathProduct_eq_prod_signedCrossingEvents]
    simp only [l, List.flatMap_def, List.prod_flatten, List.map_map, factors,
      Function.comp_def]
  -- Reversal affects multiplication order but not the additive logarithmic sum.
  have hsum : (l.map log).sum = p.wallCrossingSum ν (fun j => log (label j)) := by
    simp only [l, factors, List.flatMap_def, List.map_flatten, List.sum_flatten,
      List.map_map, List.map_reverse, List.sum_reverse, Quiver.Path.wallCrossingSum_def]
    congr 1
    apply List.map_congr_left
    intro S _
    simp [Function.comp_def, log_zpow]
  rw [hprod, ← hsum]
  exact K.log_list_prod_sub_sum_mem J hJ hl

end LieSubalgebra
