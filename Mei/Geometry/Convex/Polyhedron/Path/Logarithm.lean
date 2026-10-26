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
# Logarithms of wall path products

If the crossed labels lie in the BCH subgroup of a Lie subalgebra, the logarithm
of transport differs from the signed sum of wall logarithms by a submodule
containing all brackets of that subalgebra. Only labels actually crossed by the
path need lie in the subgroup. Simultaneous walls retain their separate factors,
and repeated visits retain their separate contributions.

The result applies `LieSubalgebra.log_list_prod_sub_sum_mem` to the existing
signed-event expansion of transport. This allows the nonlinear part of joint
transport to be studied separately from geometric cancellation of its linear part.
-/

public section

noncomputable section

open Mei Mei.Convex WallComplement BCHGroup

namespace Quiver.Path

variable {V ι R L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [LieRing.IsNilpotent L]
  {W : ι → Set V} {x y : WallComplement W}

/-- Modulo a submodule containing the brackets of a Lie subalgebra, the logarithm
of wall transport is its signed linear crossing sum. Subgroup membership is
required only for wall indices appearing in the path's actual crossing events. -/
theorem log_wallPathProduct_sub_wallCrossingSum_mem (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → BCHGroup L)
    (hcomm : ∀ a b, affineSpan ℝ (W a) = affineSpan ℝ (W b) →
      Commute (label a) (label b))
    (K : LieSubalgebra R L) (J : Submodule R L)
    (hJ : ∀ u ∈ K, ∀ v ∈ K, ⁅u, v⁆ ∈ J)
    (hlabel : ∀ S ∈ p.signedCrossingEvents ν, ∀ a ∈ S, label a.1 ∈ K.bchSubgroup) :
    log (p.wallPathProduct ν label hcomm) -
      p.wallCrossingSum ν (fun j => log (label j)) ∈ J := by
  classical
  let l := (p.signedCrossingEvents ν).reverse.flatMap
    (fun S => S.toList.map (fun a => label a.1 ^ a.2))
  have hl : ∀ g ∈ l, g ∈ K.bchSubgroup := by
    intro g hg
    obtain ⟨S, hS, hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact K.bchSubgroup.zpow_mem
      (hlabel S (List.mem_reverse.mp hS) a (Finset.mem_toList.mp ha)) _
  have hp : l.prod = p.wallPathProduct ν label hcomm := by
    rw [wallPathProduct_eq_prod_signedCrossingEvents]
    simp [l, List.flatMap_def, List.prod_flatten, Function.comp_def]
  have hs : (l.map log).sum = p.wallCrossingSum ν (fun j => log (label j)) := by
    simp only [l, List.flatMap_def, List.map_flatten, List.sum_flatten,
      List.map_map, List.map_reverse, List.sum_reverse, Function.comp_def, wallCrossingSum_def]
    congr 1
    apply List.map_congr_left
    intro S _
    simp only [log_zpow]
    rw [← List.sum_toFinset _ (Finset.nodup_toList S)]
    simp
  simpa only [hp, hs] using K.log_list_prod_sub_sum_mem J hJ hl

end Quiver.Path
