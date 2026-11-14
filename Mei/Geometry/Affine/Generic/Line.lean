/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Generic
public import TauCeti.LinearAlgebra.AffineSpace.Transverse
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Finite exceptional times on affine lines

An affine line starting outside an affine obstacle meets it at most once. Thus a
line starting at a generic point of a finite exceptional arrangement has only
finitely many nongeneric parameter values. The other endpoint can be arbitrary;
a constant line at a generic point has no exceptional times.
-/

public section


namespace TauCeti.ExceptionalArrangement

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A function locally constant near generic points is constant on every
preconnected parameter set avoiding the finitely many nongeneric times of a line
starting at a generic point. The event set is exactly the nongeneric times. -/
theorem exists_lineEvents {X : Type*} (E : ExceptionalArrangement ℝ V) (g : V → X)
    (hstable : ∀ x, E.IsGeneric x → ∀ᶠ x' in nhds x, g x' = g x)
    {x : V} (hx : E.IsGeneric x) (y : V) :
    ∃ A : Finset ℝ,
      (∀ t, t ∈ A ↔ ¬ E.IsGeneric (AffineMap.lineMap x y t)) ∧
      ∀ B : Set ℝ, IsPreconnected B → (∀ t ∈ B, t ∉ A) →
        ∀ s ∈ B, ∀ t ∈ B, g (AffineMap.lineMap x y s) = g (AffineMap.lineMap x y t) := by
  classical
  let hfinite := E.finite_setOf_not_isGeneric_lineMap hx y
  refine ⟨hfinite.toFinset, fun t => hfinite.mem_toFinset, ?_⟩
  intro B hB havoid s hs t ht
  let : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp hB
  let L (b : B) := g (AffineMap.lineMap x y (b : ℝ))
  have hc : Continuous (fun b : B => AffineMap.lineMap x y (b : ℝ)) :=
    AffineMap.lineMap_continuous.comp continuous_subtype_val
  have hlocal : IsLocallyConstant L := by
    apply (IsLocallyConstant.iff_eventually_eq L).mpr
    intro b
    have hgeneric : E.IsGeneric (AffineMap.lineMap x y (b : ℝ)) := by
      by_contra hn
      exact havoid b b.property (hfinite.mem_toFinset.mpr hn)
    exact hc.continuousAt.tendsto.eventually (hstable _ hgeneric)
  exact hlocal.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

end Topology

end TauCeti.ExceptionalArrangement
