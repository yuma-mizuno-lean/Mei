/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Differential
public import Mei.Geometry.Convex.PolyhedralCochain.Transverse.Coboundary

/-!
# The coboundary on transverse cochains

The polyhedral coboundary preserves the submodule of cochains transverse to any
fixed vector. Its restriction `PolyhedralCochain.transverseCoboundary` squares to
zero and commutes with coefficient maps. This lets the swept boundary term in a
sweep homotopy be stated directly on cochains, independently of presentations.

Preservation uses `coboundaryOfFinsupp_mem_transverseSubmodule` on a transverse
presentation supplied by `mem_transverseSubmodule_iff_exists`. The restriction
uses Mathlib's `LinearMap.restrict`; its square-zero law is inherited from the
ordinary polyhedral coboundary. No lattice condition on the vector is needed.
-/

public section

noncomputable section

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E E' : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] {k : ℕ}

/-- The coboundary of a transverse cochain is transverse to the same vector. -/
theorem coboundary_mem_transverseSubmodule (v : V) (C : PolyhedralCochain R h E k)
    (hC : C ∈ transverseSubmodule v) : coboundary C ∈ transverseSubmodule v := by
  obtain ⟨f, hf, rfl⟩ := (mem_transverseSubmodule_iff_exists v C).mp hC
  rw [coboundary_ofFinsupp]
  exact coboundaryOfFinsupp_mem_transverseSubmodule v f hf

/-- Restrict the polyhedral coboundary to cochains transverse to a fixed vector.
The inclusion in ordinary cochains commutes with this restricted coboundary. -/
def transverseCoboundary (v : V) :
    transverseSubmodule (R := R) (h := h) (E := E) (k := k) v →ₗ[R]
      transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) v :=
  coboundary.restrict (coboundary_mem_transverseSubmodule v)

/-- The restricted coboundary has the same underlying cochain as the ordinary one. -/
@[simp]
theorem coe_transverseCoboundary (v : V)
    (C : transverseSubmodule (R := R) (h := h) (E := E) (k := k) v) :
    (transverseCoboundary v C : PolyhedralCochain R h E (k + 1)) =
      coboundary (C : PolyhedralCochain R h E k) := (rfl)

/-- A transverse generator has its signed facet sum as restricted coboundary. -/
@[simp]
theorem transverseCoboundary_mk (v : V) (σ : OrientedCell h k)
    (hv : v ∉ (affineSpan ℝ σ.carrier).direction) (c : E) :
    transverseCoboundary v ⟨mk (R := R) σ c, mk_mem_transverseSubmodule v σ hv c⟩ =
      ⟨σ.cellCoboundary c, σ.cellCoboundary_mem_transverseSubmodule v hv c⟩ := by
  apply Subtype.ext
  simp

/-- The restricted coboundary squares to zero, including for torsion coefficients. -/
@[simp]
theorem transverseCoboundary_transverseCoboundary (v : V)
    (C : transverseSubmodule (R := R) (h := h) (E := E) (k := k) v) :
    transverseCoboundary v (transverseCoboundary v C) = 0 := by
  apply Subtype.ext
  simp

/-- Coefficient maps commute with the restricted coboundary. -/
@[simp]
theorem transverseMap_transverseCoboundary (f : E →ₗ[R] E') (v : V)
    (C : transverseSubmodule (R := R) (h := h) (E := E) (k := k) v) :
    transverseMap f v (transverseCoboundary v C) =
      transverseCoboundary v (transverseMap f v C) := by
  apply Subtype.ext
  simp

end Mei.PolyhedralCochain
