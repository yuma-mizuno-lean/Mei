/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Module.Submodule.Union
public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.Homotopy

/-!
# Exactness of polyhedral cochains in positive codimension

Every finite polyhedral cochain of positive codimension admits a common transverse
integral direction. Consequently every closed such cochain has a primitive,
represented by finitely many cells outgoing in that direction. No prescribed
direction or transversality hypothesis on the cochain is required.

This applies in particular to closed codimension-one crossing-defect cochains:
they can be represented as boundaries of polyhedral potentials. Evaluation of
these potentials at endpoints is the remaining geometric step in turning this
exactness statement into path independence of their intersection sums.

The integral-direction choice uses
`AddMonoidHom.exists_forall_apply_notMem_of_span_eq_top` and the integral lattice's
spanning property. Primitives come from
`PolyhedralCochain.exists_outgoing_sweep_presentation`, the finite-presentation
form of the negative-ray sweep homotopy. The direction depends on the finite
cochain presentation, so the primitive is not canonical.
-/

public section

noncomputable section

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

/-- Every positive-codimension cochain is transverse to some integral direction.
This is a property of the cochain class; no chosen presentation occurs in the
conclusion. -/
theorem exists_mem_transverseSubmodule (C : PolyhedralCochain R h E (k + 1)) :
    ∃ n : N, C ∈ transverseSubmodule (i n) := by
  classical
  have := h.finiteDimensional
  obtain ⟨f, rfl⟩ := ofFinsupp_surjective C
  obtain ⟨n, hn⟩ := i.exists_forall_apply_notMem_of_span_eq_top h.span_range_eq_top
    (fun σ : f.support => (affineSpan ℝ σ.val.carrier).direction) (fun σ he => by
      have hd := σ.val.finrank_direction_add
      rw [he, finrank_top] at hd
      omega)
  exact ⟨n, (mem_transverseSubmodule_iff_exists (i n) _).mpr
    ⟨f, fun σ hσ => hn ⟨σ, hσ⟩, rfl⟩⟩

/-- A closed positive-codimension cochain has a finite primitive presentation
whose cells are all outgoing in one integral direction. This direction is chosen
together with the primitive, rather than imposed on the source. -/
theorem exists_outgoing_primitive (C : PolyhedralCochain R h E (k + 1))
    (hC : coboundary C = 0) :
    ∃ (n : N) (g : OrientedCell h k →₀ E),
      coboundary (ofFinsupp (R := R) g) = C ∧
      ∀ τ ∈ g.support, i n ∉ Set.recessionCone τ.carrier := by
  obtain ⟨n, hn⟩ := exists_mem_transverseSubmodule C
  obtain ⟨g, _, hd, hout⟩ := exists_outgoing_sweep_presentation n ⟨C, hn⟩ hC
  refine ⟨n, -g, ?_, ?_⟩
  · rw [map_neg, map_neg, hd, neg_neg]
  · simpa only [Finsupp.support_neg] using hout

/-- A positive-codimension cochain is closed exactly when it is a coboundary.
Coefficients may have torsion, and the cells may be unbounded or have lineality. -/
theorem coboundary_eq_zero_iff_exists_coboundary (C : PolyhedralCochain R h E (k + 1)) :
    coboundary C = 0 ↔ ∃ B : PolyhedralCochain R h E k, coboundary B = C := by
  constructor
  · intro hC
    obtain ⟨_, g, hg, _⟩ := exists_outgoing_primitive C hC
    exact ⟨ofFinsupp g, hg⟩
  · rintro ⟨B, rfl⟩
    exact coboundary_coboundary B

end Mei.PolyhedralCochain
