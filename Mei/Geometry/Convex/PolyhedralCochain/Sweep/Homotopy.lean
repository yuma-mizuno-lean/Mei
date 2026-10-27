/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Transverse.Differential
public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.Filling

/-!
# The sweep homotopy on polyhedral cochains

For every transverse cochain `C`, negative-ray sweeping satisfies
`d (Sₙ C) + Sₙ (d C) = -C`. Both the coboundary and sweep are operations on the
quotient by orientation and subdivision relations. In particular a transverse
cochain is closed exactly when the negative of its sweep is a primitive. A closed
cochain has a finite filling presentation consisting entirely of outgoing cells.

The homotopy descends
`OrientedCell.cellCoboundary_sweep_add_sweep_cellCoboundary` using the existing
linear sweep and restricted coboundary, with `transverse_hom_ext`. The outgoing
presentation uses `exists_sweep_presentation`. These are the polyhedral sweep
and cycle-filling argument in Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, proof of Theorem 2.6. Real offsets, unbounded
supports and lineality are allowed, over modules with arbitrary ring scalars.
-/

public section

noncomputable section

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

/-- The sweep homotopy on transverse cochains, with equality in ordinary cochains.
The swept coboundary uses the restricted coboundary on the transverse submodule. -/
theorem coboundary_sweep_add_sweep_coboundary (n : N)
    (C : transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) (i n)) :
    coboundary (sweep n C) + sweep n (transverseCoboundary (i n) C) =
      -(C : PolyhedralCochain R h E (k + 1)) := by
  have he : coboundary ∘ₗ sweep n + sweep n ∘ₗ transverseCoboundary (i n) =
      -(transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) (i n)).subtype := by
    apply transverse_hom_ext (i n)
    intro σ hn c
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply,
      Submodule.subtype_apply]
    rw [sweep_mk (R := R) n σ hn c, coboundary_mk,
      transverseCoboundary_mk (i n) σ hn c]
    exact σ.cellCoboundary_sweep_add_sweep_cellCoboundary (R := R) n hn c
  exact LinearMap.congr_fun he C

/-- Sweeping a closed transverse cochain gives a coboundary cancelling that cochain. -/
theorem coboundary_sweep_of_coboundary_eq_zero (n : N)
    (C : transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) (i n))
    (hC : coboundary (C : PolyhedralCochain R h E (k + 1)) = 0) :
    coboundary (sweep n C) = -(C : PolyhedralCochain R h E (k + 1)) := by
  have hz : transverseCoboundary (i n) C = 0 := by
    apply Subtype.ext
    simpa only [coe_transverseCoboundary, ZeroMemClass.coe_zero] using hC
  simpa only [hz, map_zero, add_zero] using coboundary_sweep_add_sweep_coboundary n C

/-- The canonical swept filling cancels the source precisely when it is closed. -/
theorem coboundary_sweep_eq_neg_iff (n : N)
    (C : transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) (i n)) :
    coboundary (sweep n C) = -(C : PolyhedralCochain R h E (k + 1)) ↔
      coboundary (C : PolyhedralCochain R h E (k + 1)) = 0 := by
  constructor
  · intro hC
    have he := congrArg coboundary hC
    simpa only [coboundary_coboundary, map_neg, zero_eq_neg] using he
  · exact coboundary_sweep_of_coboundary_eq_zero n C

/-- A closed transverse cochain has a finite outgoing presentation of its canonical
sweep. Its coboundary cancels the source, without choosing a source presentation
in the statement or requiring formal cancellation of signed facets. -/
theorem exists_outgoing_sweep_presentation (n : N)
    (C : transverseSubmodule (R := R) (h := h) (E := E) (k := k + 1) (i n))
    (hC : coboundary (C : PolyhedralCochain R h E (k + 1)) = 0) :
    ∃ g : OrientedCell h k →₀ E,
      ofFinsupp (R := R) g = sweep n C ∧
      coboundary (ofFinsupp (R := R) g) = -(C : PolyhedralCochain R h E (k + 1)) ∧
      ∀ τ ∈ g.support, i n ∉ Set.recessionCone τ.carrier := by
  obtain ⟨f, hf, he⟩ := (mem_transverseSubmodule_iff_exists (i n) _).mp C.property
  obtain ⟨g, hg, _, hout⟩ := exists_sweep_presentation (R := R) n f hf
  have hrep : (⟨ofFinsupp (R := R) f,
      (mem_transverseSubmodule_iff_exists (i n) _).mpr ⟨f, hf, rfl⟩⟩ :
      transverseSubmodule (i n)) = C := Subtype.ext he
  rw [hrep] at hg
  refine ⟨g, hg, ?_, fun τ hτ => (hout τ hτ).choose_spec.2.2⟩
  rw [hg]
  exact coboundary_sweep_of_coboundary_eq_zero n C hC

end Mei.PolyhedralCochain
