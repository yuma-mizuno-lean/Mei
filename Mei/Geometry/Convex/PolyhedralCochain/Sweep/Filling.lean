/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.Boundary

/-!
# Outgoing fillings of finite transverse cycles

A finite transverse presentation whose signed facet sum vanishes admits a finite
outgoing filling: sweep its cells in the negative lattice direction, keeping their
coefficients and contracted orientations. The signed facet sum of the filling is
the negative of the original cochain. Every cell occurring in the filling has
the positive lattice direction outside its recession cone.

More generally, `exists_sweep_presentation` realizes the cochain sweep by a finite
presentation and gives its boundary formula, including the swept boundary term.
Closedness means that `coboundaryOfFinsupp` vanishes in polyhedral cochains; it
does not require cancellation of the formal facet presentation. No coboundary on
the quotient of source presentations is assumed or constructed here.

The construction assembles `OrientedCell.cellCoboundary_sweep_add_sweep_cellCoboundary`
and `OrientedCell.sweep_strictlyOutgoing`, using the existing linear sweep on
transverse cochains. This is the finite cycle-filling argument used for central
wall corrections in Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, proof of Theorem 2.6.
-/

public section

noncomputable section

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

/-- Realize the sweep by a finite presentation of actual swept cells. Its signed
boundary satisfies the sweep homotopy formula in cochains, and all its nonzero
cells are outgoing in the positive sweeping direction. Coincident swept cells
are combined by addition of their coefficients. -/
theorem exists_sweep_presentation (n : N) (f : OrientedCell h (k + 1) →₀ E)
    (hf : ∀ σ ∈ f.support, i n ∉ (affineSpan ℝ σ.carrier).direction) :
    ∃ g : OrientedCell h k →₀ E,
      ofFinsupp (R := R) g = sweep n
        ⟨ofFinsupp f, (mem_transverseSubmodule_iff_exists (i n) _).mpr ⟨f, hf, rfl⟩⟩ ∧
      coboundaryOfFinsupp (R := R) g + sweep n
        ⟨coboundaryOfFinsupp (R := R) f, coboundaryOfFinsupp_mem_transverseSubmodule (i n) f hf⟩ =
          -ofFinsupp (R := R) f ∧
      ∀ τ ∈ g.support, ∃ (σ : OrientedCell h (k + 1)) (hσ : σ ∈ f.support),
        τ = σ.sweep n (hf σ hσ) ∧
          i n ∉ Set.recessionCone τ.carrier := by
  classical
  let g : OrientedCell h k →₀ E :=
    ∑ σ : f.support, Finsupp.single (σ.val.sweep n (hf σ.val σ.property)) (f σ.val)
  have hboundary : coboundaryOfFinsupp (R := R) f =
      ∑ σ : f.support, σ.val.cellCoboundary (f σ.val) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    simp only [Finsupp.sum, map_sum, coboundaryOfFinsupp_single]
    exact (Finset.sum_attach f.support _).symm
  have hbase : ofFinsupp (R := R) f = ∑ σ : f.support, mk σ.val (f σ.val) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    simp only [Finsupp.sum, map_sum, ofFinsupp_single]
    exact (Finset.sum_attach f.support _).symm
  have htrans : (⟨coboundaryOfFinsupp (R := R) f,
      coboundaryOfFinsupp_mem_transverseSubmodule (i n) f hf⟩ :
      transverseSubmodule (i n)) =
      ∑ σ : f.support, ⟨σ.val.cellCoboundary (f σ.val),
        σ.val.cellCoboundary_mem_transverseSubmodule (i n)
          (hf σ.val σ.property) (f σ.val)⟩ := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using hboundary
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [sweep_ofFinsupp n f hf]
    simp only [g, map_sum, ofFinsupp_single]
  · rw [htrans, map_sum]
    simp only [map_sum, coboundaryOfFinsupp_single]
    rw [← Finset.sum_add_distrib]
    simp only [OrientedCell.cellCoboundary_sweep_add_sweep_cellCoboundary,
      Finset.sum_neg_distrib, ← hbase]
  · intro τ hτ
    dsimp only [g] at hτ
    obtain ⟨σ, _, hσ⟩ := Finsupp.mem_support_finsetSum τ hτ
    have he : τ = σ.val.sweep n (hf σ.val σ.property) :=
      ((Finsupp.mem_support_single _ _ _).mp hσ).1
    exact ⟨σ.val, σ.property, he, he.symm ▸ σ.val.sweep_strictlyOutgoing n
      (hf σ.val σ.property)⟩

/-- A closed finite transverse presentation has a finite outgoing filling whose
signed boundary cancels it. The filling represents its canonical cochain sweep;
its boundary is an equality in cochains, including subdivision relations. -/
theorem exists_outgoing_filling_of_coboundary_eq_zero (n : N)
    (f : OrientedCell h (k + 1) →₀ E)
    (hf : ∀ σ ∈ f.support, i n ∉ (affineSpan ℝ σ.carrier).direction)
    (hclosed : coboundaryOfFinsupp (R := R) f = 0) :
    ∃ g : OrientedCell h k →₀ E,
      ofFinsupp (R := R) g = sweep n
        ⟨ofFinsupp f, (mem_transverseSubmodule_iff_exists (i n) _).mpr ⟨f, hf, rfl⟩⟩ ∧
      coboundaryOfFinsupp (R := R) g = -ofFinsupp (R := R) f ∧
      ∀ τ ∈ g.support, i n ∉ Set.recessionCone τ.carrier := by
  obtain ⟨g, hg, hd, hout⟩ := exists_sweep_presentation (R := R) n f hf
  have hz : (⟨coboundaryOfFinsupp (R := R) f,
      coboundaryOfFinsupp_mem_transverseSubmodule (i n) f hf⟩ :
      transverseSubmodule (i n)) = 0 := Subtype.ext hclosed
  rw [hz, map_zero, add_zero] at hd
  exact ⟨g, hg, hd, fun τ hτ => (hout τ hτ).choose_spec.2.2⟩

end Mei.PolyhedralCochain
