/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Convex.Polyhedron.SignCell

/-!
# Rational-normal sign cells

Signing and doubling rational-normal affine inequalities gives rational-normal
weak sign cells. Consequently the closures of realized sign cells have finite
rational-normal presentations, including when the offsets are irrational.
-/

public section

namespace Mei.Convex

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite ι]

/-- Weak cells of a finite rational-normal affine arrangement are rational-normal
polyhedra. Equality rows are represented by opposite inequalities. -/
theorem isRationalNormalPolyhedron_weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (σ : ι → SignType) : IsRationalNormalPolyhedron h (weakSignCell g σ) := by
  have hrows : ∀ p, Toric.IsRationalFunctional h
      (weakSignCellRows g σ p).toAffineMap.linear := by
    rintro ⟨j, b⟩
    cases hs : σ j <;> cases b <;>
      simp only [weakSignCellRows_eq, hs, Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact hg j | exact (hg j).neg
  refine isRationalNormalPolyhedron_iff.mpr
    ⟨RationalAffinePolyhedron.ofFinite (weakSignCellRows g σ) hrows, ?_⟩
  ext x
  rw [RationalAffinePolyhedron.mem_carrier_ofFinite, mem_weakSignCell_iff_rows]

/-- Every realized closed cell of a finite rational-normal arrangement admits a
rational-normal presentation. No rationality of offsets is required. -/
theorem isRationalNormalPolyhedron_of_mem_realizedSignCellClosures
    {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    {P : Set V} (hP : P ∈ realizedSignCellClosures g) :
    IsRationalNormalPolyhedron h P := by
  obtain ⟨σ, hσ, rfl⟩ := mem_realizedSignCellClosures.mp hP
  rw [closure_signCell hσ]
  exact isRationalNormalPolyhedron_weakSignCell g hg σ

end Mei.Convex
