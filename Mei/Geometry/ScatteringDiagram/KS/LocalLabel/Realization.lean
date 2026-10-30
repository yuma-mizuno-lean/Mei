/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel
public import Mei.Geometry.Convex.PolyhedralComplex.Generic

/-!
# Realizing finite wall labels by completed germs

Every finite wall label of a completed KS diagram is the projection of a
completed local label at a point on that wall regular at every cutoff. The
point can be chosen in any open patch meeting the wall's intrinsic interior.
For a nonidentity finite label, the completed germ belongs to the supported
ray of that wall. In particular, all completed germs are trivial exactly when
all finite wall labels are trivial.

This realizes finite wall data inside the actual completed diagram rather
than choosing unrelated algebraic lifts. It requires neither consistency nor
stabilization or refinement of the complexes. The construction combines
`FinitePolyhedralComplex.exists_mem_wall_notMem_singularSupport` with
`CompletedDiagram.germLabel` and its projection and supported-ray theorems.
The local-wall interpretation follows Bridgeland, *Scattering diagrams, Hall
algebras and stability conditions*, Definition 2.3 and §§2.9–2.11
(arXiv:1603.00416v4), and Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.CompletedDiagram

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {C : ℕ → FinitePolyhedralComplex h} (D : CompletedDiagram s d ℒ C)

/-- A finite wall label is realized by a completed germ in every open patch
of its intrinsic interior. The realizing point is regular at all orders. -/
theorem exists_germLabel_projection_eq (k : ℕ) (P : (C k).walls)
    {U : Set V} (hU : IsOpen U)
    (hne : (U ∩ intrinsicInterior ℝ (P : Set V)).Nonempty) :
    ∃ θ ∈ U ∩ intrinsicInterior ℝ (P : Set V),
      ∃ hθ : ∀ l, θ ∉ singularSupport (fun Q : (C l).walls => (Q : Set V)),
        CompletedGroup.projection k (D.germLabel θ hθ) = (D.diagram k).label P := by
  obtain ⟨θ, hθP, hθ⟩ := (C k).exists_mem_wall_notMem_singularSupport P C hU hne
  exact ⟨θ, hθP, hθ,
    D.projection_germLabel_of_mem θ hθ k P (intrinsicInterior_subset hθP.2)⟩

/-- Every nonidentity finite wall label is realized by a completed germ on
the same supported ray, with the point regular at every cutoff. -/
theorem exists_germLabel_mem_completedRaySubgroup [Module.Free ℤ N]
    (k : ℕ) (P : (C k).walls) (hP : (D.diagram k).label P ≠ 1) :
    ∃ θ ∈ intrinsicInterior ℝ (P : Set V),
      ∃ hθ : ∀ l, θ ∉ singularSupport (fun Q : (C l).walls => (Q : Set V)),
        D.germLabel θ hθ ∈ d.completedRaySubgroup ℒ ((D.diagram k).wallRay P) ∧
        CompletedGroup.projection k (D.germLabel θ hθ) = (D.diagram k).label P := by
  obtain ⟨θ, hθP, hθ⟩ :=
    (C k).exists_mem_intrinsicInterior_wall_notMem_singularSupport P C
  have hmem := intrinsicInterior_subset hθP
  exact ⟨θ, hθP, hθ, D.germLabel_mem_completedRaySubgroup θ hθ k P hmem hP,
    D.projection_germLabel_of_mem θ hθ k P hmem⟩

/-- Completed local labels detect triviality of every finite wall label,
even when the complexes change at every order. -/
theorem forall_germLabel_eq_one_iff :
    (∀ θ (hθ : ∀ l, θ ∉ singularSupport (fun Q : (C l).walls => (Q : Set V))),
      D.germLabel θ hθ = 1) ↔ ∀ k (P : (C k).walls), (D.diagram k).label P = 1 := by
  constructor
  · intro hg k P
    obtain ⟨θ, hθP, hθ⟩ :=
      (C k).exists_mem_intrinsicInterior_wall_notMem_singularSupport P C
    rw [← D.projection_germLabel_of_mem θ hθ k P (intrinsicInterior_subset hθP),
      hg θ hθ, map_one]
    -- The categorical tower fiber and the concrete BCH quotient share their identity.
    rfl
  · intro hlabels θ hθ
    rw [germLabel_eq_one_iff]
    intro k
    by_cases hp : ∃ P : (C k).walls, θ ∈ (P : Set V)
    · obtain ⟨P, hP⟩ := hp
      rw [(D.diagram k).localLabel_of_mem θ (hθ k) P hP, hlabels k P]
    · exact (D.diagram k).localLabel_of_notMem θ (hθ k) (by simpa using hp)

end Mei.CompletedDiagram
