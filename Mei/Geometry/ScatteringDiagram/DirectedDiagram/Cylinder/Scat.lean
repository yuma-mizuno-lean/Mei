/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Cylinder.Class
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat

/-!
# Outgoing scattering commutes with cylinders

Completing a full-hyperplane input and then adjoining unrestricted spatial
coordinates gives the same scattering class as completing the cylinder input.
The comparison holds at every cutoff and identifies the two outgoing completion
constructions independently of their wall presentations.

This combines `IsOutgoingCompletion.cylinder`, `outgoingCompletion_unique` and
`scat_spec`. The outgoing completion theorem is Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Theorem 2.6, arXiv:1503.06183v5; the cylinder interpretation is used in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

universe u v

variable {Γ Λ K R V E : Type*} {L : Type v}
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup K]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ Λ × K} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {j : K →+ E} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (h' : TauCeti.Toric.IsIntegralLattice j)

variable {ι : Type u}
  (D : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) ι)
  (hfull : ∀ a, ∃ c : ℝ,
    (D.wall a).support = {x | h.realCharacter (D.wall a).normal x = c})

variable [Module.Free ℤ Γ]

/-- The canonical outgoing scattering class commutes with cylinder lifting. -/
theorem cylinder_scat :
    Class.cylinder h' (D.Scat hfull) =
      (D.cylinder h').Scat (D.cylinder_fullHyperplane h' hfull) := by
  obtain ⟨η, C, hC, hc⟩ := D.scat_spec hfull
  rw [hc, Class.cylinder_toClass]
  symm
  apply scat_eq_toClass
  have hinput : (D.cylinder h').wall = fun a => (D.wall a).cylinder h' :=
    funext (cylinder_wall D h')
  rw [hinput]
  exact hC.cylinder h'

/-- The scattering comparison uses the same cutoff before and after lifting. -/
theorem projection_cylinder_scat (k : ℕ) :
    ((D.cylinder h').Scat (D.cylinder_fullHyperplane h' hfull)).projection k =
      LevelClass.cylinder h' k ((D.Scat hfull).projection k) := by
  rw [← D.cylinder_scat h' hfull, Class.projection_cylinder]

end Mei.DirectedDiagram
