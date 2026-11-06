/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Tangent.Transport

/-!
# Consistency of incident tangent diagrams

At every point of a consistent directed diagram, the diagram of incident tangent
walls is consistent. The statement holds separately at each finite cutoff, so it also
applies to diagrams known consistent only through a specified order. Supports may be
bounded or have lineality; tangent supports need not be full hyperplanes.

For two finite tangent paths, `eventually_exists_tangentAt_path` realizes both inside
the original diagram at a common positive scale, with equal corresponding endpoints
and unchanged products. Endpoint independence in the original diagram then identifies
the tangent products. For the scattering-diagram conventions, see Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, §2.1.
-/

public section

open Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι}

/-- Consistency at a fixed cutoff passes to the incident tangent diagram at every point. -/
theorem LevelConsistent.tangentAt {k : ℕ} (hD : D.LevelConsistent k) (x : V) :
    (D.tangentAt x).LevelConsistent k := by
  rw [levelConsistent_def] at hD ⊢
  intro u v p q
  obtain ⟨r, hp, hq⟩ := ((D.eventually_exists_tangentAt_path k p).and
    (D.eventually_exists_tangentAt_path k q)).exists
  obtain ⟨u', v', p', hu, hv, _, hp⟩ := hp
  obtain ⟨u'', v'', q', hu', hv', _, hq⟩ := hq
  have huu : u'' = u' := WallComplement.ext (hu'.trans hu.symm)
  have hvv : v'' = v' := WallComplement.ext (hv'.trans hv.symm)
  subst u'' v''
  exact hp.symm.trans ((hD p' q').trans hq)

/-- Every incident tangent diagram of a consistent directed diagram is consistent. -/
theorem Consistent.tangentAt (hD : D.Consistent) (x : V) : (D.tangentAt x).Consistent := by
  rw [consistent_iff] at hD ⊢
  exact fun k => (hD k).tangentAt x

end Mei.DirectedDiagram
