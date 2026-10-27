/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Sweep

/-!
# Outgoing walls from homogeneous swept coefficients

A rational-normal polyhedron swept in a transverse lattice direction supports an
outgoing directed wall whenever its enlarged tangent space is the kernel of a
nonzero integral normal. A homogeneous coefficient in that normal's wall space
gives its completed exponential label. The support is swept by an actual positive
degree, while the wall is indexed by its supported primitive ray; saturation of
the positive monoid is unnecessary. The label vanishes at every smaller cutoff.

The construction combines `Mei.Convex.vectorSpan_sweep`,
`Mei.Convex.sweep_strictlyOutgoing`, rational negative-ray addition, and
`DirectedWallSpaces.expToCompletion_mem_wallGroup`. These are the individual
homogeneous walls used in the outgoing correction construction of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6. No cancellation or consistency assertion is made here.
-/

public section

noncomputable section

open Set

namespace Mei.DirectedWall

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

/-- A transverse swept polyhedron with a homogeneous wall coefficient gives an
actual outgoing wall. Its normal, supported ray, support and label are prescribed,
and it is invisible below the coefficient's degree. -/
theorem exists_outgoing_sweep {P : Set V} (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty) {n : Γ} {w : SupportedRay d} (hn : n ∈ w.rayDegrees)
    (htrans : i (ρ n) ∉ (affineSpan ℝ P).direction)
    {m : Λ →+ ℤ} (hm : m ≠ 0)
    (hker : (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i (ρ n))
    {a : L} (ha : a ∈ H.wall n m) :
    ∃ W : DirectedWall (d := d) h H,
      W.normal = m ∧ W.ray = w ∧ W.support = Convex.sweep P (i (ρ n)) ∧
      W.label = d.expToCompletion ℒ a ∧ W.Outgoing ∧
      ∀ l : ℕ, (l : ℤ) < d.degree n → CompletedGroup.projection l W.label = 1 := by
  have hmn : m (ρ n) = 0 := by
    have hv : i (ρ n) ∈ (h.realCharacter m).ker :=
      hker ▸ (le_sup_right : ℝ ∙ i (ρ n) ≤ _)
        (Submodule.mem_span_singleton_self _)
    simpa only [LinearMap.mem_ker, h.realCharacter_apply, Int.cast_eq_zero] using hv
  have hmw : m (ρ w.generator) = 0 := by
    obtain ⟨-, b, hb, hnb⟩ := SupportedRay.mem_rayDegrees.mp hn
    have hb0 : b ≠ 0 := ne_of_gt hb
    rw [hnb, map_zsmul, map_zsmul, zsmul_eq_mul] at hmn
    exact (mul_eq_zero.mp hmn).resolve_left hb0
  let W : DirectedWall (d := d) h H :=
    { normal := m
      normal_ne_zero := hm
      ray := w
      normal_direction := hmw
      support := Convex.sweep P (i (ρ n))
      support_nonempty := Convex.sweep_nonempty hne _
      rational_support := hP.sweep (ρ n)
      direction_support := by
        rw [direction_affineSpan, Convex.vectorSpan_sweep hne, ← direction_affineSpan, hker]
      label := d.expToCompletion ℒ a
      label_mem := H.expToCompletion_mem_wallGroup (H.wall_le_raySubmodule w m hn ha) }
  refine ⟨W, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [W.outgoing_iff]
    intro hrec
    have hinc := W.incoming_iff.mpr (mem_recessionCone.mp hrec)
    have hrec := (W.incoming_iff_of_mem_rayDegrees hn).mp hinc
    exact Convex.sweep_strictlyOutgoing hne
      (by simpa only [direction_affineSpan] using htrans) ((mem_recessionCone).mp hrec)
  · intro l hl
    have hz := (d.degreeIdeal ℒ l).mkQ_eq_zero.mpr
      (d.le_degreeIdeal ℒ hl (H.wall_le_piece n m ha))
    exact (d.projection_expToCompletion ℒ l a).trans (by rw [hz, BCHGroup.exp_zero]; rfl)

end Mei.DirectedWall
