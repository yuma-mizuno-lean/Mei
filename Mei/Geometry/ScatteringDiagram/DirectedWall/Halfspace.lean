/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Analysis.Convex.Halfspace

/-!
# Cutting directed walls by half-spaces

Let `W` be a directed wall and `μ` an integral functional with real extension `ℓ`. If some
support point `x` of `W` satisfies `a < ℓ x`, the cut `W.support ∩ {a ≤ ℓ}` is again the support
of a directed wall with the normal, ray and label of `W` (`DirectedWall.cutHalfspace`). It is a
rational-normal polyhedron, and it spans the same affine subspace as `W.support`, because it
contains a strictly feasible point (`AffineMap.affineSpan_inter_le_eq`). For example, cutting a
full affine hyperplane gives a half-hyperplane, and in the plane a half-line.

Incomingness asks that the support be preserved by the geometric degree direction
`v = i(ρ w)`. A cut of an incoming wall is incoming exactly when `μ(ρ w) ≥ 0`
(`DirectedWall.incoming_cutHalfspace_iff`). The condition is necessary for every cut, of an
incoming wall or not: when `μ(ρ w) < 0`, the ray in direction `v` from a strictly feasible point
leaves the half-space (`DirectedWall.nonneg_of_incoming_cutHalfspace`). In particular, whether
the cut of an incoming wall is incoming does not depend on the offset `a`.

The directed walls and their incomingness follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Definition 2.2 and Remark 2.3 (arXiv:1503.06183v5), with
affine supports.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

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
  {H : DirectedWallSpaces ρ ℒ} (W : DirectedWall (d := d) h H)

/-- The wall `W` cut by the closed half-space `{x | a ≤ ℓ x}`, where `ℓ` is the real extension
of the integral functional `μ` and some support point lies strictly inside the half-space. The
normal, ray and label are those of `W`. -/
def cutHalfspace (μ : Λ →+ ℤ) (a : ℝ) (hμ : ∃ x ∈ W.support, a < h.realCharacter μ x) :
    DirectedWall (d := d) h H where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := W.ray
  normal_direction := W.normal_direction
  support := W.support ∩ {x | a ≤ h.realCharacter μ x}
  support_nonempty := by
    obtain ⟨x, hx, hax⟩ := hμ
    exact ⟨x, hx, hax.le⟩
  rational_support := by
    let := h.finiteDimensional
    let ℓ := (h.realCharacter μ).toContinuousLinearMap
    have hℓ : TauCeti.Toric.IsRationalFunctional h ℓ.toLinearMap :=
      TauCeti.Toric.IsRationalFunctional.realCharacter h μ.toIntLinearMap
    have he : {x | a ≤ h.realCharacter μ x} = {x | (-ℓ) x ≤ -a} := by
      ext x
      simp [ℓ]
    rw [he]
    exact W.rational_support.inter
      (TauCeti.isRationalNormalPolyhedron_setOf_le (-ℓ) (by simpa using hℓ.neg) (-a))
  direction_support := by
    let g : V →ᵃ[ℝ] ℝ := AffineMap.const ℝ V a - (h.realCharacter μ).toAffineMap
    have hg : {x | a ≤ h.realCharacter μ x} = {x | g x ≤ 0} := by
      ext x
      simp [g]
    obtain ⟨x, hx, hax⟩ := hμ
    rw [hg, g.affineSpan_inter_le_eq W.rational_support.convex ⟨x, hx, by simpa [g] using hax⟩,
      W.direction_support]
  label := W.label
  label_mem := W.label_mem

variable (μ : Λ →+ ℤ) (a : ℝ) (hμ : ∃ x ∈ W.support, a < h.realCharacter μ x)

/-- Cutting keeps the normal. -/
@[simp]
theorem cutHalfspace_normal : (W.cutHalfspace μ a hμ).normal = W.normal := (rfl)

/-- Cutting keeps the supported ray. -/
@[simp]
theorem cutHalfspace_ray : (W.cutHalfspace μ a hμ).ray = W.ray := (rfl)

/-- The support of the cut wall is the intersection with the closed half-space. -/
@[simp]
theorem cutHalfspace_support :
    (W.cutHalfspace μ a hμ).support = W.support ∩ {x | a ≤ h.realCharacter μ x} := (rfl)

/-- Cutting keeps the label. -/
@[simp]
theorem cutHalfspace_label : (W.cutHalfspace μ a hμ).label = W.label := (rfl)

/-- If a cut wall is incoming, the cutting functional is nonnegative on the degree direction:
otherwise the geometric ray from a strictly feasible support point leaves the half-space. -/
theorem nonneg_of_incoming_cutHalfspace (hc : (W.cutHalfspace μ a hμ).Incoming) :
    0 ≤ μ (ρ W.ray.generator) := by
  obtain ⟨x, hx, hax⟩ := id hμ
  by_contra hneg
  have hc0 : (μ (ρ W.ray.generator) : ℝ) < 0 := by exact_mod_cast not_le.mp hneg
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (h.realCharacter μ x - a) / -(μ (ρ W.ray.generator) : ℝ) :=
    ⟨_, rfl⟩
  have hsc : s * -(μ (ρ W.ray.generator) : ℝ) = h.realCharacter μ x - a := by
    rw [hs]
    field_simp [hc0.ne]
  have hs0 : 0 ≤ s := hs ▸ div_nonneg (by linarith) (by linarith)
  have hxc : x ∈ (W.cutHalfspace μ a hμ).support := by
    rw [cutHalfspace_support]
    exact ⟨hx, hax.le⟩
  have hmem := (incoming_iff _).mp hc x hxc (s + 1) (by linarith)
  simp only [cutHalfspace_support, cutHalfspace_ray, Set.mem_inter_iff,
    Set.mem_ofPred_eq, map_add, map_smul, h.realCharacter_apply, smul_eq_mul] at hmem
  nlinarith [hmem.2]

/-- A cut of an incoming wall by a functional nonnegative on the degree direction is incoming. -/
theorem Incoming.cutHalfspace {W : DirectedWall (d := d) h H} (hW : W.Incoming)
    {hμ : ∃ x ∈ W.support, a < h.realCharacter μ x} (h0 : 0 ≤ μ (ρ W.ray.generator)) :
    (W.cutHalfspace μ a hμ).Incoming := by
  rw [incoming_iff]
  intro x hx t ht
  simp only [cutHalfspace_support, cutHalfspace_ray, Set.mem_inter_iff,
    Set.mem_ofPred_eq] at hx ⊢
  refine ⟨(incoming_iff W).mp hW x hx.1 t ht, ?_⟩
  have hc : (0 : ℝ) ≤ μ (ρ W.ray.generator) := by exact_mod_cast h0
  rw [map_add, map_smul, h.realCharacter_apply, smul_eq_mul]
  linarith [mul_nonneg ht hc, hx.2]

/-- A cut of an incoming wall is incoming exactly when the cutting functional is nonnegative on
the degree direction. The offset of the half-space plays no role. -/
theorem incoming_cutHalfspace_iff (hW : W.Incoming) :
    (W.cutHalfspace μ a hμ).Incoming ↔ 0 ≤ μ (ρ W.ray.generator) :=
  ⟨W.nonneg_of_incoming_cutHalfspace μ a hμ, hW.cutHalfspace μ a⟩

end Mei.DirectedWall
