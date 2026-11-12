/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Halfspace
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.Toric.Algebraic.Lattice

/-!
# Incoming walls with affine supports

A directed wall with supported ray `w` is incoming when the geometric degree direction
`i(ρ w)` is a recession direction of its support. Two examples show what this definition does
and does not require. Both use the positive quadrant `P = ℕ²` of `ℤ²`
(`Module.Basis.positiveDegrees` of the standard basis), arbitrary wall spaces, and labels
anywhere in the relevant wall group.

* Take `ρ = id`, the plane `ℝ²` with lattice `ℤ²`, the ray `w = e₁` and the normal `m = e₂*`.
  The half-line `𝔡 = ℝ_{≥0} e₁` and its translate `𝔡 + 2e₁` are supports of incoming walls
  (`DirectedWall.Examples.horizontalHalfLine_incoming`), since translation does not change the
  recession cone. Yet `e₁ ∈ 𝔡` and `e₁ ∉ 𝔡 + 2e₁`
  (`DirectedWall.Examples.geometricDirection_mem_horizontalHalfLine_zero`,
  `DirectedWall.Examples.geometricDirection_notMem_horizontalHalfLine_two`). Incomingness is a
  condition on the recession cone of the support, not on whether the support contains the
  direction.
* Take `ρ(a, b) = a` to `ℤ`, with `ℝ` as the spatial space. The degree `(0, 1)` has zero
  geometric direction, so every wall on its ray is incoming
  (`DirectedWall.Examples.incoming_of_ray_eq_verticalRay`). This includes the walls whose support
  is the single point `{c}`, the hyperplanes of the normal `id : ℤ → ℤ`
  (`DirectedWall.Examples.pointWall_support`).

The walls are `DirectedWall.ofAffineHyperplane` and its half-space cuts
`DirectedWall.cutHalfspace`. The directed walls and their incomingness follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, Definition 2.2 and
Remark 2.3 (arXiv:1503.06183v5), with affine supports.
-/

public section

open TauCeti (IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei.DirectedWall.Examples

open TauCeti.Toric

open scoped Pointwise

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The supported ray through `e₁ = (1, 0)` in the positive quadrant. -/
local notation "horizontalRay" => Module.Basis.positiveDegreesRay (Module.Basis.finTwoProd ℤ) 0

/-- The supported ray through `e₂ = (0, 1)` in the positive quadrant. -/
local notation "verticalRay" => Module.Basis.positiveDegreesRay (Module.Basis.finTwoProd ℤ) 1

variable {R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  {ℒ : ℤ × ℤ → Submodule R L} [GradedLieAlgebra ℒ] [IsPositiveGrading ℕ² ℒ]

section HalfLine

variable {H : DirectedWallSpaces (AddMonoidHom.id (ℤ × ℤ)) ℒ}
  (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  (g : H.wallGroup horizontalRay (AddMonoidHom.snd ℤ ℤ))

/-- The horizontal axis `{y = 0}` of `ℝ²` as a wall on the ray `e₁`, with normal `e₂*`. -/
def horizontalAxis : DirectedWall (d := ℕ²) h H :=
  ofAffineHyperplane h H (AddMonoidHom.snd ℤ ℤ)
    (fun he => by simpa using DFunLike.congr_fun he (0, 1)) 0 horizontalRay (by simp) g

/-- The horizontal axis is the set of points with vanishing second coordinate. -/
theorem horizontalAxis_support : (horizontalAxis h g).support = {x | x.2 = 0} := by
  simp [horizontalAxis]

/-- The half-line `{(t, 0) | a ≤ t}` of the horizontal axis, as a wall on the ray `e₁` with
normal `e₂*`: the horizontal axis cut by the half-plane `{a ≤ x}`. -/
def horizontalHalfLine (a : ℝ) : DirectedWall (d := ℕ²) h H :=
  (horizontalAxis h g).cutHalfspace (AddMonoidHom.fst ℤ ℤ) a
    ⟨(a + 1, 0), by simp [horizontalAxis_support], by simp⟩

/-- The half-line wall is supported on `{(t, 0) | a ≤ t}`. -/
theorem horizontalHalfLine_support (a : ℝ) :
    (horizontalHalfLine h g a).support = (fun t : ℝ => (t, (0 : ℝ))) '' Set.Ici a := by
  ext ⟨x, y⟩
  simp only [horizontalHalfLine, cutHalfspace_support, horizontalAxis_support,
    IsIntegralLattice.realCharacter_fst, Set.mem_inter_iff, Set.mem_ofPred_eq,
    LinearMap.fst_apply, Set.mem_image, Set.mem_Ici, Prod.mk.injEq]
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨x, hx, rfl, hy.symm⟩
  · rintro ⟨t, ht, rfl, rfl⟩
    exact ⟨rfl, ht⟩

/-- The half-line starting at `2e₁` is the translate `𝔡 + 2e₁` of `𝔡 = ℝ_{≥0} e₁`. -/
theorem horizontalHalfLine_two_support :
    (horizontalHalfLine h g 2).support =
      ((2 : ℝ), (0 : ℝ)) +ᵥ (horizontalHalfLine h g 0).support := by
  rw [horizontalHalfLine_support, horizontalHalfLine_support, ← Set.image_vadd, Set.image_image]
  ext ⟨x, y⟩
  simp only [Set.mem_image, Set.mem_Ici, Prod.mk.injEq, vadd_eq_add, Prod.mk_add_mk, add_zero]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    exact ⟨t - 2, by linarith, by ring, rfl⟩
  · rintro ⟨t, ht, rfl, rfl⟩
    exact ⟨2 + t, by linarith, rfl, rfl⟩

/-- Every half-line wall `{(t, 0) | a ≤ t}` on the ray `e₁` is incoming: the cut of the
incoming horizontal axis by `{a ≤ x}` is incoming since `e₁*(e₁) = 1 ≥ 0`. In particular both
`𝔡 = ℝ_{≥0} e₁` and its translate `𝔡 + 2e₁` are incoming. -/
theorem horizontalHalfLine_incoming (a : ℝ) : (horizontalHalfLine h g a).Incoming :=
  ((horizontalAxis h g).incoming_cutHalfspace_iff _ a _ (ofAffineHyperplane_incoming ..)).mpr
    (by simp [horizontalAxis])

/-- The geometric degree direction `e₁` of the ray lies in the support `𝔡 = ℝ_{≥0} e₁`. -/
theorem geometricDirection_mem_horizontalHalfLine_zero :
    (Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)
        ((horizontalHalfLine h g 0).ray.generator) ∈ (horizontalHalfLine h g 0).support := by
  rw [horizontalHalfLine_support]
  exact ⟨1, zero_le_one, by simp [horizontalHalfLine, horizontalAxis]⟩

/-- The geometric degree direction `e₁` of the ray does not lie in the translated support
`𝔡 + 2e₁`, although that wall is incoming. -/
theorem geometricDirection_notMem_horizontalHalfLine_two :
    (Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)
        ((horizontalHalfLine h g 2).ray.generator) ∉ (horizontalHalfLine h g 2).support := by
  rw [horizontalHalfLine_support]
  rintro ⟨t, ht, he⟩
  simp only [horizontalHalfLine, horizontalAxis, cutHalfspace_ray, ofAffineHyperplane_ray,
    Module.Basis.positiveDegreesRay_generator, Module.Basis.finTwoProd_zero] at he
  have he₁ : t = 1 := by simpa using congrArg Prod.fst he
  linarith [Set.mem_Ici.mp ht]

end HalfLine

section ZeroDirection

variable {H : DirectedWallSpaces (AddMonoidHom.fst ℤ ℤ) ℒ}
  (h : IsIntegralLattice (Int.castAddHom ℝ))

/-- For `ρ(a, b) = a`, every wall on the ray of `(0, 1)` is incoming, whatever its support:
the degree `(0, 1)` has zero geometric direction. -/
theorem incoming_of_ray_eq_verticalRay (W : DirectedWall (d := ℕ²) h H)
    (hW : W.ray = verticalRay) : W.Incoming :=
  W.incoming_of_degreeDirection_eq_zero (by simp [hW])

variable (g : H.wallGroup verticalRay (AddMonoidHom.id ℤ)) (c : ℝ)

/-- The wall on the ray of `(0, 1)` supported on the hyperplane `{c}` of `ℝ` cut out by the
normal `id : ℤ → ℤ`. -/
def pointWall : DirectedWall (d := ℕ²) h H :=
  ofAffineHyperplane h H (AddMonoidHom.id ℤ)
    (fun he => by simpa using DFunLike.congr_fun he 1) c verticalRay (by simp) g

/-- The wall `pointWall` is supported on the single point `c`. -/
theorem pointWall_support : (pointWall h g c).support = {c} := by
  have hid : h.realCharacter (AddMonoidHom.id ℤ) = LinearMap.id :=
    (h.eq_realCharacter fun n => by simp).symm
  ext x
  simp [pointWall, hid]

/-- The point wall is incoming, because its degree `(0, 1)` has zero geometric direction. -/
theorem pointWall_incoming : (pointWall h g c).Incoming :=
  incoming_of_ray_eq_verticalRay h _ (ofAffineHyperplane_ray ..)

end ZeroDirection

end Mei.DirectedWall.Examples
