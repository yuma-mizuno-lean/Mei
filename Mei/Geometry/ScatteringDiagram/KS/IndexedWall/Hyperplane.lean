/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall

/-!
# Full hyperplane indexed walls

In a KS space, the kernel `n⊥` of the normal of a degree `n` is a linear hyperplane with a
rational normal (`KSSpace.isRationalNormalPolyhedron_ker_normal`). For a supported ray `w` and a
label in the completed group of `w`, the whole hyperplane `w⊥` is therefore an indexed wall
(`IndexedWall.hyperplane`). Its support contains every point of `w⊥`, in particular the origin;
no cone structure beyond the hyperplane itself is chosen.

Indexed walls follow the abelian-ray description of scattering diagrams in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public section

open TauCeti (IsRationalNormalPolyhedron)

open TauCeti (PositiveDegrees IsPositiveGrading SupportedRay)

noncomputable section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i} (s : KSSpace h)

namespace KSSpace

/-- The hyperplane cut out by the normal of a degree has rational normals. -/
theorem isRationalNormalPolyhedron_ker_normal (n : N) :
    IsRationalNormalPolyhedron h (LinearMap.ker (s.normal n) : Set V) := by
  let := h.finiteDimensional
  let ℓ := (s.normal n).toContinuousLinearMap
  have hℓ : TauCeti.Toric.IsRationalFunctional h ℓ.toLinearMap := by
    convert TauCeti.Toric.IsRationalFunctional.realCharacter h (AddMonoidHom.eval n).toIntLinearMap
      using 1
    exact s.normal_eq_realCharacter n
  have he : (LinearMap.ker (s.normal n) : Set V) = {x | ℓ x ≤ 0} ∩ {x | (-ℓ) x ≤ -0} := by
    ext x
    simp [ℓ, le_antisymm_iff]
  rw [he]
  exact (TauCeti.isRationalNormalPolyhedron_setOf_le ℓ hℓ 0).inter
    (TauCeti.isRationalNormalPolyhedron_setOf_le (-ℓ) (by simpa using hℓ.neg) (-0))

end KSSpace

namespace IndexedWall

variable {R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The full hyperplane `w⊥` of a supported ray `w`, labelled by an element of the completed
group of `w`. -/
def hyperplane (w : SupportedRay d) (g : d.completedBCHGroup ℒ)
    (hg : g ∈ d.completedRaySubgroup ℒ w) : IndexedWall s d ℒ where
  ray := w
  support := LinearMap.ker (s.normal w.generator)
  isCone := ⟨PointedCone.ofSubmodule (LinearMap.ker (s.normal w.generator)),
    PointedCone.coe_ofSubmodule _⟩
  rational_support := s.isRationalNormalPolyhedron_ker_normal w.generator
  direction_support := by
    rw [← Submodule.coe_toAffineSubspace, AffineSubspace.affineSpan_coe,
      Submodule.toAffineSubspace_direction]
  label := g
  label_mem := hg

variable (w : SupportedRay d) (g : d.completedBCHGroup ℒ) (hg : g ∈ d.completedRaySubgroup ℒ w)

/-- The full hyperplane wall lies on the given supported ray. -/
@[simp]
theorem hyperplane_ray : (hyperplane s w g hg).ray = w := (rfl)

/-- The support of the full hyperplane wall is the hyperplane `w⊥`. -/
@[simp]
theorem hyperplane_support :
    (hyperplane s w g hg).support = LinearMap.ker (s.normal w.generator) := (rfl)

/-- The full hyperplane wall carries the given label. -/
@[simp]
theorem hyperplane_label : (hyperplane s w g hg).label = g := (rfl)

/-- A point lies on the full hyperplane wall exactly when it annihilates the ray generator. -/
theorem mem_hyperplane_support {θ : V} :
    θ ∈ (hyperplane s w g hg).support ↔ s.evaluation θ w.generator = 0 := by
  simp

end IndexedWall

end Mei
