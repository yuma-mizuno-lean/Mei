/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Group.Hom.Int
public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Convex.Recession
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Directed affine walls

A directed wall has a nonempty rational-normal polyhedral support, an integral
normal cutting out its affine direction, a supported primitive degree ray, and
a label in the corresponding completed wall group. The degree lattice and the
tangent lattice are independent. In particular the spatial direction may vanish,
and the primitive generator need not belong to the positive monoid.

Incomingness means that the positive geometric ray preserves the support. It is
unchanged by replacing the primitive generator with any actual
degree on its supported ray. A wall of zero geometric direction is incoming.

Wall labels commute whenever their affine supporting directions agree, even for
different primitive degrees, and their finite-order logarithms then have zero bracket.
The proof restricts the real normal kernels to the lattice and uses the
proportional-normal commutation theorem for completed wall groups.

The wall data and direction convention follow Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Definition 2.2 and Remark 2.3.
Label commutation corresponds to the observation immediately preceding equation (8).
Here we allow general rational-normal polyhedral supports with arbitrary real offsets,
and express incomingness by membership of the positive projected degree in the support's
recession cone. This affine adaptation preserves incomingness under translation and
includes zero projected degrees.

The constructions use `Mei.DirectedWallSpaces.wallGroup`,
`TauCeti.Toric.IsIntegralLattice.realCharacter` and Mathlib's
`Module.Dual.finrank_ker_add_one_of_ne_zero`.
-/

public section

noncomputable section

open Set

namespace Mei

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (H : DirectedWallSpaces ρ ℒ)

/-- A directed affine wall, with its label in the completed group of its actual
supported-ray wall spaces. Supports may be bounded or have lineality. -/
@[ext]
structure DirectedWall where
  /-- A nonzero integral conormal. -/
  normal : Λ →+ ℤ
  /-- The conormal is nonzero. -/
  normal_ne_zero : normal ≠ 0
  /-- The primitive ambient degree direction. -/
  ray : SupportedRay d
  /-- The conormal annihilates the geometric degree direction. -/
  normal_direction : normal (ρ ray.generator) = 0
  /-- The actual support, independent of an inequality presentation. -/
  support : Set V
  /-- A wall has nonempty support. -/
  support_nonempty : support.Nonempty
  /-- The support has rational normals and arbitrary real offsets. -/
  rational_support : IsRationalNormalPolyhedron h support
  /-- The affine direction is the kernel of the real extended normal. -/
  direction_support : (affineSpan ℝ support).direction = LinearMap.ker (h.realCharacter normal)
  /-- The completed wall label. -/
  label : d.completedBCHGroup ℒ
  /-- The label has logarithms in the supported-ray wall spaces at every order. -/
  label_mem : label ∈ H.wallGroup ray normal

namespace DirectedWall

variable {h H} (W : DirectedWall (d := d) h H)

/-- The support is a closed convex polyhedron on the existing polyhedral carrier. -/
theorem isConvexPolyhedron : TauCeti.IsConvexPolyhedron W.support := by
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp W.rational_support
  rw [← hP]
  exact P.isConvexPolyhedron

/-- The nonzero normal makes the support a codimension-one polyhedron. -/
theorem finrank_direction_add_one :
    Module.finrank ℝ (affineSpan ℝ W.support).direction + 1 = Module.finrank ℝ V := by
  let := h.finiteDimensional
  rw [W.direction_support]
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro he
  apply W.normal_ne_zero
  ext n
  have hn := DFunLike.congr_fun he (i n)
  simpa using hn

/-- The spatial velocity, with the sign used for directed wall propagation. -/
def direction : V := -i (ρ W.ray.generator)

/-- The spatial velocity is the negative geometric image of the primitive degree. -/
theorem direction_def : W.direction = -i (ρ W.ray.generator) := (rfl)

/-- A wall is incoming if its support is preserved by the positive geometric ray. -/
def Incoming : Prop := i (ρ W.ray.generator) ∈ recessionCone W.support

/-- A wall is outgoing if it is not incoming. -/
def Outgoing : Prop := ¬W.Incoming

/-- Incomingness is preservation of every ray based at a support point. -/
theorem incoming_iff : W.Incoming ↔
    ∀ x ∈ W.support, ∀ t : ℝ, 0 ≤ t → x + t • i (ρ W.ray.generator) ∈ W.support := by
  rw [Incoming, mem_recessionCone]

/-- Outgoingness means the positive geometric degree direction is not a recession
direction of the support, including when that geometric direction is zero. -/
theorem outgoing_iff : W.Outgoing ↔ i (ρ W.ray.generator) ∉ recessionCone W.support := Iff.rfl

/-- The geometric degree direction lies in the direction of the supporting hyperplane. -/
theorem geometricDirection_mem_direction_support :
    i (ρ W.ray.generator) ∈ (affineSpan ℝ W.support).direction := by
  rw [W.direction_support, LinearMap.mem_ker, h.realCharacter_apply, W.normal_direction]
  simp

/-- Every actual degree on the ray has the same incomingness test. -/
theorem incoming_iff_of_mem_rayDegrees {n : Γ} (hn : n ∈ W.ray.rayDegrees) :
    W.Incoming ↔ i (ρ n) ∈ recessionCone W.support := by
  rw [SupportedRay.mem_rayDegrees] at hn
  obtain ⟨a, ha, rfl⟩ := hn.2
  have he : i (ρ (a • W.ray.generator)) = (a : ℝ) • i (ρ W.ray.generator) := by
    simp only [map_zsmul, Int.cast_smul_eq_zsmul]
  rw [he, (recessionCone W.support).smul_mem_iff (by exact_mod_cast ha)]
  rfl

/-- A wall with zero spatial degree direction is always incoming. -/
theorem incoming_of_geometricDirection_eq_zero (hz : i (ρ W.ray.generator) = 0) :
    W.Incoming := by
  rw [Incoming, hz]
  exact (recessionCone W.support).zero_mem

/-- In particular, a degree killed by the projection gives an incoming wall. -/
theorem incoming_of_degreeDirection_eq_zero (hz : ρ W.ray.generator = 0) : W.Incoming :=
  W.incoming_of_geometricDirection_eq_zero (by rw [hz, map_zero])

/-- The real normal takes a constant value along the support. -/
theorem normal_apply_eq (D : DirectedWall (d := d) h H) {x y : V}
    (hx : x ∈ D.support) (hy : y ∈ D.support) :
    h.realCharacter D.normal x = h.realCharacter D.normal y := by
  have hm : x - y ∈ LinearMap.ker (h.realCharacter D.normal) := by
    rw [← D.direction_support]
    exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hx) (subset_affineSpan ℝ _ hy)
  simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero] using hm

/-- The spatial velocity is tangent to the supporting hyperplane, also when it is zero. -/
theorem direction_mem : W.direction ∈ (affineSpan ℝ W.support).direction := by
  rw [W.direction_def]
  exact (affineSpan ℝ W.support).direction.neg_mem W.geometricDirection_mem_direction_support

/-- An outgoing wall has a point which leaves its support under a positive-degree translation. -/
theorem outgoing_exists_iff (D : DirectedWall (d := d) h H) : D.Outgoing ↔
    ∃ x ∈ D.support, ∃ t : ℝ, 0 ≤ t ∧ x + t • i (ρ D.ray.generator) ∉ D.support := by
  simp only [Outgoing, incoming_iff, not_forall, exists_prop]

/-- Walls with the same affine tangent direction have proportional integral normals. -/
private theorem exists_ne_zero_zsmul_eq_normal_of_direction_eq (D E : DirectedWall (d := d) h H)
    (he : (affineSpan ℝ D.support).direction = (affineSpan ℝ E.support).direction) :
    ∃ c e : ℤ, c ≠ 0 ∧ e ≠ 0 ∧ c • D.normal = e • E.normal := by
  have hk : D.normal.ker = E.normal.ker := by
    ext n
    have hn := SetLike.ext_iff.mp
      (D.direction_support.symm.trans (he.trans E.direction_support)) (i n)
    simpa only [LinearMap.mem_ker, h.realCharacter_apply, Int.cast_eq_zero,
      AddMonoidHom.mem_ker] using hn
  exact D.normal.exists_ne_zero_zsmul_eq_of_ker_eq E.normal D.normal_ne_zero hk

/-- Labels commute whenever the affine tangent hyperplanes have the same direction.
The wall supports need not meet and the supported primitive degrees may differ. -/
theorem commute_label_of_direction_eq (D E : DirectedWall (d := d) h H)
    (he : (affineSpan ℝ D.support).direction = (affineSpan ℝ E.support).direction) :
    Commute D.label E.label := by
  obtain ⟨c, e, hc, he, hn⟩ := exists_ne_zero_zsmul_eq_normal_of_direction_eq D E he
  exact H.commute_of_mem_wallGroup D.label_mem E.label_mem hc he hn

/-- Labels of walls whose affine tangent hyperplanes have the same direction have
commuting logarithms at every finite order. -/
theorem lie_log_projection_eq_zero_of_direction_eq (D E : DirectedWall (d := d) h H)
    (he : (affineSpan ℝ D.support).direction = (affineSpan ℝ E.support).direction) (k : ℕ) :
    ⁅BCHGroup.log (CompletedGroup.projection k D.label),
      BCHGroup.log (CompletedGroup.projection k E.label)⁆ = 0 := by
  obtain ⟨c, e, hc, he, hn⟩ := exists_ne_zero_zsmul_eq_normal_of_direction_eq D E he
  exact H.lie_eq_zero_of_mem_truncatedRayLieSubalgebra
    ((H.mem_wallGroup _ _ _).mp D.label_mem k) ((H.mem_wallGroup _ _ _).mp E.label_mem k) hc he hn

end DirectedWall
end Mei
