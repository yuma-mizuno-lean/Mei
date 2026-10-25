/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Geometry.Convex.Polyhedron.Rational.Map
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
unchanged by translation or by replacing the primitive generator with any actual
degree on its supported ray. A wall of zero geometric direction is incoming.

Translation uses Mathlib's `AffineEquiv.constVAdd` and `AffineSubspace.map_span`,
and the existing integral-affine transport of rational-normal polyhedra.
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

/-- Outgoingness is the failure of incomingness, including when the spatial
direction is zero. -/
theorem outgoing_iff : W.Outgoing ↔ ¬W.Incoming := Iff.rfl

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

/-- Move only the support by an arbitrary real translation. The integral normal,
primitive degree and completed label are retained. -/
def translate (v : V) : DirectedWall (d := d) h H where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := W.ray
  normal_direction := W.normal_direction
  support := (fun x => v + x) '' W.support
  support_nonempty := W.support_nonempty.image _
  rational_support := by
    let e : Toric.IntegralAffineEquiv h h :=
      ⟨AffineEquiv.constVAdd ℝ V v, AddEquiv.refl Λ, fun _ => rfl⟩
    exact W.rational_support.image e
  direction_support := by
    have he := congrArg AffineSubspace.direction
      (AffineSubspace.map_span (AffineEquiv.constVAdd ℝ V v).toAffineMap W.support)
    simpa [W.direction_support] using he.symm
  label := W.label
  label_mem := W.label_mem

@[simp]
theorem translate_normal (v : V) : (W.translate v).normal = W.normal := (rfl)

@[simp]
theorem translate_ray (v : V) : (W.translate v).ray = W.ray := (rfl)

@[simp]
theorem translate_support (v : V) :
    (W.translate v).support = (fun x => v + x) '' W.support := (rfl)

@[simp]
theorem translate_label (v : V) : (W.translate v).label = W.label := (rfl)

/-- Translation leaves the wall's spatial velocity unchanged. -/
@[simp]
theorem direction_translate (v : V) : (W.translate v).direction = W.direction := by
  rw [direction_def, translate_ray, direction_def]

/-- Incomingness depends on the recession cone, so translation preserves it. -/
@[simp]
theorem incoming_translate_iff (v : V) : (W.translate v).Incoming ↔ W.Incoming := by
  simp only [Incoming, translate_ray, translate_support, Set.image_add_left,
    recessionCone_preimage_add]

/-- Outgoingness is translation invariant, including for unbounded supports. -/
@[simp]
theorem outgoing_translate_iff (v : V) : (W.translate v).Outgoing ↔ W.Outgoing := by
  rw [outgoing_iff, incoming_translate_iff, outgoing_iff]

/-- Translation by zero fixes all wall data. -/
@[simp]
theorem translate_zero : W.translate 0 = W := by
  ext <;> simp

/-- Successive translations add their translation vectors. -/
@[simp]
theorem translate_translate (v w : V) : (W.translate v).translate w = W.translate (w + v) := by
  apply DirectedWall.ext <;>
    simp only [translate_normal, translate_ray, translate_support, translate_label]
  rw [Set.image_image]
  congr 1
  funext x
  exact (add_assoc w v x).symm

end DirectedWall
end Mei
