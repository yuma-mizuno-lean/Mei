/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Group.Hom.Int
public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Geometry.Convex.Polyhedron.Rational.Map
public import Mei.Geometry.Convex.Recession
public import Mei.Geometry.Affine.Span

/-!
# Directed affine walls

A directed wall has an actual nonempty rational-normal polyhedral support, a nonzero
integral normal, a supported primitive degree, and a completed label in the associated
wall group. Its support has direction exactly the real kernel of its normal.
The incoming condition uses the recession cone, so it is invariant under arbitrary
translations and includes every wall whose geometric direction is zero.

Wall labels commute whenever their affine supporting directions agree, even for
different primitive degrees. The proof restricts the real normal kernels to the lattice
and uses the proportional-normal commutation theorem for completed wall groups.

The wall data and direction convention follow Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Definition 2.2 and Remark 2.3.
Label commutation corresponds to the observation immediately preceding equation (8).
Here we allow general rational-normal polyhedral supports with arbitrary real offsets,
and express incomingness by membership of the positive projected degree in the support's
recession cone. This affine adaptation preserves incomingness under translation and
includes zero projected degrees.

The constructions use `Mei.DirectedWallSpaces.wallGroup`,
`TauCeti.Toric.IsIntegralLattice.realCharacter`, Mathlib's `AffineEquiv.constVAdd`
and `Module.Dual.finrank_ker_add_one_of_ne_zero`.
-/

public section

namespace Mei

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (d : PositiveDegrees Γ)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] {i : Λ →+ V}

/-- An affine wall labelled in the completed group of its supported primitive ray.
The support may be translated, unbounded or have lineality; the projected degree may vanish. -/
structure DirectedWall (h : TauCeti.Toric.IsIntegralLattice i)
    (H : DirectedWallSpaces ρ ℒ) where
  /-- The coorienting integral normal. -/
  normal : Λ →+ ℤ
  /-- A wall has a nonzero normal, including when its geometric direction is zero. -/
  normal_ne_zero : normal ≠ 0
  /-- The supported primitive ambient degree, which need not belong to the positive monoid. -/
  ray : SupportedRay d
  /-- The degree is tangent to the normal after geometric projection. -/
  tangent : normal (ρ ray.generator) = 0
  /-- The actual closed wall carrier. -/
  support : Set V
  /-- Empty walls are excluded. -/
  nonempty : support.Nonempty
  /-- The support admits rational normals and arbitrary real offsets. -/
  rational : IsRationalNormalPolyhedron h support
  /-- The affine tangent hyperplane is exactly the kernel of the extended normal. -/
  direction_eq : (affineSpan ℝ support).direction = LinearMap.ker (h.realCharacter normal)
  /-- The completed wall label. -/
  label : d.completedBCHGroup ℒ
  /-- Its finite logarithms belong to the actual allowed degrees on the supported ray. -/
  label_mem : label ∈ H.wallGroup ray normal

namespace DirectedWall

variable {d} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}

/-- The normal, primitive ray, actual support and label determine a directed wall. -/
@[ext (iff := false)]
theorem ext {D E : DirectedWall d h H} (hn : D.normal = E.normal) (hr : D.ray = E.ray)
    (hs : D.support = E.support) (hl : D.label = E.label) : D = E := by
  cases D
  cases E
  cases hn
  cases hr
  cases hs
  cases hl
  rfl

/-- The wall support is a convex polyhedron on the existing polyhedral carrier. -/
theorem isConvexPolyhedron (D : DirectedWall d h H) : TauCeti.IsConvexPolyhedron D.support := by
  obtain ⟨Q, hQ⟩ := isRationalNormalPolyhedron_iff.mp D.rational
  rw [← hQ]
  exact Q.isConvexPolyhedron

/-- The real normal takes a constant value along the support. -/
theorem normal_apply_eq (D : DirectedWall d h H) {x y : V}
    (hx : x ∈ D.support) (hy : y ∈ D.support) :
    h.realCharacter D.normal x = h.realCharacter D.normal y := by
  have hm : x - y ∈ LinearMap.ker (h.realCharacter D.normal) := by
    rw [← D.direction_eq]
    exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hx) (subset_affineSpan ℝ _ hy)
  simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero] using hm

/-- The geometric wall direction is the negative image of its primitive degree. -/
def direction (D : DirectedWall d h H) : V := -i (ρ D.ray.generator)

theorem direction_def (D : DirectedWall d h H) : D.direction = -i (ρ D.ray.generator) := (rfl)

/-- The direction is tangent to the wall, also when it is zero. -/
theorem direction_mem (D : DirectedWall d h H) :
    D.direction ∈ (affineSpan ℝ D.support).direction := by
  rw [D.direction_eq, LinearMap.mem_ker, direction]
  simp [D.tangent]

/-- The support of a directed wall has codimension one. -/
theorem finrank_direction_add_one (D : DirectedWall d h H) :
    Module.finrank ℝ (affineSpan ℝ D.support).direction + 1 = Module.finrank ℝ V := by
  let := h.finiteDimensional
  rw [D.direction_eq]
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro hz
  exact D.normal_ne_zero (h.realCharacter_injective (by simpa using hz))

/-- A wall is incoming when its positive projected primitive degree is a recession direction. -/
def Incoming (D : DirectedWall d h H) : Prop := i (ρ D.ray.generator) ∈ Set.recessionCone D.support

/-- A wall is outgoing when its positive projected degree is not a recession direction. -/
def Outgoing (D : DirectedWall d h H) : Prop := ¬D.Incoming

theorem incoming_iff (D : DirectedWall d h H) :
    D.Incoming ↔ ∀ x ∈ D.support, ∀ t : ℝ, 0 ≤ t →
      x + t • i (ρ D.ray.generator) ∈ D.support := by
  rw [Incoming, Set.mem_recessionCone]

/-- An outgoing wall has a point which leaves its support under a positive-degree translation. -/
theorem outgoing_iff (D : DirectedWall d h H) : D.Outgoing ↔
    ∃ x ∈ D.support, ∃ t : ℝ, 0 ≤ t ∧ x + t • i (ρ D.ray.generator) ∉ D.support := by
  simp only [Outgoing, incoming_iff, not_forall, exists_prop]

/-- Walls with zero projected degree are always incoming. -/
theorem incoming_of_map_ray_eq_zero (D : DirectedWall d h H) (hz : ρ D.ray.generator = 0) :
    D.Incoming := by
  simp [Incoming, hz]

/-- Translate a wall's support, keeping its normal, primitive degree and completed label. -/
noncomputable def translate (D : DirectedWall d h H) (v : V) : DirectedWall d h H where
  normal := D.normal
  normal_ne_zero := D.normal_ne_zero
  ray := D.ray
  tangent := D.tangent
  support := (fun x => v + x) '' D.support
  nonempty := D.nonempty.image _
  rational := by
    let e : Toric.IntegralAffineEquiv h h :=
      ⟨AffineEquiv.constVAdd ℝ V v, AddEquiv.refl Λ, fun _ => rfl⟩
    exact D.rational.image e
  direction_eq := by
    have hl : (AffineEquiv.constVAdd ℝ V v).toAffineMap.linear = LinearMap.id := rfl
    have he := (AffineEquiv.constVAdd ℝ V v).toAffineMap.direction_affineSpan_image D.support
    simpa only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add,
      hl, Submodule.map_id, D.direction_eq] using he
  label := D.label
  label_mem := D.label_mem

@[simp]
theorem translate_normal (D : DirectedWall d h H) (v : V) : (D.translate v).normal = D.normal :=
  (rfl)

@[simp]
theorem translate_ray (D : DirectedWall d h H) (v : V) : (D.translate v).ray = D.ray := (rfl)

@[simp]
theorem translate_support (D : DirectedWall d h H) (v : V) :
    (D.translate v).support = (fun x => v + x) '' D.support := (rfl)

@[simp]
theorem translate_label (D : DirectedWall d h H) (v : V) : (D.translate v).label = D.label :=
  (rfl)

@[simp]
theorem translate_zero (D : DirectedWall d h H) : D.translate 0 = D := by
  ext <;> simp

/-- Successive translations add their displacement vectors. -/
@[simp]
theorem translate_translate (D : DirectedWall d h H) (v w : V) :
    (D.translate v).translate w = D.translate (w + v) := by
  apply ext
  · simp
  · simp
  · simp only [translate_support, Set.image_image, add_assoc]
  · simp

/-- Incomingness depends on the recession directions, not the location of the support. -/
@[simp]
theorem incoming_translate (D : DirectedWall d h H) (v : V) :
    (D.translate v).Incoming ↔ D.Incoming := by
  simp only [Incoming, translate_ray, translate_support, Set.image_add_left,
    Set.recessionCone_preimage_add_left]

/-- Outgoingness is likewise invariant under arbitrary translations. -/
@[simp]
theorem outgoing_translate (D : DirectedWall d h H) (v : V) :
    (D.translate v).Outgoing ↔ D.Outgoing := by
  simp [Outgoing]

/-- Labels commute whenever the affine tangent hyperplanes have the same direction.
The wall supports need not meet and the supported primitive degrees may differ. -/
theorem commute_label_of_direction_eq (D E : DirectedWall d h H)
    (he : (affineSpan ℝ D.support).direction = (affineSpan ℝ E.support).direction) :
    Commute D.label E.label := by
  have hk : D.normal.ker = E.normal.ker := by
    ext n
    have hn := SetLike.ext_iff.mp (D.direction_eq.symm.trans (he.trans E.direction_eq)) (i n)
    simpa only [LinearMap.mem_ker, h.realCharacter_apply, Int.cast_eq_zero,
      AddMonoidHom.mem_ker] using hn
  obtain ⟨c, e, hc, he, hn⟩ :=
    D.normal.exists_ne_zero_zsmul_eq_of_ker_eq E.normal D.normal_ne_zero hk
  exact H.commute_of_mem_wallGroup D.label_mem E.label_mem hc he hn

end DirectedWall
end Mei
