/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Trivialization
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.CellCrossing
public import Mei.Geometry.Convex.PolyhedralComplex.Incidence
public import Mei.Geometry.Convex.PolyhedralCochain.Coorientation
public import Mei.Algebra.Lie.BCH.CentralExtension

/-!
# Central crossing-defect cochains

Choose an orientation on each wall of an adapted complex. Each oriented wall
admits an integral coorientation and two incident full cells, with its crossing
label realized by an actual admissible segment between their interiors.
Lower-order chamber lifts then give the kernel-valued coefficient
`log (t₊⁻¹ * X * t₋)`. Summing these coefficients on the oriented cells constructs
the finite central defect cochain. Simultaneously reversing a cell and its
crossing leaves its contribution unchanged.

The geometric choices are constructed using
`FinitePolyhedralComplex.exists_transverse_wall_chambers`,
`OrientedCell.exists_integral_coorientation` and
`DirectedDiagram.eventually_exists_levelPathProduct_eq_wallCrossingLabel`.
Kernel membership uses the finite chamber-lift projection formula; its logarithm
is `LieHom.logDefect`. The obstruction construction follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6, and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix C.3.

This construction retains the choices of incident cells and lifts. Identifying
its coboundary with positively oriented meridian holonomy requires the geometric
incidence and boundary identities in addition to this finite sum.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Geometric crossing choices for an oriented adapted wall. The realization
condition uses an actual admissible segment, without assuming a transport or
kernel equation. Only the normal and the two incident cells are stored as data. -/
@[ext]
structure AdaptedWallCrossing {l : ℕ} (σ : OrientedCell h 1)
    (hσ : σ.carrier ∈ (D.adaptedComplex l).walls) where
  /-- An integral representative of the prescribed positive side. -/
  normal : Λ →+ ℤ
  /-- The normal cuts out the wall direction. -/
  ker_normal : (h.realCharacter normal).ker = (affineSpan ℝ σ.carrier).direction
  /-- The integral normal represents the chosen conormal orientation. -/
  sign_normal : ∀ v : V, SignType.sign (h.realCharacter normal v) =
    σ.orientation.evalSign (fun _ : Fin 1 => v)
  /-- The full cell on the source side of the crossing. -/
  minus : (D.adaptedComplex l).cellsOfCodimension 0
  /-- The full cell on the target side of the crossing. -/
  plus : (D.adaptedComplex l).cellsOfCodimension 0
  /-- The two full cells meet exactly in the wall. -/
  inter_eq : (minus : Set V) ∩ (plus : Set V) = σ.carrier
  /-- A segment from these cell interiors realizes the positive crossing label. -/
  realized : ∃ (q v : V) (a : ℝ), q ∈ intrinsicInterior ℝ σ.carrier ∧
    0 < h.realCharacter normal v ∧ 0 < a ∧
    ∃ (x y : WallComplement (fun j : D.active l => (D.wall j).support))
    (e : x ⟶ y), x.val = q - a • v ∧ y.val = q + a • v ∧
      x.val ∈ interior (minus : Set V) ∧
      y.val ∈ interior (plus : Set V) ∧
      D.levelPathProduct l e.toPath =
        D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter normal) ker_normal

namespace AdaptedWallCrossing

variable {D} {l : ℕ} {σ : OrientedCell h 1}
  {hσ : σ.carrier ∈ (D.adaptedComplex l).walls}

/-- Every prescribed orientation admits geometric crossing choices. No
consistency, chamber lifts or crossing-defect equations are required. -/
instance : Nonempty (D.AdaptedWallCrossing σ hσ) := by
  have := h.finiteDimensional
  obtain ⟨m, -, hmker, hmsign⟩ := σ.exists_integral_coorientation
  have hmreal : h.realCharacter m ≠ 0 := by
    intro he
    have hd := σ.finrank_direction_add
    rw [← hmker, he, LinearMap.ker_zero, finrank_top] at hd
    omega
  obtain ⟨v, hv⟩ := LinearMap.surjective hmreal 1
  have hvpos : 0 < h.realCharacter m v := by rw [hv]; exact zero_lt_one
  obtain ⟨q, hq⟩ := σ.nonempty.intrinsicInterior
    ((D.adaptedComplex l).isConvexPolyhedron
      ((D.adaptedComplex l).mem_cells_of_mem_walls hσ)).convex
  have hvdir : v ∉ (affineSpan ℝ σ.carrier).direction := by
    rw [← hmker, LinearMap.mem_ker]
    exact hvpos.ne'
  obtain ⟨P, hP, Q, hQ, _, hPQ, ε, hε, hshort⟩ :=
    (D.adaptedComplex l).exists_transverse_wall_chambers hσ hq
      (by simp) hvdir
  have hcross := D.eventually_exists_levelPathProduct_eq_wallCrossingLabel
    ⟨σ.carrier, hσ⟩ (h.realCharacter m) hmker hq hvpos
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a ∈ Ioo 0 ε := Ioo_mem_nhdsGT hε
  obtain ⟨a, ha, x, y, e, hx, hy, he⟩ := (hsmall.and hcross).exists
  have hPi := Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
    ((D.adaptedComplex l).affineSpan_eq_top_of_mem_cellsOfCodimension_zero hP)
  have hQi := Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
    ((D.adaptedComplex l).affineSpan_eq_top_of_mem_cellsOfCodimension_zero hQ)
  refine ⟨⟨m, hmker, hmsign, ⟨P, hP⟩, ⟨Q, hQ⟩, hPQ,
    q, v, a, hq, hvpos, ha.1, x, y, e, hx, hy, ?_, ?_, he⟩⟩
  · rw [hx, ← hPi]
    exact (hshort a ha).1
  · rw [hy, ← hQi]
    exact (hshort a ha).2

/-- Reversing the orientation exchanges the two chambers and reverses the
actual segment realizing the crossing. -/
def reverse (c : D.AdaptedWallCrossing σ hσ) :
    D.AdaptedWallCrossing (l := l) σ.reverse (by simpa using hσ) where
  normal := -c.normal
  ker_normal := by simpa using c.ker_normal
  sign_normal v := by
    simp only [map_neg, LinearMap.neg_apply, Left.sign_neg, c.sign_normal,
      OrientedCell.reverse_orientation, Module.Ray.evalSign_neg]
  minus := c.plus
  plus := c.minus
  inter_eq := by simpa only [inter_comm, OrientedCell.reverse_carrier] using c.inter_eq
  realized := by
    obtain ⟨q, v, a, hq, hv, ha, x, y, e, hx, hy, hxi, hyi, he⟩ := c.realized
    refine ⟨q, -v, a, by simpa using hq, by simpa using hv, ha, y, x, Quiver.reverse e,
      by simpa using hy, by simpa [sub_eq_add_neg] using hx, hyi, hxi, ?_⟩
    rw [← Quiver.Path.reverse_toPath, D.levelPathProduct_reverse, he]
    simpa using (D.wallCrossingLabel_neg ⟨σ.carrier, hσ⟩
      (h.realCharacter c.normal) c.ker_normal).symm

@[simp]
theorem reverse_normal (c : D.AdaptedWallCrossing σ hσ) :
    c.reverse.normal = -c.normal := (rfl)

@[simp]
theorem reverse_minus (c : D.AdaptedWallCrossing σ hσ) : c.reverse.minus = c.plus := (rfl)

@[simp]
theorem reverse_plus (c : D.AdaptedWallCrossing σ hσ) : c.reverse.plus = c.minus := (rfl)

variable {k : ℕ} {σ : OrientedCell h 1}
  {hσ : σ.carrier ∈ (D.adaptedComplex (k + 1)).walls}
  (c : D.AdaptedWallCrossing σ hσ)
  (hk : D.LevelConsistent k)
  (b : WallComplement (fun j : D.active k => (D.wall j).support))
  (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
  (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)),
    x.val ∈ interior (P : Set V) →
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)

include hk b ht in
/-- The lower-order crossing equation follows from a geometric realization
and the chamber-lift projection formula. -/
theorem truncation_label_mul :
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
        (D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal) *
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t c.minus) =
        (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t c.plus) := by
  obtain ⟨q, v, a, _, _, _, x, y, e, _, _, hx, hy, he⟩ := c.realized
  have hker := D.adapted_chamber_lift_path_mem_ker (Nat.le_succ k) hk b t ht
    e.toPath c.minus c.plus hx hy
  rw [he, MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_assoc] at hker
  exact (inv_mul_eq_one.mp hker).symm

/-- The central crossing defect, with values in the successive Lie kernel. -/
def defect : (d.truncationMap ℒ (Nat.le_succ k)).ker :=
  (d.truncationMap ℒ (Nat.le_succ k)).logDefect (t c.minus) (t c.plus)
    (D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal)
    (c.truncation_label_mul hk b t ht)

/-- The coefficient is the logarithm of the crossing label gauged by the two
incident chamber lifts. -/
@[simp]
theorem coe_defect :
    (c.defect hk b t ht : d.truncatedLie ℒ (k + 1)) =
      BCHGroup.log ((t c.plus)⁻¹ *
        D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal *
        t c.minus) := LieHom.coe_logDefect _ _ _ _ _

/-- A crossing coefficient vanishes exactly when its label carries the source
lift to the target lift. -/
@[simp]
theorem defect_eq_zero_iff : c.defect hk b t ht = 0 ↔
    D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal =
      t c.plus * (t c.minus)⁻¹ :=
  LieHom.logDefect_eq_zero_iff _ _ _ _ _

/-- Reversing the cooriented crossing negates its kernel-valued coefficient. -/
@[simp]
theorem defect_reverse : c.reverse.defect hk b t ht = -c.defect hk b t ht := by
  have hlabel : D.wallCrossingLabel ⟨σ.reverse.carrier, by simpa using hσ⟩
      (h.realCharacter c.reverse.normal) c.reverse.ker_normal =
      (D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal)⁻¹ := by
    simpa only [OrientedCell.reverse_carrier, reverse_normal, map_neg] using
      D.wallCrossingLabel_neg ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal
  have he := (d.truncationMap ℒ (Nat.le_succ k)).logDefect_inv (t c.minus) (t c.plus)
    (D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal)
    (c.truncation_label_mul hk b t ht)
  apply Subtype.ext
  simpa only [coe_defect, LieSubmodule.coe_neg, reverse_minus, reverse_plus,
    hlabel, LieHom.coe_logDefect] using congrArg Subtype.val he

end AdaptedWallCrossing

variable {D} {k : ℕ}
  (σ : (D.adaptedComplex (k + 1)).walls → OrientedCell h 1)
  (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
  (cross : ∀ Q, D.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property))
  (hk : D.LevelConsistent k)
  (b : WallComplement (fun j : D.active k => (D.wall j).support))
  (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
  (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)),
    x.val ∈ interior (P : Set V) →
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)

/-- The finite central crossing-defect cochain on the adapted wall cells, with
the given orientations, geometric crossing choices and lower-order chamber lifts. -/
def crossingDefectCochain :
    PolyhedralCochain R h (d.truncationMap ℒ (Nat.le_succ k)).ker 1 :=
  ∑ Q, PolyhedralCochain.mk (σ Q) ((cross Q).defect hk b t ht)

/-- The generator formula for the central crossing-defect cochain. -/
theorem crossingDefectCochain_def :
    crossingDefectCochain σ hσ cross hk b t ht =
      ∑ Q, PolyhedralCochain.mk (σ Q) ((cross Q).defect hk b t ht) := (rfl)

/-- Simultaneously reversing each wall orientation and its geometric crossing
preserves the central defect cochain. -/
@[simp]
theorem crossingDefectCochain_reverse :
    crossingDefectCochain (fun Q => (σ Q).reverse) (fun Q => by simpa using hσ Q)
      (fun Q => (cross Q).reverse) hk b t ht =
        crossingDefectCochain σ hσ cross hk b t ht := by
  simp [crossingDefectCochain_def]

end Mei.DirectedDiagram
