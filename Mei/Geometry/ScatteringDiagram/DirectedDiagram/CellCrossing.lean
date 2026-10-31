/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Adapted
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing.Constancy
public import Mei.Geometry.Convex.PolyhedralComplex.Chamber
public import Mei.Geometry.Convex.PolyhedralComplex.Incidence

/-!
# Oriented crossing labels on adapted wall cells

Every relative interior point of an adapted wall cell is regular for the active
indexed wall family. The combined label is constant throughout that relative
interior and on the positive side of any chosen coorientation. Thus each oriented
wall cell has one crossing label, realized by every sufficiently short positively
transverse segment through any of its relative interior points. Artificial walls
carry the identity. Reversing the coorientation inverts the crossing label.
Positive rescaling preserves it. Each short crossing is realized between two
distinct incident full cells, with endpoints in their ordinary interiors.

These labels provide the crossing factors for the central defects of chamber
trivializations. They retain all coincident indexed contributions, without requiring
consistency. The construction combines `DirectedDiagram.adaptedComplex` and its
support-incidence characterization with `DirectedDiagram.combinedLabel` and its
short-segment realization theorem. Incident full cells are supplied by
`FinitePolyhedralComplex.exists_transverse_wall_chambers`.
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

/-- Relative interior points of adapted wall cells avoid the active singular support,
including relative boundaries of repeated or overlapping indexed supports. -/
theorem notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall {k : ℕ}
    {Q : Set V} (hQ : Q ∈ (D.adaptedComplex k).walls) {θ : V}
    (hθ : θ ∈ intrinsicInterior ℝ Q) :
    θ ∉ singularSupport (fun j : D.active k => (D.wall j).support) := by
  have hcell := (D.adaptedComplex k).mem_cells_of_mem_walls hQ
  have hspan (j : D.active k) (hj : θ ∈ (D.wall j).support) :
      affineSpan ℝ Q = affineSpan ℝ (D.wall j).support :=
    D.affineSpan_eq_of_adaptedWall_subset hQ j
      ((D.mem_support_iff_of_mem_intrinsicInterior_adaptedComplex k hcell hθ j).mp hj)
  intro hs
  rcases mem_singularSupport.mp hs with ⟨j, hj⟩ | ⟨j, l, hne, hj, hl⟩
  · have hjmem := intrinsicFrontier_subset (D.wall j).isConvexPolyhedron.isClosed hj
    have hsub := (D.mem_support_iff_of_mem_intrinsicInterior_adaptedComplex
      k hcell hθ j).mp hjmem
    have hint := intrinsicInterior_mono_of_affineSpan_eq hsub (hspan j hjmem) hθ
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hj
    exact hj.2 hint
  · exact hne (congrArg AffineSubspace.direction ((hspan j hj).symm.trans (hspan l hl)))

/-- Throughout an adapted wall interior, positive transverse crossings for the same
coorientation have the same combined label. -/
theorem combinedLabel_eq_of_mem_intrinsicInterior_adaptedWall {k : ℕ}
    {Q : Set V} (hQ : Q ∈ (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ Q).direction)
    {θ η v w : V} (hθ : θ ∈ intrinsicInterior ℝ Q) (hη : η ∈ intrinsicInterior ℝ Q)
    (hv : 0 < ν v) (hw : 0 < ν w) :
    D.combinedLabel k θ v
        (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall hQ hθ) =
      D.combinedLabel k η w
        (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall hQ hη) := by
  have hcell := (D.adaptedComplex k).mem_cells_of_mem_walls hQ
  apply D.combinedLabel_eq_of_incident_iff_of_pos_iff
    (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall hQ hθ)
    (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall hQ hη)
  · intro j
    exact (D.mem_support_iff_of_mem_intrinsicInterior_adaptedComplex k hcell hθ j).trans
      (D.mem_support_iff_of_mem_intrinsicInterior_adaptedComplex k hcell hη j).symm
  · intro j hj
    have hsub := (D.mem_support_iff_of_mem_intrinsicInterior_adaptedComplex
      k hcell hθ j).mp hj
    have hker : ν.ker ≤ (h.realCharacter (D.wall j).normal).ker := by
      rw [hν, ← (D.wall j).direction_support,
        D.affineSpan_eq_of_adaptedWall_subset hQ j hsub]
    exact ν.apply_pos_iff_of_ker_le_ker _ hker hv hw

private theorem existsUnique_wallCrossingLabel {k : ℕ} (Q : (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction) :
    ∃! X : d.truncatedGroup ℒ k, ∀ (θ v : V)
      (hθ : θ ∈ intrinsicInterior ℝ (Q : Set V)), 0 < ν v →
      D.combinedLabel k θ v
        (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall Q.property hθ) = X := by
  have := h.finiteDimensional
  have hcell := (D.adaptedComplex k).mem_cells_of_mem_walls Q.property
  obtain ⟨θ, hθ⟩ := ((D.adaptedComplex k).nonempty _ hcell).intrinsicInterior
    ((D.adaptedComplex k).isConvexPolyhedron hcell).convex
  have hne : ν ≠ 0 := by
    intro he
    have hd := (D.adaptedComplex k).finrank_direction_add_one_of_mem_walls Q.property
    rw [← hν, he, LinearMap.ker_zero, finrank_top] at hd
    omega
  obtain ⟨v, hv⟩ := LinearMap.surjective hne 1
  have hvpos : 0 < ν v := by rw [hv]; exact zero_lt_one
  refine ⟨D.combinedLabel k θ v
    (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall Q.property hθ), ?_, ?_⟩
  · intro η w hη hw
    exact D.combinedLabel_eq_of_mem_intrinsicInterior_adaptedWall Q.property ν hν hη hθ hw hvpos
  · intro X hX
    exact (hX θ v hθ hvpos).symm

/-- The crossing factor from the negative to the positive side of a cooriented
adapted wall cell. Each incident wall label is inverted precisely when that wall's
own normal evaluates positively on the crossing velocity. -/
def wallCrossingLabel {k : ℕ} (Q : (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction) :
    d.truncatedGroup ℒ k :=
  Classical.choose (D.existsUnique_wallCrossingLabel Q ν hν)

/-- Every relative interior point and every positive transverse velocity compute
the cell's crossing label. -/
theorem wallCrossingLabel_eq_combinedLabel {k : ℕ} (Q : (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction)
    {θ v : V} (hθ : θ ∈ intrinsicInterior ℝ (Q : Set V)) (hv : 0 < ν v) :
    D.wallCrossingLabel Q ν hν = D.combinedLabel k θ v
      (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall Q.property hθ) :=
  ((Classical.choose_spec (D.existsUnique_wallCrossingLabel Q ν hν)).1 θ v hθ hv).symm

/-- The crossing label is uniquely characterized by its positive regular crossings. -/
theorem wallCrossingLabel_eq_iff {k : ℕ} (Q : (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction)
    (X : d.truncatedGroup ℒ k) :
    D.wallCrossingLabel Q ν hν = X ↔ ∀ (θ v : V)
      (hθ : θ ∈ intrinsicInterior ℝ (Q : Set V)), 0 < ν v →
      D.combinedLabel k θ v
        (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall Q.property hθ) = X := by
  constructor
  · rintro rfl θ v hθ hv
    exact (D.wallCrossingLabel_eq_combinedLabel Q ν hν hθ hv).symm
  · intro hX
    exact ((Classical.choose_spec (D.existsUnique_wallCrossingLabel Q ν hν)).2 X hX).symm

/-- An artificial wall, contained in no active support, has identity crossing label. -/
@[simp]
theorem wallCrossingLabel_eq_one {k : ℕ} (Q : (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction)
    (hoff : ∀ j : D.active k, ¬ (Q : Set V) ⊆ (D.wall j).support) :
    D.wallCrossingLabel Q ν hν = 1 := by
  apply (D.wallCrossingLabel_eq_iff Q ν hν 1).mpr
  intro θ v hθ _
  apply D.combinedLabel_eq_one_of_forall_notMem
  intro j hj
  exact hoff j ((D.mem_support_iff_of_mem_intrinsicInterior_adaptedComplex k
    ((D.adaptedComplex k).mem_cells_of_mem_walls Q.property) hθ j).mp hj)

/-- Positive rescaling of a cell's coorientation preserves its crossing label. -/
@[simp]
theorem wallCrossingLabel_smul_pos {k : ℕ} (Q : (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction)
    {r : ℝ} (hr : 0 < r) :
    D.wallCrossingLabel Q (r • ν) (by rwa [LinearMap.ker_smul _ _ hr.ne']) =
      D.wallCrossingLabel Q ν hν := by
  apply (D.wallCrossingLabel_eq_iff Q (r • ν) _ _).mpr
  intro θ v hθ hv
  exact (D.wallCrossingLabel_eq_combinedLabel Q ν hν hθ
    ((mul_pos_iff_of_pos_left hr).mp hv)).symm

/-- Reversing a cell's coorientation inverts its crossing label. -/
@[simp]
theorem wallCrossingLabel_neg {k : ℕ} (Q : (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction) :
    D.wallCrossingLabel Q (-ν) (by simpa using hν) = (D.wallCrossingLabel Q ν hν)⁻¹ := by
  apply (D.wallCrossingLabel_eq_iff Q (-ν) _ _).mpr
  intro θ v hθ hv
  have hpos : 0 < ν (-v) := by simpa using hv
  have htrans := D.realCharacter_normal_ne_zero_of_mem_intrinsicInterior_adaptedWall
    Q.property ν hν hθ hpos.ne'
  calc
    _ = (D.combinedLabel k θ (-v)
        (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall Q.property hθ))⁻¹ := by
      simpa only [neg_neg] using D.combinedLabel_neg k θ (-v) _ htrans
    _ = _ := by rw [← D.wallCrossingLabel_eq_combinedLabel Q ν hν hθ hpos]

/-- Short positively transverse segments at any relative interior point realize
the crossing label, with the same factor for every sufficiently small length. -/
theorem eventually_exists_levelPathProduct_eq_wallCrossingLabel {k : ℕ}
    (Q : (D.adaptedComplex k).walls) (ν : V →ₗ[ℝ] ℝ)
    (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction)
    {θ v : V} (hθ : θ ∈ intrinsicInterior ℝ (Q : Set V)) (hv : 0 < ν v) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement (fun j : D.active k => (D.wall j).support)) (e : x ⟶ y),
        x.val = θ - a • v ∧ y.val = θ + a • v ∧
        D.levelPathProduct k e.toPath = D.wallCrossingLabel Q ν hν := by
  rw [D.wallCrossingLabel_eq_combinedLabel Q ν hν hθ hv]
  apply D.eventually_exists_levelPathProduct_eq_combinedLabel
  exact D.realCharacter_normal_ne_zero_of_mem_intrinsicInterior_adaptedWall
    Q.property ν hν hθ hv.ne'

/-- A positive transverse crossing at an adapted wall is realized between two
distinct incident full cells, uniformly for every sufficiently short length.
The endpoints lie in ordinary interiors, so finite chamber lifts apply to them. -/
theorem exists_adapted_wall_crossing {k : ℕ} (Q : (D.adaptedComplex k).walls)
    (ν : V →ₗ[ℝ] ℝ) (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction)
    {θ v : V} (hθ : θ ∈ intrinsicInterior ℝ (Q : Set V)) (hv : 0 < ν v) :
    ∃ Pminus Pplus : (D.adaptedComplex k).cellsOfCodimension 0,
      Pminus ≠ Pplus ∧ (Pminus : Set V) ∩ (Pplus : Set V) = (Q : Set V) ∧
      ∀ᶠ a : ℝ in 𝓝[>] 0,
        ∃ (x y : WallComplement (fun j : D.active k => (D.wall j).support)) (e : x ⟶ y),
          x.val = θ - a • v ∧ y.val = θ + a • v ∧
          x.val ∈ interior (Pminus : Set V) ∧ y.val ∈ interior (Pplus : Set V) ∧
          D.levelPathProduct k e.toPath = D.wallCrossingLabel Q ν hν := by
  have htrans : v ∉ (affineSpan ℝ (Q : Set V)).direction := by
    rw [← hν, LinearMap.mem_ker]
    exact hv.ne'
  obtain ⟨Pminus, hm, Pplus, hp, hne, hinter, ε, hε, hshort⟩ :=
    (D.adaptedComplex k).exists_transverse_wall_chambers Q.property hθ
      (by simp only [D.support_adaptedComplex, interior_univ, mem_univ]) htrans
  have hmInt := Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
    ((D.adaptedComplex k).affineSpan_eq_top_of_mem_cellsOfCodimension_zero hm)
  have hpInt := Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
    ((D.adaptedComplex k).affineSpan_eq_top_of_mem_cellsOfCodimension_zero hp)
  refine ⟨⟨Pminus, hm⟩, ⟨Pplus, hp⟩, fun he => hne (congrArg Subtype.val he), hinter, ?_⟩
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a ∈ Ioo (0 : ℝ) ε :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨ε, hε, Subset.rfl⟩
  filter_upwards [hsmall,
    D.eventually_exists_levelPathProduct_eq_wallCrossingLabel Q ν hν hθ hv] with a ha he
  obtain ⟨x, y, e, hx, hy, he⟩ := he
  obtain ⟨hxm, hyp⟩ := hshort a ha
  refine ⟨x, y, e, hx, hy, ?_, ?_, he⟩
  · simpa only [hx, hmInt] using hxm
  · simpa only [hy, hpInt] using hyp

end Mei.DirectedDiagram
