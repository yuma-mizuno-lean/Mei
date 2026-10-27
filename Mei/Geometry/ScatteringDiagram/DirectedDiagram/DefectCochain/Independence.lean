/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Basic
public import Mei.Geometry.Convex.PolyhedralComplex.OrientedIncidence

/-!
# Independence of geometric crossing choices

For a fixed oriented adapted wall, every geometric crossing chooses the same
source and target chambers and computes the same crossing label. Consequently
its central defect, and the finite crossing-defect cochain, are independent of
the geometric crossing choices. The chamber lifts remain fixed.

Every sufficiently short positive transverse segment through any relative
interior point realizes these same chambers and this same defect. This permits
the cellwise coefficients to be used along meridians whose crossings need not
be the witnesses originally used to construct the cochain.

The geometric argument uses the positive-ray chamber uniqueness of
`FinitePolyhedralComplex.existsUnique_cell_of_positive_transverse_rays` and
`Convex.eventually_add_smul_mem_interior_of_ker_le`. The crossing labels and
kernel-valued coefficients are those of `DirectedDiagram.wallCrossingLabel`
and `DirectedDiagram.AdaptedWallCrossing.defect`.
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
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι}

namespace AdaptedWallCrossing

variable {l : ℕ} {σ : OrientedCell h 1}
  {hσ : σ.carrier ∈ (D.adaptedComplex l).walls}

/-- Every positive transverse ray from the wall interior enters the stored
target chamber, independently of the segment used to construct the crossing. -/
theorem eventually_mem_interior_plus (c : D.AdaptedWallCrossing σ hσ)
    {q v : V} (hq : q ∈ intrinsicInterior ℝ σ.carrier)
    (hv : 0 < h.realCharacter c.normal v) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, q + a • v ∈ interior (c.plus : Set V) := by
  obtain ⟨q₀, v₀, a, hq₀, hv₀, ha, _, y, _, _, hy, _, hyi, _⟩ := c.realized
  have hsub : σ.carrier ⊆ (c.plus : Set V) := by
    rw [← c.inter_eq]
    exact inter_subset_right
  have hdiff : h.realCharacter c.normal (q - q₀) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [c.ker_normal]
    exact (affineSpan ℝ σ.carrier).vsub_mem_direction
      (subset_affineSpan ℝ _ (intrinsicInterior_subset hq))
      (subset_affineSpan ℝ _ (intrinsicInterior_subset hq₀))
  have hypos : 0 < h.realCharacter c.normal (y.val - q) := by
    rw [hy]
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hdiff ⊢
    nlinarith
  exact ((D.adaptedComplex l).isConvexPolyhedron
    (((D.adaptedComplex l).mem_cellsOfCodimension 0 _).mp c.plus.property).1).convex
    |>.eventually_add_smul_mem_interior_of_ker_le hsub (h.realCharacter c.normal)
      c.ker_normal.le hq hyi hypos hv

/-- The two stored incident chambers work simultaneously at every wall
interior point and every positive transverse velocity. -/
theorem eventually_mem_interiors (c : D.AdaptedWallCrossing σ hσ)
    {q v : V} (hq : q ∈ intrinsicInterior ℝ σ.carrier)
    (hv : 0 < h.realCharacter c.normal v) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      q - a • v ∈ interior (c.minus : Set V) ∧
      q + a • v ∈ interior (c.plus : Set V) := by
  have hm := c.reverse.eventually_mem_interior_plus (by simpa using hq)
    (v := -v) (by simpa using hv)
  simpa only [reverse_plus, smul_neg, sub_eq_add_neg] using
    hm.and (c.eventually_mem_interior_plus hq hv)

/-- All geometric crossings of a fixed oriented wall have the same target
chamber, even when their integral normal representatives differ. -/
theorem plus_eq (c c' : D.AdaptedWallCrossing σ hσ) : c.plus = c'.plus := by
  obtain ⟨q, _, _, hq, _⟩ := c.realized
  have hsame (w : V) : SignType.sign (h.realCharacter c.normal w) =
      SignType.sign (h.realCharacter c'.normal w) :=
    (c.sign_normal w).trans (c'.sign_normal w).symm
  obtain ⟨Q, _, hunique⟩ :=
    (D.adaptedComplex l).existsUnique_cell_of_positive_transverse_rays hσ
      (h.realCharacter c.normal) c.ker_normal
      ⟨q, hq, by simp only [D.support_adaptedComplex, interior_univ, mem_univ]⟩
  have hplus (a : D.AdaptedWallCrossing σ hσ)
      (hs : ∀ w, 0 < h.realCharacter c.normal w → 0 < h.realCharacter a.normal w) :
      (a.plus : Set V) = Q := by
    apply hunique
    refine ⟨a.plus.property, ?_, fun q hq v hv => a.eventually_mem_interior_plus hq (hs v hv)⟩
    rw [← a.inter_eq]
    exact inter_subset_right
  apply Subtype.ext
  exact (hplus c (fun _ hw => hw)).trans
    (hplus c' (fun w hw => by
      rwa [← sign_eq_one_iff, ← hsame, sign_eq_one_iff])).symm

/-- All geometric crossings of a fixed oriented wall have the same source chamber. -/
theorem minus_eq (c c' : D.AdaptedWallCrossing σ hσ) : c.minus = c'.minus := by
  simpa only [reverse_plus] using c.reverse.plus_eq c'.reverse

/-- The oriented crossing label is independent of the integral representative
of the conormal orientation. -/
theorem wallCrossingLabel_eq (c c' : D.AdaptedWallCrossing σ hσ) :
    D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal =
      D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c'.normal) c'.ker_normal := by
  obtain ⟨q, v, _, hq, hv, _⟩ := c.realized
  have hv' : 0 < h.realCharacter c'.normal v := by
    rw [← sign_eq_one_iff, c'.sign_normal, ← c.sign_normal, sign_eq_one_iff]
    exact hv
  exact (D.wallCrossingLabel_eq_combinedLabel ⟨σ.carrier, hσ⟩ _ _ hq hv).trans
    (D.wallCrossingLabel_eq_combinedLabel ⟨σ.carrier, hσ⟩ _ _ hq hv').symm

variable {k : ℕ} {σ : OrientedCell h 1}
  {hσ : σ.carrier ∈ (D.adaptedComplex (k + 1)).walls}
  (c c' : D.AdaptedWallCrossing σ hσ)
  (hk : D.LevelConsistent k)
  (b : WallComplement (fun j : D.active k => (D.wall j).support))
  (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
  (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)),
    x.val ∈ interior (P : Set V) →
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)

/-- Fixing the chamber lifts, the central coefficient depends only on the
oriented wall, not on the geometric crossing choices. -/
theorem defect_eq : c.defect hk b t ht = c'.defect hk b t ht := by
  apply Subtype.ext
  simp only [coe_defect, c.plus_eq c', c.minus_eq c', c.wallCrossingLabel_eq c']

omit c' in
/-- At every wall interior point, all sufficiently short positive crossings
realize the fixed cellwise defect between the fixed incident chamber lifts. -/
theorem eventually_exists_log_defect_eq {q v : V}
    (hq : q ∈ intrinsicInterior ℝ σ.carrier) (hv : 0 < h.realCharacter c.normal v) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
        (e : x ⟶ y),
        x.val = q - a • v ∧ y.val = q + a • v ∧
        x.val ∈ interior (c.minus : Set V) ∧ y.val ∈ interior (c.plus : Set V) ∧
        BCHGroup.log ((t c.plus)⁻¹ * D.levelPathProduct (k + 1) e.toPath * t c.minus) =
          (c.defect hk b t ht : d.truncatedLie ℒ (k + 1)) := by
  filter_upwards [c.eventually_mem_interiors hq hv,
    D.eventually_exists_levelPathProduct_eq_wallCrossingLabel
      ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal hq hv] with a hi he
  obtain ⟨x, y, e, hx, hy, hlabel⟩ := he
  exact ⟨x, y, e, hx, hy, hx ▸ hi.1, hy ▸ hi.2, by rw [hlabel, coe_defect]⟩

end AdaptedWallCrossing

/-- Fixing oriented wall cells and chamber lifts, changing every geometric
crossing choice preserves the entire central crossing-defect cochain. -/
theorem crossingDefectCochain_congr {k : ℕ}
    (σ : (D.adaptedComplex (k + 1)).walls → OrientedCell h 1)
    (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
    (cross cross' : ∀ Q, D.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property))
    (hk : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support))
    (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
    (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
      (x : WallComplement (fun j : D.active k => (D.wall j).support)),
      x.val ∈ interior (P : Set V) →
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x) :
    crossingDefectCochain σ hσ cross hk b t ht =
      crossingDefectCochain σ hσ cross' hk b t ht := by
  simp only [crossingDefectCochain_def]
  exact Finset.sum_congr rfl fun Q _ => congrArg (PolyhedralCochain.mk (σ Q))
    ((cross Q).defect_eq (cross' Q) hk b t ht)

end Mei.DirectedDiagram
