/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.PathSubdivision

/-!
# Subdivision into single-crossing segments

Every admissible polygonal path through the walls of a finite polyhedral complex
has a subdivision whose segments meet at most one wall. The endpoints are retained,
and every inserted vertex lies on its original segment and outside all walls.
Consequently the subdivision preserves the crossing word and permits local
single-crossing formulas to compute transport along arbitrary polygonal paths.

The construction splits a segment between its first two crossings and repeats on
the remaining segment. It uses `FinitePolyhedralComplex.orderedCrossings_subdivide`,
`WallComplement.AdmissibleSegment.subdivide_left` and `subdivide_right`, and the
existing `Quiver.Path.IsSubdivision` relation. No perturbation of the path is needed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)

private theorem exists_crossing_gap
    {x y : WallComplement (fun P : C.walls => (P : Set V))} (e : x ⟶ y)
    (a b : C.walls × ℝ) (l : List (C.walls × ℝ))
    (hl : C.orderedCrossings e = a :: b :: l) :
    ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ a.2 < t ∧
      ∀ d ∈ WallComplement.crossings x y, d.2 ≤ t → d = a := by
  have ha := (C.mem_orderedCrossings e a).mp (by simp [hl])
  have hb := (C.mem_orderedCrossings e b).mp (by simp [hl])
  have haI := (WallComplement.mem_crossings x y a.1 a.2).mp ha
  have hbI := (WallComplement.mem_crossings x y b.1 b.2).mp hb
  have haoo := (e.down.crossing_mem_intrinsicInterior haI.1 haI.2).1
  have hboo := (e.down.crossing_mem_intrinsicInterior hbI.1 hbI.2).1
  have hpair := C.pairwise_orderedCrossings e
  rw [hl, List.pairwise_cons] at hpair
  obtain ⟨t, hat, htb⟩ := exists_between (hpair.1 b (by simp))
  refine ⟨t, ⟨haoo.1.trans hat, htb.trans hboo.2⟩, hat, ?_⟩
  intro d hd hdt
  have hd' := (C.mem_orderedCrossings e d).mpr hd
  simp only [hl, List.mem_cons] at hd'
  rcases hd' with rfl | rfl | hd'
  · rfl
  · exact (not_le_of_gt htb hdt).elim
  · have hbd := (List.pairwise_cons.mp hpair.2).1 d hd'
    exact (not_lt_of_ge (hdt.trans htb.le) hbd).elim

private theorem exists_split_first_crossing
    {x y : WallComplement (fun P : C.walls => (P : Set V))} (e : x ⟶ y)
    (a b : C.walls × ℝ) (l : List (C.walls × ℝ))
    (hl : C.orderedCrossings e = a :: b :: l) :
    ∃ (z : WallComplement (fun P : C.walls => (P : Set V)))
      (_ : x ⟶ z) (e₂ : z ⟶ y) (t : ℝ),
      t ∈ Ioo (0 : ℝ) 1 ∧ z.val = AffineMap.lineMap x.val y.val t ∧
      (WallComplement.crossings x z).Subsingleton ∧
      (C.orderedCrossings e₂).length < (C.orderedCrossings e).length := by
  obtain ⟨t, ht, hat, hgap⟩ := C.exists_crossing_gap e a b l hl
  let z : WallComplement (fun P : C.walls => (P : Set V)) :=
    ⟨AffineMap.lineMap x.val y.val t, fun P hP => by
      have hd := hgap (P, t) ((WallComplement.mem_crossings x y P t).mpr
        ⟨⟨ht.1.le, ht.2.le⟩, hP⟩) le_rfl
      exact (ne_of_gt hat) (congrArg Prod.snd hd)⟩
  have hz : z.val = AffineMap.lineMap x.val y.val t := rfl
  let e₁ : x ⟶ z := ⟨e.down.subdivide_left ⟨ht.1, ht.2.le⟩ hz⟩
  let e₂ : z ⟶ y := ⟨e.down.subdivide_right ⟨ht.1.le, ht.2⟩ hz⟩
  have hleft (d : C.walls × ℝ) (hd : d ∈ WallComplement.crossings x z) :
      (d.1, d.2 * t) = a := by
    have hd' := (WallComplement.mem_crossings_subdivide_left hz
      ⟨ht.1, ht.2.le⟩ d.1 d.2).mp hd
    exact hgap _ hd'.1 (mul_le_of_le_one_left ht.1.le hd'.2)
  have hsingle : (WallComplement.crossings x z).Subsingleton := by
    intro d hd f hf
    have he := (hleft d hd).trans (hleft f hf).symm
    obtain ⟨hfst, hsnd⟩ := Prod.mk.inj he
    exact Prod.ext hfst (mul_right_cancel₀ ht.1.ne' hsnd)
  have hnonempty : (C.orderedCrossings e₁) ≠ [] := by
    have ham : (a.1, a.2 / t) ∈ WallComplement.crossings x z := by
      rw [WallComplement.mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩]
      have ha := (C.mem_orderedCrossings e a).mp (by simp [hl])
      exact ⟨by simpa only [div_mul_cancel₀ _ ht.1.ne'] using ha,
        (div_le_one ht.1).mpr hat.le⟩
    exact List.ne_nil_of_mem ((C.mem_orderedCrossings e₁ _).mpr ham)
  have hlen := congrArg List.length (C.orderedCrossings_subdivide e e₁ e₂ ht hz)
  simp only [List.length_append, List.length_map] at hlen
  have hpos := List.length_pos_iff.mpr hnonempty
  exact ⟨z, e₁, e₂, t, ht, hz, hsingle, by omega⟩

/-- Subdivide an admissible segment, without moving its endpoints, so that each
new segment has at most one indexed wall crossing. -/
theorem exists_segment_subdivision_subsingleton_crossings
    {x y : WallComplement (fun P : C.walls => (P : Set V))} (e : x ⟶ y) :
    ∃ q : AdmissiblePLPath x y, e.toPath.IsSubdivision q ∧
      q.vertices.IsChain (fun u v => (WallComplement.crossings u v).Subsingleton) := by
  generalize hn : (C.orderedCrossings e).length = n
  induction n using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    rcases hl : C.orderedCrossings e with _ | ⟨a, _ | ⟨b, l⟩⟩
    · refine ⟨e.toPath, .refl _, ?_⟩
      simp only [Quiver.Path.vertices_toPath, List.isChain_pair]
      intro d hd
      have := (C.mem_orderedCrossings e d).mpr hd
      simp [hl] at this
    · refine ⟨e.toPath, .refl _, ?_⟩
      simp only [Quiver.Path.vertices_toPath, List.isChain_pair]
      intro d hd f hf
      have hd' := (C.mem_orderedCrossings e d).mpr hd
      have hf' := (C.mem_orderedCrossings e f).mpr hf
      simp only [hl, List.mem_singleton] at hd' hf'
      exact hd'.trans hf'.symm
    · obtain ⟨z, e₁, e₂, t, ht, hz, hsingle, hlt⟩ :=
        C.exists_split_first_crossing e a b l hl
      obtain ⟨q, hq, hqsmall⟩ := ih _ (hn ▸ hlt) e₂ rfl
      refine ⟨e₁.toPath.comp q,
        (Quiver.Path.IsSubdivision.split e e₁ e₂ ht hz).trans (.comp (.refl _) hq), ?_⟩
      exact (Quiver.Path.isChain_vertices_comp _ _ _).mpr
        ⟨by simpa only [Quiver.Path.vertices_toPath, List.isChain_pair] using hsingle, hqsmall⟩

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Every admissible polygonal path has a subdivision into segments meeting at
most one wall. This retains the path's geometry and its ordered crossing word. -/
theorem exists_subdivision_subsingleton_crossings (p : AdmissiblePLPath x y) :
    ∃ q : AdmissiblePLPath x y, p.IsSubdivision q ∧
      q.vertices.IsChain (fun u v => (WallComplement.crossings u v).Subsingleton) := by
  induction p with
  | nil => exact ⟨.nil, .refl _, by simp⟩
  | cons p e ih =>
    obtain ⟨q, hq, hsmall⟩ := ih
    obtain ⟨r, hr, hrsmall⟩ := C.exists_segment_subdivision_subsingleton_crossings e
    exact ⟨q.comp r, .comp hq hr,
      (isChain_vertices_comp _ _ _).mpr ⟨hsmall, hrsmall⟩⟩

end Quiver.Path
