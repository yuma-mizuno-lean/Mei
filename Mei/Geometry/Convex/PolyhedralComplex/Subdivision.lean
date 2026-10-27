/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Analysis.Convex.Exposed
public import Mei.Analysis.Convex.Intrinsic
public import Mei.Geometry.Affine.Generic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Crossing words under subdivision of a complex

If a complex `C` subdivides a complex `D`, every cell of `D` is the union of the cells
of `C` that it contains and that have its dimension. In particular every wall of `D`
is covered by walls of `C`, and a wall of `C` lies in at most one wall of `D`.

Consequently the crossing word of a polygonal path for `D` is obtained from its word
for `C` by sending each wall of `C` to the wall of `D` containing it, inverted when the
coorientations disagree, and to `1` when no wall of `D` contains it. The path is only
assumed admissible for both wall families separately; crossing times are unchanged.

The covering argument uses Mathlib's `Subspace.exists_eq_top_of_iUnion_eq_univ`:
finitely many lower-dimensional cells cannot cover a relatively open part of a cell.
The word comparison follows `Mei.FinitePolyhedralComplex.wallDeletion`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C D : FinitePolyhedralComplex h}

/-- If a convex set is covered by cells contained in it, cells of its own dimension
already cover it, including its relative boundary. -/
theorem exists_mem_cells_subset_finrank_eq_of_cover (C : FinitePolyhedralComplex h)
    {P : Set V} (hconv : Convex ℝ P)
    (hcover : ∀ x ∈ P, ∃ Q ∈ C.cells, Q ⊆ P ∧ x ∈ Q) {x : V} (hx : x ∈ P) :
    ∃ Q ∈ C.cells, Q ⊆ P ∧ x ∈ Q ∧ Module.finrank ℝ (affineSpan ℝ Q).direction =
      Module.finrank ℝ (affineSpan ℝ P).direction := by
  classical
  have := h.finiteDimensional
  let S := C.cells.filter fun Q => Q ⊆ P ∧
    Module.finrank ℝ (affineSpan ℝ Q).direction = Module.finrank ℝ (affineSpan ℝ P).direction
  let G : Set V := ⋃ Q ∈ S, Q
  have hG : IsClosed G := (S.finite_toSet).isClosed_biUnion fun Q hQ =>
    (C.isConvexPolyhedron (Finset.mem_filter.mp hQ).1).isClosed
  suffices hPG : P ⊆ G by
    obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp (hPG hx)
    obtain ⟨hQ, hQP, hdim⟩ := Finset.mem_filter.mp hQ
    exact ⟨Q, hQ, hQP, hxQ, hdim⟩
  -- The relative interior is covered, since lower-dimensional cells cannot cover a
  -- relative neighbourhood of one of its points.
  have hri : intrinsicInterior ℝ P ⊆ G := by
    intro y hy
    by_contra hyG
    obtain ⟨U, hU, hUP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hy)
    let T := C.cells.filter fun Q => Q ⊆ P ∧
      Module.finrank ℝ (affineSpan ℝ Q).direction < Module.finrank ℝ (affineSpan ℝ P).direction
    obtain ⟨Q, hle⟩ := (affineSpan ℝ P).exists_direction_le_of_forall_mem
      (fun Q : T => affineSpan ℝ (Q : Set V)) (mem_affineSpan ℝ (intrinsicInterior_subset hy))
      (Filter.inter_mem hU (hG.isOpen_compl.mem_nhds hyG)) (by
        intro z hzA hzU
        obtain ⟨Q, hQ, hQP, hzQ⟩ := hcover z (hUP ⟨hzU.1, hzA⟩)
        have hlt : Module.finrank ℝ (affineSpan ℝ Q).direction <
            Module.finrank ℝ (affineSpan ℝ P).direction :=
          lt_of_le_of_ne (Submodule.finrank_mono
            (AffineSubspace.direction_le (affineSpan_mono ℝ hQP)))
            fun he => hzU.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨hQ, hQP, he⟩) hzQ)
        exact ⟨⟨Q, Finset.mem_filter.mpr ⟨hQ, hQP, hlt⟩⟩, subset_affineSpan ℝ Q hzQ⟩)
    exact (Submodule.finrank_mono hle).not_gt (Finset.mem_filter.mp Q.property).2.2
  -- Every point of the cell is a limit of relative interior points.
  intro y hy
  obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior hconv ⟨y, hy⟩
  have hseg : openSegment ℝ z y ⊆ G :=
    (hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hz
      (subset_intrinsicClosure hy)).trans hri
  exact closure_minimal hseg hG (segment_subset_closure_openSegment (right_mem_segment ℝ z y))

/-- In a subdivision every point of an old cell lies in a new cell of the same dimension
contained in it. -/
theorem IsSubdivision.exists_mem_cells_subset_finrank_eq (hCD : C.IsSubdivision D)
    {P : Set V} (hP : P ∈ D.cells) {x : V} (hx : x ∈ P) :
    ∃ Q ∈ C.cells, Q ⊆ P ∧ x ∈ Q ∧ Module.finrank ℝ (affineSpan ℝ Q).direction =
      Module.finrank ℝ (affineSpan ℝ P).direction :=
  C.exists_mem_cells_subset_finrank_eq_of_cover (D.isConvexPolyhedron hP).convex
    (fun _ hx => hCD.exists_mem_cells_subset hP hx) hx

/-- In a subdivision every point of an old wall lies in a new wall contained in it. -/
theorem IsSubdivision.exists_mem_walls_subset (hCD : C.IsSubdivision D) {P : Set V}
    (hP : P ∈ D.walls) {x : V} (hx : x ∈ P) : ∃ Q ∈ C.walls, Q ⊆ P ∧ x ∈ Q := by
  obtain ⟨Q, hQ, hQP, hxQ, hdim⟩ :=
    hCD.exists_mem_cells_subset_finrank_eq (D.mem_cells_of_mem_walls hP) hx
  refine ⟨Q, (C.mem_cellsOfCodimension 1 Q).mpr ⟨hQ, ?_⟩, hQP, hxQ⟩
  rw [hdim]
  exact D.finrank_direction_add_one_of_mem_walls hP

/-- The free-group homomorphism sending each wall of `C` to the wall of `D` containing it,
inverted unless its coorientation is a positive multiple of that wall's coorientation, and
to `1` when no wall of `D` contains it. -/
def wallCoarsening (C D : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (μ : D.walls → V →ₗ[ℝ] ℝ) : FreeGroup C.walls →* FreeGroup D.walls := by
  classical
  exact FreeGroup.lift fun Q =>
    if hQ : ∃ P : D.walls, (Q : Set V) ⊆ P then
      if ∃ c : ℝ, 0 < c ∧ ν Q = c • μ hQ.choose then FreeGroup.of hQ.choose
      else (FreeGroup.of hQ.choose)⁻¹
    else 1

variable (ν : C.walls → V →ₗ[ℝ] ℝ) (μ : D.walls → V →ₗ[ℝ] ℝ)

open scoped Classical in
/-- Coarsening sends a wall to the wall containing it, according to the coorientations. -/
theorem wallCoarsening_of_of_subset {Q : C.walls} {P : D.walls} (hQP : (Q : Set V) ⊆ P) :
    C.wallCoarsening D ν μ (FreeGroup.of Q) =
      if ∃ c : ℝ, 0 < c ∧ ν Q = c • μ P then FreeGroup.of P else (FreeGroup.of P)⁻¹ := by
  have hQ : ∃ P : D.walls, (Q : Set V) ⊆ P := ⟨P, hQP⟩
  have hP : hQ.choose = P := Subtype.ext (eq_of_subset_of_mem_walls Q.property
    hQ.choose.property P.property hQ.choose_spec hQP)
  classical
  simp only [wallCoarsening, FreeGroup.lift_apply_of, dite_eq_left hQ, hP]

/-- Coarsening kills a wall contained in no wall of `D`. -/
@[simp]
theorem wallCoarsening_of_of_forall_not_subset {Q : C.walls}
    (hQ : ∀ P : D.walls, ¬(Q : Set V) ⊆ P) :
    C.wallCoarsening D ν μ (FreeGroup.of Q) = 1 := by
  classical
  simp only [wallCoarsening, FreeGroup.lift_apply_of, dite_eq_right (not_exists.mpr hQ)]

variable {x y : WallComplement (fun P : C.walls => (P : Set V))}
  {x' y' : WallComplement (fun P : D.walls => (P : Set V))}

/-- The wall of `D` containing a wall of `C`, if any, with the same crossing time. -/
private def coarsenCrossing (a : C.walls × ℝ) : Option (D.walls × ℝ) := by
  classical
  exact if hQ : ∃ P : D.walls, (a.1 : Set V) ⊆ P then some (hQ.choose, a.2) else none

private theorem coarsenCrossing_eq_some {a : C.walls × ℝ} {b : D.walls × ℝ} :
    coarsenCrossing a = some b ↔ (a.1 : Set V) ⊆ b.1 ∧ a.2 = b.2 := by
  classical
  rcases b with ⟨P, t⟩
  simp only [coarsenCrossing]
  split_ifs with hQ
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨hQ.choose_spec, rfl⟩
    · rintro ⟨hQP, rfl⟩
      exact ⟨Subtype.ext (eq_of_subset_of_mem_walls a.1.property hQ.choose.property
        P.property hQ.choose_spec hQP), rfl⟩
  · simp only [false_iff, not_and]
    exact fun hQP => (hQ ⟨P, hQP⟩).elim

/-- A segment admissible for both complexes crosses each wall of `D` exactly when it
crosses a wall of `C` contained in it, at the same time. -/
private theorem orderedCrossings_coarsen (hCD : C.IsSubdivision D) (e : x ⟶ y) (e' : x' ⟶ y')
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    D.orderedCrossings e' = (C.orderedCrossings e).filterMap coarsenCrossing := by
  symm
  apply (D.orderedCrossings_eq_iff e' _).mpr
  constructor
  · exact (C.pairwise_orderedCrossings e).filterMap _ (by
      intro a a' haa b hb b' hb'
      rw [coarsenCrossing_eq_some] at hb hb'
      simpa only [← hb.2, ← hb'.2] using haa)
  · rintro ⟨P, t⟩
    rw [List.mem_filterMap, WallComplement.mem_crossings, ← hx, ← hy]
    constructor
    · rintro ⟨a, ha, hab⟩
      obtain ⟨hQP, rfl⟩ := coarsenCrossing_eq_some.mp hab
      have ha' := (WallComplement.mem_crossings x y a.1 a.2).mp ((C.mem_orderedCrossings e a).mp ha)
      exact ⟨ha'.1, hQP ha'.2⟩
    · rintro ⟨ht, hP⟩
      obtain ⟨Q, hQ, hQP, hxQ⟩ := hCD.exists_mem_walls_subset P.property hP
      exact ⟨(⟨Q, hQ⟩, t), (C.mem_orderedCrossings e _).mpr
        ((WallComplement.mem_crossings x y _ t).mpr ⟨ht, hxQ⟩),
        coarsenCrossing_eq_some.mpr ⟨hQP, rfl⟩⟩

/-- Coarsening carries the letter of a crossing of `C` to the letter of the containing
wall of `D`, for a velocity transverse to it. -/
private theorem wallCoarsening_crossingLetter
    (hν : ∀ Q, LinearMap.ker (ν Q) = (affineSpan ℝ (Q : Set V)).direction)
    (hμ : ∀ P, LinearMap.ker (μ P) = (affineSpan ℝ (P : Set V)).direction)
    {Q : C.walls} {P : D.walls} (hQP : (Q : Set V) ⊆ P) (hx : x.val = x'.val)
    (hy : y.val = y'.val) (hv : ν Q (y.val - x.val) ≠ 0) :
    C.wallCoarsening D ν μ (C.crossingLetter ν x y Q) = D.crossingLetter μ x' y' P := by
  have := h.finiteDimensional
  -- The two coorientations have the same kernel, hence are proportional.
  have hker : LinearMap.ker (ν Q) = LinearMap.ker (μ P) := by
    rw [hν, hμ]
    apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le (affineSpan_mono ℝ hQP))
    have hQd := C.finrank_direction_add_one_of_mem_walls Q.property
    have hPd := D.finrank_direction_add_one_of_mem_walls P.property
    omega
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c • μ P = ν Q := by
    have hmem := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => μ P) (K := ν Q)
      (by simp only [ciInf_const, hker, le_rfl])
    rwa [Set.range_const, Submodule.mem_span_singleton] at hmem
  have hv' : y'.val - x'.val = y.val - x.val := by rw [hx, hy]
  rw [C.crossingLetter_def, D.crossingLetter_def, hv']
  rw [← hc, LinearMap.smul_apply, smul_eq_mul] at hv
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hv
  have hμ0 : μ P (y.val - x.val) ≠ 0 := right_ne_zero_of_mul hv
  by_cases hpos : 0 < c
  · have hsign : 0 < ν Q (y.val - x.val) ↔ 0 < μ P (y.val - x.val) := by
      rw [← hc, LinearMap.smul_apply, smul_eq_mul, mul_pos_iff_of_pos_left hpos]
    have hagree : ∃ c : ℝ, 0 < c ∧ ν Q = c • μ P := ⟨c, hpos, hc.symm⟩
    by_cases hs : 0 < μ P (y.val - x.val)
    · simp only [ite_eq_left (hsign.mpr hs), ite_eq_left hs, map_inv,
        wallCoarsening_of_of_subset ν μ hQP, ite_eq_left hagree]
    · simp only [ite_eq_right (mt hsign.mp hs), ite_eq_right hs,
        wallCoarsening_of_of_subset ν μ hQP, ite_eq_left hagree]
  · have hneg : c < 0 := lt_of_le_of_ne (not_lt.mp hpos) hc0
    have hagree : ¬∃ c : ℝ, 0 < c ∧ ν Q = c • μ P := by
      rintro ⟨d, hd, hd'⟩
      obtain ⟨u, hu⟩ : ∃ u, μ P u ≠ 0 := ⟨_, hμ0⟩
      have hcd : c * μ P u = d * μ P u := by
        simpa only [LinearMap.smul_apply, smul_eq_mul] using
          (congrArg (fun f => f u) hc).trans (congrArg (fun f => f u) hd')
      linarith [mul_right_cancel₀ hu hcd]
    have hsign : 0 < ν Q (y.val - x.val) ↔ ¬0 < μ P (y.val - x.val) := by
      rw [← hc, LinearMap.smul_apply, smul_eq_mul, mul_pos_iff, not_lt]
      constructor
      · rintro (⟨hc', -⟩ | ⟨-, hm⟩)
        · exact absurd hc' hpos
        · exact hm.le
      · exact fun hle => Or.inr ⟨hneg, lt_of_le_of_ne hle hμ0⟩
    by_cases hs : 0 < μ P (y.val - x.val)
    · simp only [ite_eq_right (fun h' => hsign.mp h' hs), ite_eq_left hs,
        wallCoarsening_of_of_subset ν μ hQP, ite_eq_right hagree]
    · simp only [ite_eq_left (hsign.mpr hs), ite_eq_right hs, map_inv, inv_inv,
        wallCoarsening_of_of_subset ν μ hQP, ite_eq_right hagree]

/-- For a segment admissible for both complexes, coarsening its word for `C` gives its
word for `D`. -/
theorem segmentCrossingWord_coarsen (hCD : C.IsSubdivision D)
    (hν : ∀ Q, LinearMap.ker (ν Q) = (affineSpan ℝ (Q : Set V)).direction)
    (hμ : ∀ P, LinearMap.ker (μ P) = (affineSpan ℝ (P : Set V)).direction)
    (e : x ⟶ y) (e' : x' ⟶ y') (hx : x.val = x'.val) (hy : y.val = y'.val) :
    D.segmentCrossingWord μ e' = C.wallCoarsening D ν μ (C.segmentCrossingWord ν e) := by
  have hl (l : List (C.walls × ℝ)) (hl : ∀ a ∈ l, a ∈ C.orderedCrossings e) :
      ((l.filterMap coarsenCrossing).map fun a => D.crossingLetter μ x' y' a.1).prod =
        C.wallCoarsening D ν μ ((l.map fun a => C.crossingLetter ν x y a.1).prod) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ih := ih fun b hb => hl b (List.mem_cons_of_mem a hb)
      rw [List.map_cons, List.prod_cons, map_mul]
      cases hf : coarsenCrossing (D := D) a with
      | none =>
        rw [List.filterMap_cons_none hf, ih]
        have hQ : ∀ P : D.walls, ¬(a.1 : Set V) ⊆ P := fun P hQP => by
          simpa [hf] using (coarsenCrossing_eq_some (b := (P, a.2))).mpr ⟨hQP, rfl⟩
        have hz : C.wallCoarsening D ν μ (C.crossingLetter ν x y a.1) = 1 := by
          rw [C.crossingLetter_def]
          split_ifs <;> simp [wallCoarsening_of_of_forall_not_subset ν μ hQ]
        rw [hz, one_mul]
      | some b =>
        rw [List.filterMap_cons_some hf, List.map_cons, List.prod_cons, ih]
        obtain ⟨hQP, -⟩ := coarsenCrossing_eq_some.mp hf
        rw [wallCoarsening_crossingLetter ν μ hν hμ hQP hx hy
          (C.normal_velocity_ne_zero (ν a.1) e (hl a List.mem_cons_self) (hν a.1))]
  simpa only [D.segmentCrossingWord_def, C.segmentCrossingWord_def,
    orderedCrossings_coarsen hCD e e' hx hy, ← List.filterMap_reverse] using
      hl (C.orderedCrossings e).reverse fun a ha => List.mem_reverse.mp ha

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C D : Mei.FinitePolyhedralComplex h}

/-- For a polygonal path admissible for both a complex and a complex it subdivides,
coarsening its crossing word for the finer complex gives its word for the coarser one. -/
theorem crossingWord_coarsen (hCD : C.IsSubdivision D) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (μ : D.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ Q, LinearMap.ker (ν Q) = (affineSpan ℝ (Q : Set V)).direction)
    (hμ : ∀ P, LinearMap.ker (μ P) = (affineSpan ℝ (P : Set V)).direction)
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    {x' y' : WallComplement (fun P : D.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    q.crossingWord μ = C.wallCoarsening D ν μ (p.crossingWord ν) := by
  induction p generalizing x' y' with
  | nil =>
    cases q with
    | nil => simp
    | cons q e => simpa using congrArg List.length hpq
  | @cons z w p e ih =>
    cases q with
    | nil => simpa using congrArg List.length hpq
    | @cons z' w' q e' =>
      simp only [vertices_cons, List.concat_eq_append, List.map_append, List.map_cons,
        List.map_nil] at hpq
      obtain ⟨hpq, hw⟩ := List.append_inj' hpq rfl
      have hz : z.val = z'.val := by
        have hpq' := hpq
        rw [← p.dropLast_append_end_eq, ← q.dropLast_append_end_eq, List.map_append,
          List.map_append, List.map_singleton, List.map_singleton] at hpq'
        simpa using (List.append_inj' hpq' rfl).2
      rw [crossingWord_cons, crossingWord_cons, map_mul, ih q hpq,
        Mei.FinitePolyhedralComplex.segmentCrossingWord_coarsen ν μ hCD hν hμ e e' hz
          (by simpa using hw)]

end Quiver.Path
