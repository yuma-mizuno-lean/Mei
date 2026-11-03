/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Itinerary
public import Mei.Geometry.Convex.PolyhedralComplex.Subdivision

/-!
# Chambers and crossing letters under coarsening

If a complex `C` subdivides a complex `D`, a point off the walls of `C` is off the walls of
`D`, so the chambers of `C` (connected components of the complement of its walls) map to
chambers of `D` (`IsSubdivision.restrictChamber`). The two sides of a wall `Q` of `C` map to
the two sides of the wall `P` of `D` containing it, when their coorientations are positively
proportional, and to a single chamber when `Q` lies in no wall of `D`.

Dually, a crossing letter of `C` coarsens to the letter of the wall of `D` containing its
wall, or to nothing (`coarsenLetter`). For a polygonal path admissible for both complexes,
the crossing letters for `D` are the coarsened crossing letters for `C`
(`Quiver.Path.crossingLetters_coarsen`), the letter-level form of
`Quiver.Path.crossingWord_coarsen`.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {C D : FinitePolyhedralComplex h}

/-- A point off the walls of a subdivision is off the walls of the coarser complex. -/
theorem IsSubdivision.forall_notMem_walls (hCD : C.IsSubdivision D) {x : V}
    (hx : ∀ Q : C.walls, x ∉ (Q : Set V)) (P : D.walls) : x ∉ (P : Set V) := by
  intro hxP
  obtain ⟨Q, hQ, -, hxQ⟩ := hCD.exists_mem_walls_subset P.property hxP
  exact hx ⟨Q, hQ⟩ hxQ

/-- The chamber of a coarser complex containing a chamber of its subdivision. -/
def IsSubdivision.restrictChamber (hCD : C.IsSubdivision D) :
    Chamber (fun Q : C.walls => (Q : Set V)) → Chamber (fun P : D.walls => (P : Set V)) :=
  Continuous.connectedComponentsMap
    (f := fun x : {x : V | ∀ Q : C.walls, x ∉ (Q : Set V)} =>
      (⟨x.1, hCD.forall_notMem_walls x.2⟩ : {x : V | ∀ P : D.walls, x ∉ (P : Set V)}))
    (continuous_subtype_val.subtype_mk _)

/-- The restriction of the chamber of a point is the chamber of the same point. -/
@[simp]
theorem IsSubdivision.restrictChamber_mk (hCD : C.IsSubdivision D)
    (x : {x : V | ∀ Q : C.walls, x ∉ (Q : Set V)}) :
    hCD.restrictChamber (ConnectedComponents.mk x) =
      ConnectedComponents.mk ⟨x.1, hCD.forall_notMem_walls x.2⟩ :=
  Continuous.connectedComponentsMap_mk _ x

/-- A point of a chamber lies in the restricted chamber. -/
theorem IsSubdivision.mem_carrier_restrictChamber (hCD : C.IsSubdivision D)
    {c : Chamber (fun Q : C.walls => (Q : Set V))} {z : V} (hz : z ∈ c.carrier) :
    z ∈ (hCD.restrictChamber c).carrier := by
  obtain ⟨hzs, rfl⟩ := ConnectedComponents.mem_carrier_iff.mp hz
  exact ConnectedComponents.mem_carrier_iff.mpr ⟨hCD.forall_notMem_walls hzs,
    (hCD.restrictChamber_mk ⟨z, hzs⟩).symm⟩

/-- A chamber restricts to any chamber of the coarser complex sharing a point with it. -/
theorem IsSubdivision.restrictChamber_eq_of_mem_carrier (hCD : C.IsSubdivision D)
    {c : Chamber (fun Q : C.walls => (Q : Set V))}
    {c' : Chamber (fun P : D.walls => (P : Set V))} {z : V} (hz : z ∈ c.carrier)
    (hz' : z ∈ c'.carrier) : hCD.restrictChamber c = c' :=
  ConnectedComponents.eq_of_mem_carrier (hCD.mem_carrier_restrictChamber hz) hz'

/-- The restriction of the chamber of an allowed endpoint is the chamber of the same point,
viewed as an allowed endpoint of the coarser complex. -/
theorem IsSubdivision.restrictChamber_chamber (hCD : C.IsSubdivision D)
    {x : WallComplement (fun Q : C.walls => (Q : Set V))}
    {x' : WallComplement (fun P : D.walls => (P : Set V))} (hxx' : x.val = x'.val) :
    hCD.restrictChamber (chamber x) = chamber x' :=
  hCD.restrictChamber_eq_of_mem_carrier (val_mem_carrier_chamber x)
    (hxx' ▸ val_mem_carrier_chamber x')

/-- The positive chamber of a wall restricts to the positive chamber of the wall of the
coarser complex containing it, when the coorientations are positively proportional. -/
theorem IsSubdivision.restrictChamber_positiveChamber (hCD : C.IsSubdivision D)
    {Q : C.walls} {P : D.walls} (hQP : (Q : Set V) ⊆ P) {ν μ : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (Q : Set V)).direction)
    (hμ : LinearMap.ker μ = (affineSpan ℝ (P : Set V)).direction)
    (hνμ : ∃ c : ℝ, 0 < c ∧ ν = c • μ) :
    hCD.restrictChamber (C.positiveChamber Q ν hν) = D.positiveChamber P μ hμ := by
  have := h.finiteDimensional
  obtain ⟨c, hc, rfl⟩ := hνμ
  have hQC := C.mem_cells_of_mem_walls Q.property
  obtain ⟨q, hq⟩ := (C.nonempty _ hQC).intrinsicInterior (C.isConvexPolyhedron hQC).convex
  have hqP : q ∈ intrinsicInterior ℝ (P : Set V) :=
    Mei.intrinsicInterior_mono_of_affineSpan_eq hQP (affineSpan_eq_of_walls_subset Q P hQP) hq
  obtain ⟨v, hv⟩ := exists_normal_eq_one hμ
  have hv' : 0 < μ v := by rw [hv]; exact one_pos
  obtain ⟨t, ht, ht'⟩ := ((eventually_add_smul_mem_positiveChamber hν hq
    (by simpa using mul_pos hc hv')).and
      (eventually_add_smul_mem_positiveChamber hμ hqP hv')).exists
  exact hCD.restrictChamber_eq_of_mem_carrier ht ht'

/-- The negative chamber of a wall restricts to the negative chamber of the wall of the
coarser complex containing it, when the coorientations are positively proportional. -/
theorem IsSubdivision.restrictChamber_negativeChamber (hCD : C.IsSubdivision D)
    {Q : C.walls} {P : D.walls} (hQP : (Q : Set V) ⊆ P) {ν μ : V →ₗ[ℝ] ℝ}
    (hν : LinearMap.ker ν = (affineSpan ℝ (Q : Set V)).direction)
    (hμ : LinearMap.ker μ = (affineSpan ℝ (P : Set V)).direction)
    (hνμ : ∃ c : ℝ, 0 < c ∧ ν = c • μ) :
    hCD.restrictChamber (C.negativeChamber Q ν hν) = D.negativeChamber P μ hμ := by
  obtain ⟨c, hc, hcμ⟩ := hνμ
  have := hCD.restrictChamber_positiveChamber hQP (ν := -ν) (μ := -μ)
    (by rwa [LinearMap.ker_neg]) (by rwa [LinearMap.ker_neg]) ⟨c, hc, by rw [hcμ, smul_neg]⟩
  rwa [positiveChamber_neg hν, positiveChamber_neg hμ] at this

/-- Both chambers of a wall lying in no wall of the coarser complex restrict to the same
chamber. -/
theorem IsSubdivision.restrictChamber_positiveChamber_eq_negativeChamber
    (hCD : C.IsSubdivision D) {Q : C.walls} (hQ : ∀ P : D.walls, ¬(Q : Set V) ⊆ P)
    {ν : V →ₗ[ℝ] ℝ} (hν : LinearMap.ker ν = (affineSpan ℝ (Q : Set V)).direction) :
    hCD.restrictChamber (C.positiveChamber Q ν hν) =
      hCD.restrictChamber (C.negativeChamber Q ν hν) := by
  have := h.finiteDimensional
  have hQC := C.mem_cells_of_mem_walls Q.property
  obtain ⟨q, hq⟩ := (C.nonempty _ hQC).intrinsicInterior (C.isConvexPolyhedron hQC).convex
  -- The relative interior of `Q` misses every wall of `D`.
  have hqD : ∀ P : D.walls, q ∉ (P : Set V) := by
    intro P hqP
    obtain ⟨Q', hQ', hQ'P, hqQ'⟩ := hCD.exists_mem_walls_subset P.property hqP
    exact hQ P ((C.subset_of_mem_intrinsicInterior hQC (C.mem_cells_of_mem_walls hQ') hq
      hqQ').trans hQ'P)
  have hopen : IsOpen {z : V | ∀ P : D.walls, z ∉ (P : Set V)} := by
    have : {z : V | ∀ P : D.walls, z ∉ (P : Set V)} = (⋃ P : D.walls, (P : Set V))ᶜ := by
      ext z
      simp
    rw [this]
    exact (isClosed_iUnion_of_finite fun P =>
      (D.isConvexPolyhedron (D.mem_cells_of_mem_walls P.property)).isClosed).isOpen_compl
  obtain ⟨v, hv⟩ := exists_normal_eq_one hν
  have hv' : 0 < ν v := by rw [hv]; exact one_pos
  -- The chamber of `D` containing `q` is a neighborhood of `q`, so both short transverse rays
  -- from `q` eventually lie in it.
  have hcar : (ConnectedComponents.mk (⟨q, hqD⟩ : {x : V | ∀ P : D.walls, x ∉ (P : Set V)})).carrier
      ∈ 𝓝 q := by
    rw [ConnectedComponents.carrier_mk]
    exact connectedComponentIn_mem_nhds (hopen.mem_nhds hqD)
  have hadd : ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ (ConnectedComponents.mk
      (⟨q, hqD⟩ : {x : V | ∀ P : D.walls, x ∉ (P : Set V)})).carrier :=
    nhdsWithin_le_nhds
      (((by fun_prop : Continuous fun t : ℝ => q + t • v).tendsto' 0 q (by simp)).eventually
        hcar)
  have hsub : ∀ᶠ t : ℝ in 𝓝[>] 0, q - t • v ∈ (ConnectedComponents.mk
      (⟨q, hqD⟩ : {x : V | ∀ P : D.walls, x ∉ (P : Set V)})).carrier :=
    nhdsWithin_le_nhds
      (((by fun_prop : Continuous fun t : ℝ => q - t • v).tendsto' 0 q (by simp)).eventually
        hcar)
  obtain ⟨t, ⟨hpos, hpc⟩, hneg, hnc⟩ :=
    (((eventually_add_smul_mem_positiveChamber hν hq hv').and hadd).and
      ((eventually_sub_smul_mem_negativeChamber hν hq hv').and hsub)).exists
  exact (hCD.restrictChamber_eq_of_mem_carrier hpos hpc).trans
    (hCD.restrictChamber_eq_of_mem_carrier hneg hnc).symm

/-- The crossing source of a letter restricts to the crossing source of the letter of the
wall containing it. -/
theorem IsSubdivision.restrictChamber_crossingSource (hCD : C.IsSubdivision D)
    {ν : C.walls → V →ₗ[ℝ] ℝ} {μ : D.walls → V →ₗ[ℝ] ℝ}
    (hν : ∀ Q, LinearMap.ker (ν Q) = (affineSpan ℝ (Q : Set V)).direction)
    (hμ : ∀ P, LinearMap.ker (μ P) = (affineSpan ℝ (P : Set V)).direction)
    {l : C.walls × Bool} {P : D.walls} (hQP : (l.1 : Set V) ⊆ P)
    (hνμ : ∃ c : ℝ, 0 < c ∧ ν l.1 = c • μ P) :
    hCD.restrictChamber (C.crossingSource ν hν l) = D.crossingSource μ hμ (P, l.2) := by
  obtain ⟨Q, _ | _⟩ := l
  · exact hCD.restrictChamber_positiveChamber hQP (hν Q) (hμ P) hνμ
  · exact hCD.restrictChamber_negativeChamber hQP (hν Q) (hμ P) hνμ

/-- The crossing target of a letter restricts to the crossing target of the letter of the
wall containing it. -/
theorem IsSubdivision.restrictChamber_crossingTarget (hCD : C.IsSubdivision D)
    {ν : C.walls → V →ₗ[ℝ] ℝ} {μ : D.walls → V →ₗ[ℝ] ℝ}
    (hν : ∀ Q, LinearMap.ker (ν Q) = (affineSpan ℝ (Q : Set V)).direction)
    (hμ : ∀ P, LinearMap.ker (μ P) = (affineSpan ℝ (P : Set V)).direction)
    {l : C.walls × Bool} {P : D.walls} (hQP : (l.1 : Set V) ⊆ P)
    (hνμ : ∃ c : ℝ, 0 < c ∧ ν l.1 = c • μ P) :
    hCD.restrictChamber (C.crossingTarget ν hν l) = D.crossingTarget μ hμ (P, l.2) := by
  obtain ⟨Q, _ | _⟩ := l
  · exact hCD.restrictChamber_negativeChamber hQP (hν Q) (hμ P) hνμ
  · exact hCD.restrictChamber_positiveChamber hQP (hν Q) (hμ P) hνμ

/-- A letter on a wall lying in no wall of the coarser complex starts and ends in chambers
with the same restriction. -/
theorem IsSubdivision.restrictChamber_crossingSource_eq_crossingTarget (hCD : C.IsSubdivision D)
    {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : ∀ Q, LinearMap.ker (ν Q) = (affineSpan ℝ (Q : Set V)).direction)
    {l : C.walls × Bool} (hl : ∀ P : D.walls, ¬(l.1 : Set V) ⊆ P) :
    hCD.restrictChamber (C.crossingSource ν hν l) =
      hCD.restrictChamber (C.crossingTarget ν hν l) := by
  obtain ⟨Q, _ | _⟩ := l
  · exact hCD.restrictChamber_positiveChamber_eq_negativeChamber hl (hν Q)
  · exact (hCD.restrictChamber_positiveChamber_eq_negativeChamber hl (hν Q)).symm

/-- The letter of the wall of `D` containing the wall of a crossing letter of `C`, with the
same sign, if any. -/
def coarsenLetter (D : FinitePolyhedralComplex h) (l : C.walls × Bool) :
    Option (D.walls × Bool) :=
  (coarsenCrossing (D := D) (l.1, (0 : ℝ))).map fun b => (b.1, l.2)

/-- A letter coarsens to a letter of a wall containing its wall, with the same sign. -/
@[simp]
theorem coarsenLetter_eq_some {l : C.walls × Bool} {m : D.walls × Bool} :
    coarsenLetter D l = some m ↔ (l.1 : Set V) ⊆ m.1 ∧ l.2 = m.2 := by
  rw [coarsenLetter, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨P, t⟩, hb, rfl⟩
    exact ⟨(coarsenCrossing_eq_some.mp hb).1, rfl⟩
  · rintro ⟨hQP, hs⟩
    exact ⟨(m.1, 0), coarsenCrossing_eq_some.mpr ⟨hQP, rfl⟩, Prod.ext rfl hs⟩

/-- A letter coarsens to nothing exactly when its wall lies in no wall of `D`. -/
@[simp]
theorem coarsenLetter_eq_none {l : C.walls × Bool} :
    coarsenLetter D l = none ↔ ∀ P : D.walls, ¬(l.1 : Set V) ⊆ P := by
  cases hl : coarsenLetter D l with
  | none =>
    refine iff_of_true rfl fun P hP => ?_
    have := (coarsenLetter_eq_some (D := D) (l := l) (m := (P, l.2))).mpr ⟨hP, rfl⟩
    rw [hl] at this
    exact absurd this (by simp)
  | some m =>
    refine iff_of_false (by simp) fun hall => ?_
    exact hall m.1 (coarsenLetter_eq_some.mp hl).1

variable {x y : WallComplement (fun P : C.walls => (P : Set V))}
  {x' y' : WallComplement (fun P : D.walls => (P : Set V))}

/-- For a segment admissible for both complexes, the crossing letters for `D` are the
coarsened crossing letters for `C`, when coorientations of contained walls are positively
proportional. -/
theorem segmentCrossingLetters_coarsen (hCD : C.IsSubdivision D)
    (ν : C.walls → V →ₗ[ℝ] ℝ) (μ : D.walls → V →ₗ[ℝ] ℝ)
    (hνμ : ∀ (Q : C.walls) (P : D.walls), (Q : Set V) ⊆ P → ∃ c : ℝ, 0 < c ∧ ν Q = c • μ P)
    (e : x ⟶ y) (e' : x' ⟶ y') (hx : x.val = x'.val) (hy : y.val = y'.val) :
    D.segmentCrossingLetters μ e' =
      (C.segmentCrossingLetters ν e).filterMap (coarsenLetter D) := by
  have hv : y'.val - x'.val = y.val - x.val := by rw [hx, hy]
  rw [segmentCrossingLetters_def, segmentCrossingLetters_def,
    orderedCrossings_coarsen hCD e e' hx hy, List.map_filterMap, List.filterMap_map]
  refine List.filterMap_congr fun a _ => ?_
  rw [Function.comp_apply]
  cases hf : coarsenCrossing (D := D) a with
  | none =>
    have hQ : ∀ P : D.walls, ¬(a.1 : Set V) ⊆ P := fun P hP => by
      simpa [hf] using (coarsenCrossing_eq_some (b := (P, a.2))).mpr ⟨hP, rfl⟩
    exact (coarsenLetter_eq_none.mpr hQ).symm
  | some b =>
    obtain ⟨hQP, -⟩ := coarsenCrossing_eq_some.mp hf
    obtain ⟨c, hc, hcν⟩ := hνμ a.1 b.1 hQP
    have hsign : (0 < μ b.1 (y'.val - x'.val)) ↔ 0 < ν a.1 (y.val - x.val) := by
      rw [hv, hcν, LinearMap.smul_apply, smul_eq_mul, mul_pos_iff_of_pos_left hc]
    simp only [Option.map_some, hsign]
    exact (coarsenLetter_eq_some.mpr ⟨hQP, rfl⟩ : coarsenLetter D (a.1, _) = _).symm

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C D : Mei.FinitePolyhedralComplex h}

open Mei Mei.FinitePolyhedralComplex

/-- For a polygonal path admissible for both a complex and a complex it subdivides, the
crossing letters for the coarser complex are the coarsened crossing letters for the finer
one, when coorientations of contained walls are positively proportional. -/
theorem crossingLetters_coarsen (hCD : C.IsSubdivision D) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (μ : D.walls → V →ₗ[ℝ] ℝ)
    (hνμ : ∀ (Q : C.walls) (P : D.walls), (Q : Set V) ⊆ P → ∃ c : ℝ, 0 < c ∧ ν Q = c • μ P)
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    {x' y' : WallComplement (fun P : D.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    q.crossingLetters μ = (p.crossingLetters ν).filterMap (coarsenLetter D) := by
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
      have hz : z.val = z'.val := (endpoints_val_eq_of_vertices_eq p q hpq).2
      rw [crossingLetters_cons, crossingLetters_cons, List.filterMap_append, ih q hpq,
        segmentCrossingLetters_coarsen hCD ν μ hνμ e e' hz (by simpa using hw)]

end Quiver.Path
