/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Plane.Basic
public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Pairing

/-!
# The coboundary of a segment in the plane

The closed segment from `p₀ = (0, 0)` to `p₁ = (1, 0)`, with conormal orientation `+dy`, is a
cell of codimension one in `ℝ × ℝ`. It has exactly two boundary facets, its endpoints, carrying
the orientations `+dx ∧ dy` at `p₀` and `-dx ∧ dy` at `p₁`: contracting `dx ∧ dy` with the
outward vector `-∂ₓ` at `p₀` gives `-dy`, and with `+∂ₓ` at `p₁` gives `+dy`. Hence the
coboundary of the segment with coefficient `c` is `(p₀, +dx ∧ dy, c) + (p₁, -dx ∧ dy, c)`.

A small positively oriented triangle around a point meets only the point cell it surrounds, and
the intersection index there is the sign of its edge frame on `dx ∧ dy`, which is `+1`. The
coboundary of the segment therefore pairs with the triangle around `p₀` to give `c`, and with
the triangle around `p₁` to give `-c`. This holds for every presentation of the coboundary
cochain by cells transverse to the triangle.
-/

public section

open Set Module

namespace Mei

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]
  {h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))}

namespace OrientedCell

variable (h) in
/-- The closed segment from `(0, 0)` to `(1, 0)`, with the conormal orientation `+dy`. -/
noncomputable def unitSegment : OrientedCell h 1 where
  carrier := segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0)
  rational := Plane.isRationalNormalPolyhedron_segment h
  nonempty := ⟨(0, 0), left_mem_segment _ _ _⟩
  finrank_direction_add := by
    rw [direction_affineSpan, Plane.vectorSpan_eq_horizontal
      (fun _ hp => (Plane.mem_segment_iff.mp hp).1) (left_mem_segment _ _ _)
      (right_mem_segment _ _ _), Plane.finrank_horizontal]
    simp
  orientation := rayOfNeZero ℝ Plane.dy Plane.dy_ne_zero
  isConormal := by
    rw [direction_affineSpan, Plane.vectorSpan_eq_horizontal
      (fun _ hp => (Plane.mem_segment_iff.mp hp).1) (left_mem_segment _ _ _)
      (right_mem_segment _ _ _)]
    exact (Module.Ray.isConormal_rayOfNeZero_iff _).mpr Plane.dy_mem_conormalForms

@[simp]
theorem unitSegment_carrier :
    (unitSegment h).carrier = segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0) := (rfl)

@[simp]
theorem unitSegment_orientation :
    (unitSegment h).orientation = rayOfNeZero ℝ Plane.dy Plane.dy_ne_zero := (rfl)

variable (h) in
/-- The point `x` of the plane as a cell of codimension two, oriented by `+dx ∧ dy`. -/
noncomputable def planePoint (x : ℝ × ℝ) : OrientedCell h 2 where
  carrier := {x}
  rational := isRationalNormalPolyhedron_singleton h x
  nonempty := Set.singleton_nonempty x
  finrank_direction_add := by
    rw [direction_affineSpan, vectorSpan_singleton]
    simp
  orientation := rayOfNeZero ℝ Plane.area Plane.area_ne_zero
  isConormal := by
    rw [direction_affineSpan, vectorSpan_singleton]
    exact (Module.Ray.isConormal_rayOfNeZero_iff _).mpr (by simp)

@[simp]
theorem planePoint_carrier (x : ℝ × ℝ) : (planePoint h x).carrier = {x} := (rfl)

@[simp]
theorem planePoint_orientation (x : ℝ × ℝ) :
    (planePoint h x).orientation = rayOfNeZero ℝ Plane.area Plane.area_ne_zero := (rfl)

/-- A point cell has the zero direction. -/
theorem direction_affineSpan_planePoint (x : ℝ × ℝ) :
    (affineSpan ℝ (planePoint h x).carrier).direction = ⊥ := by
  rw [direction_affineSpan, planePoint_carrier, vectorSpan_singleton]

/-- A reversed point cell has the zero direction. -/
theorem direction_affineSpan_planePoint_reverse (x : ℝ × ℝ) :
    (affineSpan ℝ (planePoint h x).reverse.carrier).direction = ⊥ := by
  rw [reverse_carrier, direction_affineSpan_planePoint]

/-- The exposed sets of the unit segment with a span of codimension one are its endpoints,
the supports of the cells `planePoint h (0, 0)` and `(planePoint h (1, 0)).reverse`. -/
private theorem eq_or_eq_of_isExposed_unitSegment {F : Set (ℝ × ℝ)}
    (hF : IsExposed ℝ (unitSegment h).carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ (unitSegment h).carrier)) :
    F = (planePoint h (0, 0)).carrier ∨ F = (planePoint h (1, 0)).reverse.carrier := by
  simp only [planePoint_carrier, reverse_carrier]
  rw [unitSegment_carrier, Plane.vectorSpan_eq_horizontal
    (fun _ hp => (Plane.mem_segment_iff.mp hp).1) (left_mem_segment _ _ _)
    (right_mem_segment _ _ _), Plane.finrank_horizontal] at hdim
  have hsub : F.Subsingleton := by
    rw [← vectorSpan_eq_bot_iff_subsingleton ℝ]
    exact Submodule.finrank_eq_zero.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have hFx : F = {x} := hsub.eq_singleton_of_mem hx
  obtain ⟨hx2, hx0, hx1⟩ := Plane.mem_segment_iff.mp (hF.subset hx)
  rcases hx0.eq_or_lt with h0 | h0
  · left
    rw [hFx]
    congr 1
    ext <;> simp [hx2, ← h0]
  rcases hx1.eq_or_lt with h1 | h1
  · right
    rw [hFx]
    congr 1
    ext <;> simp [hx2, h1]
  exfalso
  have hopen : x ∈ openSegment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0) := by
    refine ⟨1 - x.1, x.1, by linarith, h0, by ring, ?_⟩
    ext <;> simp [hx2]
  have := hF.isExtreme.left_mem_of_mem_openSegment (left_mem_segment _ _ _)
    (right_mem_segment _ _ _) hx hopen
  rw [hFx] at this
  have := congrArg Prod.fst (Set.mem_singleton_iff.mp this)
  simp at this
  linarith

/-- The point `p₀ = (0, 0)` with orientation `+dx ∧ dy` is the signed boundary facet of the unit
segment at its left end: contracting `dx ∧ dy` with the outward vector `-∂ₓ` gives `-dy`. -/
private theorem planePoint_zero_eq_boundaryFacet
    (hF : IsExposed ℝ (unitSegment h).carrier (planePoint h (0, 0)).carrier)
    (hne : (planePoint h (0, 0)).carrier.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ (planePoint h (0, 0)).carrier) + 1 =
      finrank ℝ (vectorSpan ℝ (unitSegment h).carrier)) :
    planePoint h (0, 0) = (unitSegment h).boundaryFacet hF hne hdim := by
  have hx : ((1, 0) : ℝ × ℝ) ∈ (unitSegment h).carrier := right_mem_segment _ _ _
  have hy : ((0, 0) : ℝ × ℝ) ∈ (planePoint h (0, 0)).carrier := rfl
  have hxF : ((1, 0) : ℝ × ℝ) ∉ (planePoint h (0, 0)).carrier := by simp
  refine ((unitSegment h).eq_boundaryFacet_iff hF hne hdim _ rfl
    ⟨(0, 0) - (1, 0), vsub_mem_vectorSpan ℝ (hF.subset hy) hx⟩ ?_
    ((hF.outwardNormal_apply_pos_iff hne hdim hx hy).mpr hxF)).mpr ?_
  · rw [direction_affineSpan_planePoint]
    simp
  · simp only [planePoint_orientation, unitSegment_orientation, Module.Ray.contract_rayOfNeZero,
      neg_rayOfNeZero]
    refine (ray_eq_iff _ _).mpr ?_
    have : Plane.area.curryLeft ((0, 0) - (1, 0)) = -Plane.dy := by
      ext w
      simp [Plane.area_apply]
    rw [this]
    exact SameRay.refl _

/-- The point `p₁ = (1, 0)` with orientation `-dx ∧ dy` is the signed boundary facet of the unit
segment at its right end: contracting `-dx ∧ dy` with the outward vector `+∂ₓ` gives `-dy`. -/
private theorem planePoint_one_reverse_eq_boundaryFacet
    (hF : IsExposed ℝ (unitSegment h).carrier (planePoint h (1, 0)).reverse.carrier)
    (hne : (planePoint h (1, 0)).reverse.carrier.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ (planePoint h (1, 0)).reverse.carrier) + 1 =
      finrank ℝ (vectorSpan ℝ (unitSegment h).carrier)) :
    (planePoint h (1, 0)).reverse = (unitSegment h).boundaryFacet hF hne hdim := by
  have hx : ((0, 0) : ℝ × ℝ) ∈ (unitSegment h).carrier := left_mem_segment _ _ _
  have hy : ((1, 0) : ℝ × ℝ) ∈ (planePoint h (1, 0)).reverse.carrier := by simp
  have hxF : ((0, 0) : ℝ × ℝ) ∉ (planePoint h (1, 0)).reverse.carrier := by simp
  refine ((unitSegment h).eq_boundaryFacet_iff hF hne hdim _ rfl
    ⟨(1, 0) - (0, 0), vsub_mem_vectorSpan ℝ (hF.subset hy) hx⟩ ?_
    ((hF.outwardNormal_apply_pos_iff hne hdim hx hy).mpr hxF)).mpr ?_
  · rw [direction_affineSpan_planePoint_reverse]
    simp
  · simp only [reverse_orientation, planePoint_orientation, unitSegment_orientation,
      neg_rayOfNeZero, Module.Ray.contract_rayOfNeZero]
    refine (ray_eq_iff _ _).mpr ?_
    have : (-Plane.area).curryLeft ((1, 0) - (0, 0)) = -Plane.dy := by
      ext w
      simp [Plane.area_apply]
    rw [this]
    exact SameRay.refl _

/-- The left endpoint is an exposed set of the unit segment. -/
private theorem isExposed_unitSegment_zero :
    IsExposed ℝ (unitSegment h).carrier (planePoint h (0, 0)).carrier := by
  intro _
  refine ⟨-FinitePolyhedralComplex.axisRow false, ?_⟩
  ext x
  simp only [planePoint_carrier, unitSegment_carrier, mem_singleton_iff, mem_ofPred_eq,
    Plane.mem_segment_iff, neg_apply, FinitePolyhedralComplex.axisRow_false_apply,
    neg_le_neg_iff]
  refine ⟨?_, fun ⟨⟨hx2, hx0, _⟩, hx⟩ => ?_⟩
  · rintro rfl
    exact ⟨⟨rfl, le_rfl, zero_le_one⟩, fun y hy => hy.2.1⟩
  · have := hx (0, 0) ⟨rfl, le_rfl, zero_le_one⟩
    ext <;> simp at this ⊢ <;> linarith

/-- The right endpoint is an exposed set of the unit segment. -/
private theorem isExposed_unitSegment_one :
    IsExposed ℝ (unitSegment h).carrier (planePoint h (1, 0)).reverse.carrier := by
  intro _
  refine ⟨FinitePolyhedralComplex.axisRow false, ?_⟩
  ext x
  simp only [reverse_carrier, planePoint_carrier, unitSegment_carrier, mem_singleton_iff,
    mem_ofPred_eq, Plane.mem_segment_iff, FinitePolyhedralComplex.axisRow_false_apply]
  refine ⟨?_, fun ⟨⟨hx2, _, hx1⟩, hx⟩ => ?_⟩
  · rintro rfl
    exact ⟨⟨rfl, zero_le_one, le_rfl⟩, fun y hy => hy.2.2⟩
  · have := hx (1, 0) ⟨rfl, zero_le_one, le_rfl⟩
    ext <;> simp at this ⊢ <;> linarith

/-- A point has dimension one less than the unit segment. -/
private theorem finrank_vectorSpan_add_one_of_carrier_eq_singleton
    {τ : OrientedCell h 2} {x : ℝ × ℝ}
    (hτ : τ.carrier = {x}) :
    finrank ℝ (vectorSpan ℝ τ.carrier) + 1 = finrank ℝ (vectorSpan ℝ (unitSegment h).carrier) := by
  rw [hτ, unitSegment_carrier, Plane.vectorSpan_eq_horizontal
    (fun _ hp => (Plane.mem_segment_iff.mp hp).1) (left_mem_segment _ _ _)
    (right_mem_segment _ _ _), vectorSpan_singleton, Plane.finrank_horizontal]
  simp

open Classical in
/-- The unit segment has exactly two signed boundary facets: its endpoints, with orientations
`+dx ∧ dy` at `(0, 0)` and `-dx ∧ dy` at `(1, 0)`. -/
theorem unitSegment_boundaryFacets :
    (unitSegment h).boundaryFacets =
      {(planePoint h (0, 0) : OrientedCell h (1 + 1)), (planePoint h (1, 0)).reverse} := by
  ext τ
  rw [mem_boundaryFacets, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨F, hF, hne, hdim, rfl⟩
    rcases eq_or_eq_of_isExposed_unitSegment hF hne hdim with rfl | rfl
    · exact Or.inl (planePoint_zero_eq_boundaryFacet hF hne hdim).symm
    · exact Or.inr (planePoint_one_reverse_eq_boundaryFacet hF hne hdim).symm
  · have h0 := finrank_vectorSpan_add_one_of_carrier_eq_singleton
      (planePoint_carrier (h := h) (0, 0))
    have h1 := finrank_vectorSpan_add_one_of_carrier_eq_singleton
      (τ := (planePoint h (1, 0)).reverse) (x := (1, 0)) (by simp)
    rintro (rfl | rfl)
    · exact ⟨_, isExposed_unitSegment_zero, (planePoint h (0, 0)).nonempty, h0,
        planePoint_zero_eq_boundaryFacet isExposed_unitSegment_zero
          (planePoint h (0, 0)).nonempty h0⟩
    · exact ⟨_, isExposed_unitSegment_one, (planePoint h (1, 0)).reverse.nonempty, h1,
        planePoint_one_reverse_eq_boundaryFacet isExposed_unitSegment_one
          (planePoint h (1, 0)).reverse.nonempty h1⟩

open Classical in
/-- The coboundary of the unit segment with coefficient `c` is
`(p₀, +dx ∧ dy, c) + (p₁, -dx ∧ dy, c)` for `p₀ = (0, 0)` and `p₁ = (1, 0)`. -/
theorem unitSegment_cellCoboundary (c : E) :
    (unitSegment h).cellCoboundary (R := R) c =
      PolyhedralCochain.mk (planePoint h (0, 0)) c +
        PolyhedralCochain.mk (planePoint h (1, 0)).reverse c := by
  rw [cellCoboundary_apply, unitSegment_boundaryFacets, Finset.sum_pair]
  intro heq
  simpa using congrArg OrientedCell.carrier heq

end OrientedCell

namespace Plane

/-- The small positively oriented triangle of half-width `1/2` around `p`, with vertices
`p + (-1/2, -1/2)`, `p + (1/2, -1/2)`, `p + (0, 1/2)`. -/
noncomputable def smallTriangle (p : ℝ × ℝ) : Fin 3 → ℝ × ℝ :=
  ![p + (-1 / 2, -1 / 2), p + (1 / 2, -1 / 2), p + (0, 1 / 2)]

/-- A point lies in the triangle around it: it is the barycenter with weights `1/4, 1/4, 1/2`. -/
theorem mem_convexHull_smallTriangle (p : ℝ × ℝ) :
    p ∈ convexHull ℝ (range (smallTriangle p)) := by
  have hmem := (convex_convexHull ℝ (range (smallTriangle p))).sum_mem
    (t := Finset.univ) (w := ![1 / 4, 1 / 4, 1 / 2]) (z := smallTriangle p)
    (fun i _ => by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_three]; norm_num)
    (fun i _ => subset_convexHull ℝ _ (mem_range_self i))
  convert hmem using 1
  ext <;> simp [Fin.sum_univ_three, smallTriangle] <;> ring

/-- The triangle around `p` lies within horizontal distance `1/2` of `p`. -/
theorem fst_mem_Icc_of_mem_convexHull_smallTriangle (p : ℝ × ℝ) {q : ℝ × ℝ}
    (hq : q ∈ convexHull ℝ (range (smallTriangle p))) :
    q.1 ∈ Icc (p.1 - 1 / 2) (p.1 + 1 / 2) := by
  have hsub : convexHull ℝ (range (smallTriangle p)) ⊆
      (LinearMap.fst ℝ ℝ ℝ) ⁻¹' Icc (p.1 - 1 / 2) (p.1 + 1 / 2) := by
    refine convexHull_min ?_ ((convex_Icc _ _).linear_preimage _)
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> refine ⟨?_, ?_⟩ <;> simp [smallTriangle] <;> linarith
  exact hsub hq

/-- The triangle around `p` is positively oriented: its edge frame has area `1`. -/
theorem area_smallTriangle_frame (p : ℝ × ℝ) :
    area (fun j : Fin 2 => smallTriangle p j.succ - smallTriangle p 0) = 1 := by
  simp [area_apply, smallTriangle]
  norm_num

/-- The edge frame of the triangle around `p` is linearly independent. -/
theorem linearIndependent_smallTriangle_frame (p : ℝ × ℝ) :
    LinearIndependent ℝ (fun j : Fin 2 => smallTriangle p j.succ - smallTriangle p 0) := by
  by_contra hdep
  have := area.map_linearDependent _ hdep
  rw [area_smallTriangle_frame] at this
  exact one_ne_zero this

end Plane

namespace OrientedCell

/-- The point cell at `x` has intersection index `+1` with a triangle whose edge frame has
positive area and whose hull contains `x`. -/
theorem planePoint_intersectionIndex_of_mem (x : ℝ × ℝ) {T : Fin 3 → ℝ × ℝ}
    (hx : x ∈ convexHull ℝ (range T)) :
    (planePoint h x).intersectionIndex T =
      (SignType.sign (Plane.area fun j : Fin 2 => T j.succ - T 0) : ℤ) := by
  rw [intersectionIndex_of_nonempty ⟨x, hx, rfl⟩]
  simp

/-- A point cell missing a test triangle has intersection index zero. -/
theorem planePoint_intersectionIndex_of_notMem (x : ℝ × ℝ) {T : Fin 3 → ℝ × ℝ}
    (hx : x ∉ convexHull ℝ (range T)) : (planePoint h x).intersectionIndex T = 0 := by
  apply intersectionIndex_of_disjoint
  simpa using hx

/-- The positively oriented triangle around `p` has index `+1` at the point cell at `p`. -/
theorem planePoint_intersectionIndex_smallTriangle_self (p : ℝ × ℝ) :
    (planePoint h p).intersectionIndex (Plane.smallTriangle p) = 1 := by
  rw [planePoint_intersectionIndex_of_mem p (Plane.mem_convexHull_smallTriangle p),
    Plane.area_smallTriangle_frame]
  simp

/-- The triangle around `p` misses the points of the plane to the right of it. -/
theorem planePoint_intersectionIndex_smallTriangle_of_lt {p q : ℝ × ℝ} (hpq : p.1 + 1 / 2 < q.1) :
    (planePoint h q).intersectionIndex (Plane.smallTriangle p) = 0 := by
  refine planePoint_intersectionIndex_of_notMem _ fun hq => ?_
  linarith [(Plane.fst_mem_Icc_of_mem_convexHull_smallTriangle p hq).2]

/-- The triangle around `p` misses the points of the plane to the left of it. -/
theorem planePoint_intersectionIndex_smallTriangle_of_gt {p q : ℝ × ℝ} (hpq : q.1 < p.1 - 1 / 2) :
    (planePoint h q).intersectionIndex (Plane.smallTriangle p) = 0 := by
  refine planePoint_intersectionIndex_of_notMem _ fun hq => ?_
  linarith [(Plane.fst_mem_Icc_of_mem_convexHull_smallTriangle p hq).1]

/-- The triangle around `p` is transverse to the point cell at `p`. -/
theorem isTransverse_planePoint_smallTriangle_self (p : ℝ × ℝ) :
    (planePoint h p).IsTransverse (Plane.smallTriangle p) where
  disjoint_intrinsicFrontier := by simp
  linearIndependent _ := by
    rw [direction_affineSpan_planePoint]
    exact (Plane.linearIndependent_smallTriangle_frame p).map' _ (by simp)

/-- The triangle around `p` is transverse to point cells that it misses. -/
theorem isTransverse_planePoint_smallTriangle_of_notMem {p q : ℝ × ℝ}
    (hq : q ∉ convexHull ℝ (range (Plane.smallTriangle p))) :
    (planePoint h q).IsTransverse (Plane.smallTriangle p) :=
  isTransverse_of_disjoint _ (by simpa using hq)

open Classical in
/-- The triangle around `p₀ = (0, 0)` is transverse to both boundary facets of the unit
segment. -/
theorem isTransverse_smallTriangle_zero_of_mem_boundaryFacets {τ : OrientedCell h (1 + 1)}
    (hτ : τ ∈ (unitSegment h).boundaryFacets) : τ.IsTransverse (Plane.smallTriangle (0, 0)) := by
  rw [unitSegment_boundaryFacets, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl
  · exact isTransverse_planePoint_smallTriangle_self _
  · rw [isTransverse_reverse_iff]
    refine isTransverse_planePoint_smallTriangle_of_notMem fun hq => ?_
    linarith [(Plane.fst_mem_Icc_of_mem_convexHull_smallTriangle _ hq).2]

open Classical in
/-- The triangle around `p₁ = (1, 0)` is transverse to both boundary facets of the unit
segment. -/
theorem isTransverse_smallTriangle_one_of_mem_boundaryFacets {τ : OrientedCell h (1 + 1)}
    (hτ : τ ∈ (unitSegment h).boundaryFacets) : τ.IsTransverse (Plane.smallTriangle (1, 0)) := by
  rw [unitSegment_boundaryFacets, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl
  · refine isTransverse_planePoint_smallTriangle_of_notMem fun hq => ?_
    linarith [(Plane.fst_mem_Icc_of_mem_convexHull_smallTriangle _ hq).1]
  · rw [isTransverse_reverse_iff]
    exact isTransverse_planePoint_smallTriangle_self _

end OrientedCell

namespace PolyhedralCochain

open OrientedCell

open Classical in
/-- The coboundary of the unit segment with coefficient `c` pairs with the small positively
oriented triangle around `p₀ = (0, 0)` to give `c`, for the signed boundary presentation. -/
theorem intersectionPairing_coboundaryPresentation_unitSegment_zero (c : E) :
    intersectionPairing (R := R) (Plane.smallTriangle (0, 0))
      (coboundaryPresentation (R := R) (Finsupp.single (unitSegment h) c)) = c := by
  rw [coboundaryPresentation_single, unitSegment_boundaryFacets, map_sum, Finset.sum_pair,
    intersectionPairing_single, intersectionPairing_single, intersectionIndex_reverse,
    planePoint_intersectionIndex_smallTriangle_self,
    planePoint_intersectionIndex_smallTriangle_of_lt (h := h) (q := (1, 0)) (by norm_num)]
  · simp
  · intro heq
    simpa using congrArg OrientedCell.carrier heq

open Classical in
/-- The coboundary of the unit segment with coefficient `c` pairs with the small positively
oriented triangle around `p₁ = (1, 0)` to give `-c`, for the signed boundary presentation. -/
theorem intersectionPairing_coboundaryPresentation_unitSegment_one (c : E) :
    intersectionPairing (R := R) (Plane.smallTriangle (1, 0))
      (coboundaryPresentation (R := R) (Finsupp.single (unitSegment h) c)) = -c := by
  rw [coboundaryPresentation_single, unitSegment_boundaryFacets, map_sum, Finset.sum_pair,
    intersectionPairing_single, intersectionPairing_single, intersectionIndex_reverse,
    planePoint_intersectionIndex_smallTriangle_self,
    planePoint_intersectionIndex_smallTriangle_of_gt (h := h) (q := (0, 0)) (by norm_num)]
  · simp
  · intro heq
    simpa using congrArg OrientedCell.carrier heq

open Classical in
/-- Every presentation of the coboundary of the unit segment by cells transverse to the triangle
around `p₀` pairs with it to give `c`. -/
theorem intersectionPairing_eq_of_ofFinsupp_eq_coboundary_unitSegment_zero (c : E)
    {y : OrientedCell h (1 + 1) →₀ E}
    (hy : ofFinsupp (R := R) y = coboundaryOfFinsupp (Finsupp.single (unitSegment h) c))
    (hT : ∀ τ ∈ y.support, τ.IsTransverse (Plane.smallTriangle (0, 0))) :
    intersectionPairing (R := R) (Plane.smallTriangle (0, 0)) y = c := by
  rw [← intersectionPairing_coboundaryPresentation_unitSegment_zero (R := R) (h := h) c]
  refine intersectionPairing_eq_of_ofFinsupp_eq
    (by rw [hy, ofFinsupp_coboundaryPresentation]) hT fun τ hτ => ?_
  obtain ⟨σ, hσ, hτσ⟩ := Finset.mem_biUnion.mp
    (support_coboundaryPresentation_subset (R := R) (Finsupp.single (unitSegment h) c) hτ)
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hσ)] at hτσ
  exact isTransverse_smallTriangle_zero_of_mem_boundaryFacets hτσ

open Classical in
/-- Every presentation of the coboundary of the unit segment by cells transverse to the triangle
around `p₁` pairs with it to give `-c`. -/
theorem intersectionPairing_eq_neg_of_ofFinsupp_eq_coboundary_unitSegment_one (c : E)
    {y : OrientedCell h (1 + 1) →₀ E}
    (hy : ofFinsupp (R := R) y = coboundaryOfFinsupp (Finsupp.single (unitSegment h) c))
    (hT : ∀ τ ∈ y.support, τ.IsTransverse (Plane.smallTriangle (1, 0))) :
    intersectionPairing (R := R) (Plane.smallTriangle (1, 0)) y = -c := by
  rw [← intersectionPairing_coboundaryPresentation_unitSegment_one (R := R) (h := h) c]
  refine intersectionPairing_eq_of_ofFinsupp_eq
    (by rw [hy, ofFinsupp_coboundaryPresentation]) hT fun τ hτ => ?_
  obtain ⟨σ, hσ, hτσ⟩ := Finset.mem_biUnion.mp
    (support_coboundaryPresentation_subset (R := R) (Finsupp.single (unitSegment h) c) hτ)
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hσ)] at hτσ
  exact isTransverse_smallTriangle_one_of_mem_boundaryFacets hτσ

end PolyhedralCochain

end Mei
