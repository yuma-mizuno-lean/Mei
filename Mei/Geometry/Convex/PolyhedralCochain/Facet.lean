/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Face
public import Mei.Geometry.Convex.Polyhedron.Face.Cut
public import Mei.Analysis.Convex.Exposed.Orientation
public import Mei.Analysis.Convex.Exposed.Separation

/-!
# Oriented boundary facets

Every nonempty exposed facet of an oriented rational-normal cell has a canonical
boundary orientation. Contracting it by any outward tangent vector gives the
negative of the parent's conormal orientation. Equivalently, append an outward
conormal to the parent's conormal frame and multiply by `(-1)^(k+1)` for a
parent of codimension `k`. This is the signed generator needed for the
polyhedral coboundary.

The construction uses `IsExposed.facetOrientation`, which extends the outward
covector and forms the signed wedge with the parent's conormal orientation.
The contraction characterization proves independence of the outward vector
and determines the oriented facet uniquely. `boundaryFacet_orientation` identifies
it with the general ordered-field construction `IsExposed.facetOrientation`.
Equally oriented cells induce opposite boundary orientations on a common facet
exposed by opposite functionals, as computed by
`IsExposed.facetOrientation_eq_neg_wedgeCovector`. In particular, the common
slice of a hyperplane cut occurs with opposite orientations in both facet families.
No inner product, boundedness,
salience or full-dimensionality is assumed.

For a half-space cut retaining the cell's codimension,
`carrier_eq_cut_zero_or_inter_boundaryFacet` classifies the supports of every signed facet
of the cut piece: each is the cutting section or the restriction of an original signed
facet. It uses the exposed-face classification `TauCeti.IsConvexPolyhedron.facet_cut_iff`.
-/

public section

open Module Set

noncomputable section

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- The signed boundary facet of an oriented cell. Its contraction by an outward
tangent vector is the negative of the parent's orientation. -/
def boundaryFacet (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    OrientedCell h (k + 1) := by
  have := h.finiteDimensional
  have ho : σ.orientation.IsConormal (vectorSpan ℝ σ.carrier) := by
    simpa only [direction_affineSpan] using σ.isConormal
  have hconv : Convex ℝ σ.carrier := by
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
    exact hP ▸ P.convex
  exact
    { carrier := F
      rational := hF.isExtreme.isRationalNormalPolyhedron σ.rational
        (hF.convex hconv)
      nonempty := hne
      finrank_direction_add := by
        have hp := σ.finrank_direction_add
        rw [direction_affineSpan] at hp ⊢
        omega
      orientation := hF.facetOrientation hne hdim σ.orientation ho
      isConormal := by
        rw [direction_affineSpan]
        exact hF.isConormal_facetOrientation hne hdim σ.orientation ho }

/-- The boundary facet has exactly the prescribed support. -/
@[simp]
theorem boundaryFacet_carrier (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    (σ.boundaryFacet hF hne hdim).carrier = F :=
  (rfl)

/-- Every outward tangent vector computes the boundary orientation by contraction;
neither its length nor a particular exposing inequality is part of the result. -/
theorem contract_boundaryFacet (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (v : vectorSpan ℝ σ.carrier)
    (hv : (v : V) ∉ (affineSpan ℝ (σ.boundaryFacet hF hne hdim).carrier).direction) :
    letI := h.finiteDimensional
    0 < (hF.outwardNormal hne hdim).someVector v →
    (σ.boundaryFacet hF hne hdim).orientation.contract
      (σ.boundaryFacet hF hne hdim).isConormal
      (σ.boundaryFacet hF hne hdim).finrank_quotient_direction v hv = -σ.orientation := by
  have := h.finiteDimensional
  intro hpos
  have hk := (σ.boundaryFacet hF hne hdim).finrank_quotient_direction
  rw [boundaryFacet_carrier, direction_affineSpan] at hk
  simpa only [boundaryFacet, direction_affineSpan] using
    hF.contract_facetOrientation hne hdim σ.orientation
      (by simpa only [direction_affineSpan] using σ.isConormal) hk v hpos

/-- Among cells with the prescribed support, a single outward contraction
characterizes the signed boundary facet. -/
theorem eq_boundaryFacet_iff (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (τ : OrientedCell h (k + 1)) (hτ : τ.carrier = F)
    (v : vectorSpan ℝ σ.carrier)
    (hv : (v : V) ∉ (affineSpan ℝ τ.carrier).direction) :
    letI := h.finiteDimensional
    0 < (hF.outwardNormal hne hdim).someVector v →
    (τ = σ.boundaryFacet hF hne hdim ↔
      τ.orientation.contract τ.isConormal τ.finrank_quotient_direction v hv =
        -σ.orientation) := by
  have := h.finiteDimensional
  intro hpos
  constructor
  · rintro rfl
    exact σ.contract_boundaryFacet hF hne hdim v hv hpos
  · intro he
    have hc : τ.carrier = (σ.boundaryFacet hF hne hdim).carrier := by simp [hτ]
    have hp : (σ.boundaryFacet hF hne hdim).orientation.IsConormal
        (affineSpan ℝ τ.carrier).direction := by
      rw [hc]
      exact (σ.boundaryFacet hF hne hdim).isConormal
    have he' := σ.contract_boundaryFacet hF hne hdim v (by rwa [← hc]) hpos
    have hq : (σ.boundaryFacet hF hne hdim).orientation.contract hp
        τ.finrank_quotient_direction v hv = -σ.orientation := by
      simpa only [hc] using he'
    have ho := (Module.Ray.contract_eq_contract_iff τ.orientation
      (σ.boundaryFacet hF hne hdim).orientation τ.isConormal hp
      τ.finrank_quotient_direction v hv).mp (he.trans hq.symm)
    exact OrientedCell.ext hc ho

/-- Reversing a cell reverses the signed orientation of each boundary facet. -/
@[simp]
theorem boundaryFacet_reverse (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    σ.reverse.boundaryFacet (by simpa using hF) hne
        (by rw [reverse_carrier]; exact hdim) =
      (σ.boundaryFacet hF hne hdim).reverse := by
  have := h.finiteDimensional
  have hproper : F ≠ σ.carrier := by
    intro heq
    rw [heq] at hdim
    omega
  obtain ⟨x, hx, hxF⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hF.subset hproper)
  have hnecopy := hne
  obtain ⟨y, hy⟩ := hnecopy
  let v : vectorSpan ℝ σ.carrier :=
    ⟨y - x, vsub_mem_vectorSpan ℝ (hF.subset hy) hx⟩
  have hpos : 0 < (hF.outwardNormal hne hdim).someVector v :=
    (hF.outwardNormal_apply_pos_iff hne hdim hx hy).mpr hxF
  have hn : (v : V) ∉ (affineSpan ℝ (σ.boundaryFacet hF hne hdim).carrier).direction := by
    intro hmem
    have hz : (hF.outwardNormal hne hdim).someVector v = 0 := by
      apply LinearMap.mem_ker.mp
      rw [IsExposed.ker_outwardNormal]
      simpa only [boundaryFacet_carrier, direction_affineSpan, Submodule.mem_comap,
        Submodule.subtype_apply] using hmem
    linarith
  have he := (Module.Ray.contract_neg (σ.boundaryFacet hF hne hdim).orientation
    (σ.boundaryFacet hF hne hdim).isConormal
    (σ.boundaryFacet hF hne hdim).finrank_quotient_direction v hn).trans
      (congrArg Neg.neg (σ.contract_boundaryFacet hF hne hdim v hn hpos))
  symm
  have hc := σ.reverse.eq_boundaryFacet_iff (by simpa using hF) hne
    (by rw [reverse_carrier]; exact hdim) (σ.boundaryFacet hF hne hdim).reverse (by simp)
    ⟨y - x, by simpa only [reverse_carrier] using v.property⟩ (by simpa using hn)
  have hFr : IsExposed ℝ σ.reverse.carrier F := by simpa only [reverse_carrier] using hF
  have hdr : finrank ℝ (vectorSpan ℝ F) + 1 =
      finrank ℝ (vectorSpan ℝ σ.reverse.carrier) := by rw [reverse_carrier]; exact hdim
  have hpos' := (hFr.outwardNormal_apply_pos_iff hne hdr
    (x := x) (y := y) (by simpa only [reverse_carrier] using hx) hy).mpr hxF
  apply (hc hpos').mpr
  dsimp only [v] at he
  convert he using 1 <;> simp only [reverse_carrier, reverse_orientation]

/-- The boundary facet orientation is the canonical signed covector extension of
its parent's orientation. -/
theorem boundaryFacet_orientation (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    letI := h.finiteDimensional
    (σ.boundaryFacet hF hne hdim).orientation =
      hF.facetOrientation hne hdim σ.orientation
        (by simpa only [direction_affineSpan] using σ.isConormal) := by
  have := h.finiteDimensional
  rfl

/-- A facet inherited by a same-codimension subcell has the same signed conormal
orientation as the original facet. Both parent cells carry the same orientation;
the smaller facet need only be contained in the original one. -/
theorem boundaryFacet_orientation_eq_of_subset (σ τ : OrientedCell h k)
    (hτσ : τ.carrier ⊆ σ.carrier) (ho : τ.orientation = σ.orientation)
    {F G : Set V} (hF : IsExposed ℝ σ.carrier F) (hneF : F.Nonempty)
    (hdF : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hG : IsExposed ℝ τ.carrier G) (hneG : G.Nonempty)
    (hdG : finrank ℝ (vectorSpan ℝ G) + 1 = finrank ℝ (vectorSpan ℝ τ.carrier))
    (hGF : G ⊆ F) :
    (τ.boundaryFacet hG hneG hdG).orientation =
      (σ.boundaryFacet hF hneF hdF).orientation := by
  have := h.finiteDimensional
  -- The two facets have the same tangent hyperplane inside the parent direction.
  have hd : (affineSpan ℝ G).direction = (affineSpan ℝ F).direction := by
    apply Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le (affineSpan_mono ℝ hGF))
    have hσ := σ.finrank_direction_add
    have hτ := τ.finrank_direction_add
    rw [direction_affineSpan] at hσ hτ
    rw [direction_affineSpan, direction_affineSpan]
    omega
  -- A vector from the smaller parent to its facet points outward for both parents.
  have hnot : ¬ τ.carrier ⊆ F := by
    intro ht
    have hle := Submodule.finrank_mono (vectorSpan_mono ℝ ht)
    have hσ := σ.finrank_direction_add
    have hτ := τ.finrank_direction_add
    rw [direction_affineSpan] at hσ hτ
    omega
  obtain ⟨x, hx, hxF⟩ := Set.not_subset.mp hnot
  have hneGcopy := hneG
  obtain ⟨y, hy⟩ := hneGcopy
  let v : vectorSpan ℝ τ.carrier :=
    ⟨y - x, vsub_mem_vectorSpan ℝ (hG.subset hy) hx⟩
  have hposG := (hG.outwardNormal_apply_pos_iff hneG hdG hx hy).mpr
    (fun hxG => hxF (hGF hxG))
  have hnG : (v : V) ∉ (affineSpan ℝ G).direction := by
    intro hv
    have hz : (hG.outwardNormal hneG hdG).someVector v = 0 := by
      apply LinearMap.mem_ker.mp
      rw [IsExposed.ker_outwardNormal]
      simpa only [Submodule.mem_comap, Submodule.subtype_apply, direction_affineSpan] using hv
    exact (ne_of_gt hposG) hz
  let u : vectorSpan ℝ σ.carrier :=
    ⟨y - x, vsub_mem_vectorSpan ℝ (hF.subset (hGF hy)) (hτσ hx)⟩
  have hposF := (hF.outwardNormal_apply_pos_iff hneF hdF (hτσ hx) (hGF hy)).mpr hxF
  have hnF : (u : V) ∉ (affineSpan ℝ F).direction := by
    simpa only [u, v, ← hd] using hnG
  have hp : (σ.boundaryFacet hF hneF hdF).orientation.IsConormal
      (affineSpan ℝ G).direction := by
    rw [hd]
    exact (σ.boundaryFacet hF hneF hdF).isConormal
  -- The common outward contraction determines the top conormal orientation.
  apply (Module.Ray.contract_eq_contract_iff _ _
    (τ.boundaryFacet hG hneG hdG).isConormal hp
    (τ.boundaryFacet hG hneG hdG).finrank_quotient_direction v hnG).mp
  rw [τ.contract_boundaryFacet hG hneG hdG v hnG hposG, ho]
  exact (σ.contract_boundaryFacet hF hneF hdF u hnF hposF).symm.trans
    (Module.Ray.contract_congr _ _
      (σ.boundaryFacet hF hneF hdF).isConormal hp
      (σ.boundaryFacet hF hneF hdF).finrank_quotient_direction
      (τ.boundaryFacet hG hneG hdG).finrank_quotient_direction
      (y - x) hnF hnG rfl)

private theorem finite_boundaryFacets (σ : OrientedCell h k) :
    {τ : OrientedCell h (k + 1) | ∃ (F : Set V) (hF : IsExposed ℝ σ.carrier F)
      (hne : F.Nonempty)
      (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)),
      τ = σ.boundaryFacet hF hne hdim}.Finite := by
  apply Set.Finite.of_injOn (f := OrientedCell.carrier)
    (t := {F | IsExposed ℝ σ.carrier F})
  · rintro τ ⟨F, hF, hne, hdim, rfl⟩
    simpa only [boundaryFacet_carrier, Set.mem_ofPred_eq] using hF
  · rintro τ ⟨F, hF, hne, hdim, rfl⟩ υ ⟨G, hG, hneG, hdimG, rfl⟩ heq
    simp only [boundaryFacet_carrier] at heq
    subst G
    rfl
  · obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
    exact hP ▸ P.isConvexPolyhedron.finite_exposed_sets

/-- All nonempty exposed facets, with their signed boundary orientations. Each geometric
facet occurs once, regardless of redundant inequalities in a presentation of the cell. -/
def boundaryFacets (σ : OrientedCell h k) : Finset (OrientedCell h (k + 1)) :=
  σ.finite_boundaryFacets.toFinset

/-- Membership in the signed facet family is characterized by the canonical facet construction. -/
@[simp]
theorem mem_boundaryFacets (σ : OrientedCell h k) (τ : OrientedCell h (k + 1)) :
    τ ∈ σ.boundaryFacets ↔ ∃ (F : Set V) (hF : IsExposed ℝ σ.carrier F)
      (hne : F.Nonempty)
      (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)),
      τ = σ.boundaryFacet hF hne hdim :=
  Set.Finite.mem_toFinset _

/-- The signed facet associated to any nonempty exposed facet occurs in the family. -/
theorem boundaryFacet_mem_boundaryFacets (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    σ.boundaryFacet hF hne hdim ∈ σ.boundaryFacets :=
  (σ.mem_boundaryFacets _).mpr ⟨F, hF, hne, hdim, rfl⟩

/-- Every boundary facet is supported inside its parent cell. -/
theorem carrier_subset_of_mem_boundaryFacets (σ : OrientedCell h k)
    {τ : OrientedCell h (k + 1)} (hτ : τ ∈ σ.boundaryFacets) :
    τ.carrier ⊆ σ.carrier := by
  obtain ⟨F, hF, hne, hdim, rfl⟩ := (σ.mem_boundaryFacets τ).mp hτ
  exact hF.subset

/-- The parent determines the orientation of a boundary facet from its support. -/
theorem carrier_injOn_boundaryFacets (σ : OrientedCell h k) :
    Set.InjOn (fun τ : OrientedCell h (k + 1) => τ.carrier) {τ | τ ∈ σ.boundaryFacets} := by
  rintro τ hτ υ hυ he
  obtain ⟨F, hF, hne, hdim, rfl⟩ := (σ.mem_boundaryFacets τ).mp hτ
  obtain ⟨G, hG, hneG, hdimG, rfl⟩ := (σ.mem_boundaryFacets υ).mp hυ
  simp only [boundaryFacet_carrier] at he
  subst G
  rfl

/-- Every signed facet of a half-space cut retaining the parent's codimension is supported
on the cutting section or on the restriction of an original signed facet. The orientations
of the parent and the cut piece need not agree for this support classification. -/
theorem carrier_eq_cut_zero_or_inter_boundaryFacet (σ τ : OrientedCell h k)
    (g : V →ᴬ[ℝ] ℝ) (hτ : τ.carrier = σ.carrier ∩ {x | g x ≤ 0})
    {υ : OrientedCell h (k + 1)} (hυ : υ ∈ τ.boundaryFacets) :
    υ.carrier = σ.carrier ∩ {x | g x = 0} ∨
      ∃ η ∈ σ.boundaryFacets, υ.carrier = η.carrier ∩ {x | g x ≤ 0} := by
  have := h.finiteDimensional
  obtain ⟨F, hF, hFne, hFdim, hυF⟩ := (τ.mem_boundaryFacets υ).mp hυ
  have hσdim := σ.finrank_direction_add
  have hτdim := τ.finrank_direction_add
  rw [direction_affineSpan] at hσdim hτdim
  have hcut : finrank ℝ (vectorSpan ℝ (σ.carrier ∩ {x | g x ≤ 0})) =
      finrank ℝ (vectorSpan ℝ σ.carrier) := by
    rw [← hτ]
    omega
  have hpoly : TauCeti.IsConvexPolyhedron σ.carrier := by
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
    exact hP ▸ P.isConvexPolyhedron
  have hface : IsExposed ℝ (σ.carrier ∩ {x | g x ≤ 0}) F := by rwa [← hτ]
  rcases (hpoly.facet_cut_iff g hFne hcut (by omega)).mp hface with he | ⟨G, hG, hGdim, he⟩
  · left
    simpa only [hυF, boundaryFacet_carrier] using he
  · right
    have hGne : G.Nonempty := hFne.mono (he ▸ Set.inter_subset_left)
    refine ⟨σ.boundaryFacet hG hGne hGdim,
      σ.boundaryFacet_mem_boundaryFacets hG hGne hGdim, ?_⟩
    simpa only [hυF, boundaryFacet_carrier] using he

/-- A vector transverse to a cell is transverse to every boundary facet. -/
theorem notMem_direction_of_mem_boundaryFacets (σ : OrientedCell h k)
    {τ : OrientedCell h (k + 1)} (hτ : τ ∈ σ.boundaryFacets) {v : V}
    (hv : v ∉ (affineSpan ℝ σ.carrier).direction) :
    v ∉ (affineSpan ℝ τ.carrier).direction :=
  fun hm => hv ((AffineSubspace.direction_le
    (affineSpan_mono ℝ (σ.carrier_subset_of_mem_boundaryFacets hτ))) hm)

open Classical in
/-- Reversing the parent reverses every boundary facet. -/
@[simp]
theorem boundaryFacets_reverse (σ : OrientedCell h k) :
    σ.reverse.boundaryFacets = σ.boundaryFacets.image reverse := by
  classical
  ext τ
  constructor
  · rintro hτ
    obtain ⟨F, hF, hne, hdim, rfl⟩ := (σ.reverse.mem_boundaryFacets τ).mp hτ
    have hF' : IsExposed ℝ σ.carrier F := by simpa only [reverse_carrier] using hF
    have hd' : finrank ℝ (vectorSpan ℝ F) + 1 =
        finrank ℝ (vectorSpan ℝ σ.carrier) := by
      rw [reverse_carrier] at hdim
      exact hdim
    exact Finset.mem_image.mpr ⟨σ.boundaryFacet hF' hne hd',
      σ.boundaryFacet_mem_boundaryFacets hF' hne hd', (σ.boundaryFacet_reverse hF' hne hd').symm⟩
  · rintro hτ
    obtain ⟨υ, hυ, rfl⟩ := Finset.mem_image.mp hτ
    obtain ⟨F, hF, hne, hdim, rfl⟩ := (σ.mem_boundaryFacets υ).mp hυ
    rw [← boundaryFacet_reverse]
    exact σ.reverse.boundaryFacet_mem_boundaryFacets _ _ _

/-- A cell with zero-dimensional direction has no nonempty facets. -/
@[simp]
theorem boundaryFacets_eq_empty_of_finrank_eq (σ : OrientedCell h k)
    (hk : k = finrank ℝ V) : σ.boundaryFacets = ∅ := by
  have hzero : finrank ℝ (vectorSpan ℝ σ.carrier) = 0 := by
    have hd := σ.finrank_direction_add
    rw [direction_affineSpan] at hd
    omega
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro τ hτ
  obtain ⟨F, hF, hne, hdim, heq⟩ := (σ.mem_boundaryFacets τ).mp hτ
  omega

/-- A surviving facet of a same-dimensional oriented piece has the original
boundary orientation. The piece and the parent carry the same orientation. -/
theorem boundaryFacet_orientation_eq_of_subset (σ π : OrientedCell h k)
    (hπ : π.carrier ⊆ σ.carrier) (ho : π.orientation = σ.orientation)
    {F G : Set V} (hF : IsExposed ℝ σ.carrier F) (hG : IsExposed ℝ π.carrier G)
    (hFne : F.Nonempty) (hGne : G.Nonempty)
    (hFd : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hGd : finrank ℝ (vectorSpan ℝ G) + 1 = finrank ℝ (vectorSpan ℝ π.carrier))
    (hGF : G ⊆ F) :
    (π.boundaryFacet hG hGne hGd).orientation =
      (σ.boundaryFacet hF hFne hFd).orientation := by
  have := h.finiteDimensional
  -- Equal codimensions identify the parent and facet directions.
  have hdP : vectorSpan ℝ π.carrier = vectorSpan ℝ σ.carrier := by
    simpa only [direction_affineSpan] using π.direction_eq_of_subset σ hπ
  have hdF : vectorSpan ℝ G = vectorSpan ℝ F :=
    Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hGF) (by rw [hdP] at hGd; omega)
  -- A vector towards the smaller facet points outwards for both parents.
  obtain ⟨x, hx, hxF⟩ : ∃ x ∈ π.carrier, x ∉ F := by
    apply Set.not_subset.mp
    intro hs
    have hle := Submodule.finrank_mono (vectorSpan_mono ℝ hs)
    rw [hdP] at hle
    omega
  have hGne' := hGne
  obtain ⟨y, hy⟩ := hGne'
  let v : vectorSpan ℝ π.carrier := ⟨y - x, vsub_mem_vectorSpan ℝ (hG.subset hy) hx⟩
  have hposG := (hG.outwardNormal_apply_pos_iff hGne hGd hx hy).mpr
    (fun hxG => hxF (hGF hxG))
  have hposF := (hF.outwardNormal_apply_pos_iff hFne hFd (hπ hx) (hGF hy)).mpr hxF
  have hv : (v : V) ∉ (affineSpan ℝ G).direction := by
    intro hv
    have hz : (hG.outwardNormal hGne hGd).someVector v = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hG.ker_outwardNormal hGne hGd]
      simpa only [direction_affineSpan, Submodule.mem_comap, Submodule.subtype_apply] using hv
    exact (ne_of_gt hposG) hz
  -- The shared outward contraction determines the boundary orientation.
  let τ : OrientedCell h (k + 1) :=
    { π.boundaryFacet hG hGne hGd with
      orientation := (σ.boundaryFacet hF hFne hFd).orientation
      isConormal := by
        rw [boundaryFacet_carrier, direction_affineSpan, hdF, ← direction_affineSpan]
        simpa only [boundaryFacet_carrier] using (σ.boundaryFacet hF hFne hFd).isConormal }
  have he : τ = π.boundaryFacet hG hGne hGd := by
    apply (π.eq_boundaryFacet_iff hG hGne hGd τ (by simp [τ]) v
      (by simpa only [τ, boundaryFacet_carrier] using hv) hposG).mpr
    have hc := σ.contract_boundaryFacet hF hFne hFd
      ⟨y - x, vsub_mem_vectorSpan ℝ (hF.subset (hGF hy)) (hπ hx)⟩
      (by simpa only [boundaryFacet_carrier, direction_affineSpan, ← hdF] using hv) hposF
    simpa only [τ, boundaryFacet_carrier, direction_affineSpan, hdF, ho] using hc
  exact (congrArg orientation he).symm

/-- Equally oriented cells with the same tangent direction induce opposite
signed orientations on a facet exposed by opposite functionals. -/
theorem boundaryFacet_eq_reverse_of_toExposed (σ τ : OrientedCell h k)
    {F : Set V} (hF : IsExposed ℝ σ.carrier F) (hG : IsExposed ℝ τ.carrier F)
    (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hd : vectorSpan ℝ σ.carrier = vectorSpan ℝ τ.carrier)
    (ho : σ.orientation = τ.orientation)
    (l : V →L[ℝ] ℝ) (hl : F = l.toExposed σ.carrier)
    (hm : F = (-l).toExposed τ.carrier) :
    σ.boundaryFacet hF hne hdim =
      (τ.boundaryFacet hG hne (by rw [← hd]; exact hdim)).reverse := by
  have := h.finiteDimensional
  have hlW : ∃ n ∈ vectorSpan ℝ σ.carrier, l n ≠ 0 := by
    by_contra hn
    apply l.comp_vectorSpan_ne_zero (hl ▸ hne) (by
      rw [← hl]
      intro he
      rw [he] at hdim
      omega)
    ext v
    simpa only [ContinuousLinearMap.coe_coe, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.zero_apply] using
      not_not.mp (fun hv => hn ⟨v, v.property, hv⟩)
  have hmW : ∃ n ∈ vectorSpan ℝ τ.carrier, (-l) n ≠ 0 := by
    simpa only [← hd, neg_apply, neg_ne_zero] using hlW
  have hk := (σ.boundaryFacet hF hne hdim).finrank_quotient_direction
  rw [boundaryFacet_carrier, direction_affineSpan] at hk
  apply OrientedCell.ext (by simp only [boundaryFacet_carrier, reverse_carrier])
  rw [reverse_orientation, σ.boundaryFacet_orientation, τ.boundaryFacet_orientation,
    hF.facetOrientation_eq_neg_wedgeCovector hne hdim σ.orientation
      (by simpa only [direction_affineSpan] using σ.isConormal) hk l hl hlW,
    hG.facetOrientation_eq_neg_wedgeCovector hne (by rw [← hd]; exact hdim) τ.orientation
      (by simpa only [direction_affineSpan] using τ.isConormal) hk (-l) hm hmW]
  simp only [← ho, ← hd, ContinuousLinearMap.toLinearMap_neg]
  rw [Module.Ray.wedgeCovector_neg_right, neg_neg]

/-- Adjacent equally oriented cells spanning the same affine subspace induce
opposite signed boundary orientations on their common facet. -/
theorem boundaryFacet_eq_reverse_of_common_facet (σ τ : OrientedCell h k)
    {F : Set V} (hF : IsExposed ℝ σ.carrier F) (hG : IsExposed ℝ τ.carrier F)
    (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hspan : affineSpan ℝ σ.carrier = affineSpan ℝ τ.carrier)
    (ho : σ.orientation = τ.orientation) (hinter : σ.carrier ∩ τ.carrier = F) :
    σ.boundaryFacet hF hne hdim =
      (τ.boundaryFacet hG hne (by
        rw [← direction_affineSpan ℝ τ.carrier, ← hspan, direction_affineSpan]
        exact hdim)).reverse := by
  have := h.finiteDimensional
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
  obtain ⟨Q, hQ⟩ := isRationalNormalPolyhedron_iff.mp τ.rational
  obtain ⟨l, hl, hm⟩ := hF.exists_opposite_exposing hG (hP ▸ P.convex) (hQ ▸ Q.convex)
    hne hdim hspan hinter
  exact σ.boundaryFacet_eq_reverse_of_toExposed τ hF hG hne hdim
    (by simpa only [direction_affineSpan] using congrArg AffineSubspace.direction hspan)
    ho l hl hm

/-- The common slice of a hyperplane cut occurs in both signed facet families,
with opposite orientations, when the two pieces have the same orientation. -/
theorem exists_boundaryFacet_cut_reverse (σ σ₁ σ₂ : OrientedCell h k)
    (l : V →L[ℝ] ℝ) (a : ℝ)
    (hminus : σ₁.carrier = σ.carrier ∩ {x | l x ≤ a})
    (hplus : σ₂.carrier = σ.carrier ∩ {x | a ≤ l x})
    (ho : σ₁.orientation = σ₂.orientation)
    (hne : (σ.carrier ∩ {x | l x = a}).Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ (σ.carrier ∩ {x | l x = a})) + 1 =
      finrank ℝ (vectorSpan ℝ σ.carrier)) :
    ∃ υ ∈ σ₁.boundaryFacets, υ.carrier = σ.carrier ∩ {x | l x = a} ∧
      υ.reverse ∈ σ₂.boundaryFacets := by
  have := h.finiteDimensional
  have hdminus : vectorSpan ℝ σ₁.carrier = vectorSpan ℝ σ.carrier := by
    simpa only [direction_affineSpan] using
      σ₁.direction_eq_of_subset σ (by rw [hminus]; exact inter_subset_left)
  have hdplus : vectorSpan ℝ σ₂.carrier = vectorSpan ℝ σ.carrier := by
    simpa only [direction_affineSpan] using
      σ₂.direction_eq_of_subset σ (by rw [hplus]; exact inter_subset_left)
  let F := σ.carrier ∩ {x | l x = a}
  have hl : F = l.toExposed σ₁.carrier := by
    rw [hminus, l.toExposed_inter_le σ.carrier a hne]
  have hm : F = (-l).toExposed σ₂.carrier := by
    have hne' : (σ.carrier ∩ {x | (-l) x = -a}).Nonempty := by
      simpa only [neg_apply, neg_inj] using hne
    have he := (-l).toExposed_inter_le σ.carrier (-a) hne'
    simpa only [neg_apply, neg_le_neg_iff, neg_inj, ← hplus] using he.symm
  have hF : IsExposed ℝ σ₁.carrier F := by
    rw [hl]
    exact ContinuousLinearMap.toExposed.isExposed
  have hG : IsExposed ℝ σ₂.carrier F := by
    rw [hm]
    exact ContinuousLinearMap.toExposed.isExposed
  have hdm : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ₁.carrier) := by
    rw [hdminus]
    exact hdim
  have hdp : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ₂.carrier) := by
    rw [hdplus]
    exact hdim
  let υ := σ₁.boundaryFacet hF hne hdm
  have hυ : υ ∈ σ₁.boundaryFacets := σ₁.boundaryFacet_mem_boundaryFacets hF hne hdm
  have he : σ₂.boundaryFacet hG hne hdp = υ.reverse := by
    have hr := σ₁.boundaryFacet_eq_reverse_of_toExposed σ₂ hF hG hne hdm
      (hdminus.trans hdplus.symm) ho l hl hm
    simpa only [reverse_reverse] using congrArg reverse hr.symm
  have hυr : υ.reverse ∈ σ₂.boundaryFacets := by
    rw [← he]
    exact σ₂.boundaryFacet_mem_boundaryFacets hG hne hdp
  exact ⟨υ, hυ, by simp only [υ, boundaryFacet_carrier, F], hυr⟩

end Mei.OrientedCell
