/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Topology.Algebra.Affine
public import Mei.Analysis.Convex.Intrinsic
public import Mei.LinearAlgebra.Dual.Order
public import Mathlib.LinearAlgebra.Ray
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Exposed subsets, relative interiors and affine transport

Intersections of exposed subsets are exposed in the intersection of their
ambient sets. An affine equivalence with continuous inverse carries exposed subsets to
exposed subsets. Composing an exposing linear functional with the inverse
linear part preserves all comparisons: the inverse translation contributes
the same additive constant at every point.

An exposed subset meeting the relative interior is the whole ambient set.
See also `AffineMap.eq_zero_on_of_mem_intrinsicInterior`.
Distinct exposed facets containing a common nonempty facet meet exactly there,
even when the ambient set is not convex.

A nonempty exposed facet has a canonical outward conormal ray on the direction
of its parent set. Its representatives vanish precisely on the facet direction
and are positive from a point outside the facet towards the facet. Restricting to
the parent direction removes the freedom to add an ambient functional vanishing
there. This makes the ray independent of the exposing inequality, including for
lower-dimensional polyhedra with lineality, and supplies the outward conormal
used to orient boundary faces.

The facet construction uses Mathlib's `ContinuousLinearMap.toExposed`,
`Submodule.comapSubtypeEquivOfLe` and `Module.Ray`, and
`LinearMap.exists_pos_smul_eq_of_ker_le_ker` for positive proportionality.
-/

public section

namespace IsExposed

section Intersections

variable {R V : Type*} [TopologicalSpace R] [Ring R] [PartialOrder R] [IsOrderedRing R]
  [ContinuousAdd R] [AddCommMonoid V] [TopologicalSpace V] [Module R V] {P Q F G : Set V}

/-- Intersections of exposed subsets are exposed in the intersection of their
ambient sets. This includes empty intersections and requires no convexity. -/
theorem inter_inter (hF : IsExposed R P F) (hG : IsExposed R Q G) :
    IsExposed R (P ∩ Q) (F ∩ G) := by
  rintro ⟨p, hpF, hpG⟩
  obtain ⟨l, hl⟩ := hF ⟨p, hpF⟩
  obtain ⟨m, hm⟩ := hG ⟨p, hpG⟩
  have hpL := hl ▸ hpF
  have hpM := hm ▸ hpG
  refine ⟨l + m, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxF, hxG⟩
    have hxL := hl ▸ hxF
    have hxM := hm ▸ hxG
    exact ⟨⟨hxL.1, hxM.1⟩, fun y hy => add_le_add (hxL.2 y hy.1) (hxM.2 y hy.2)⟩
  · rintro x ⟨⟨hxP, hxQ⟩, hxmax⟩
    have hsum := hxmax p ⟨hpL.1, hpM.1⟩
    constructor
    · rw [hl]
      refine ⟨hxP, fun y hy => ?_⟩
      exact (add_le_add_iff_right (m x)).mp
        ((add_le_add (hpL.2 y hy) (hpM.2 x hxQ)).trans hsum)
    · rw [hm]
      refine ⟨hxQ, fun y hy => ?_⟩
      exact (add_le_add_iff_left (l x)).mp
        ((add_le_add (hpL.2 x hxP) (hpM.2 y hy)).trans hsum)

end Intersections

variable {R V W : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module R W] {P F : Set V}

/-- An affine equivalence with continuous inverse preserves exposed subsets,
including empty subsets, without any convexity assumption. -/
theorem image_affineEquiv (hF : IsExposed R P F) (e : V ≃ᵃ[R] W)
    (he : Continuous e.symm) : IsExposed R (e '' P) (e '' F) := by
  intro hne
  have hFne : F.Nonempty := by
    obtain ⟨y, x, hx, _⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hF hFne
  let T : W →L[R] V := ⟨e.symm.toAffineMap.linear, AffineMap.continuous_linear_iff.mpr he⟩
  let k := l.comp T
  have hval (y : W) : l (e.symm y) = k y + l (e.symm 0) := by
    have hd := congrFun e.symm.toAffineMap.decomp y
    have heq : e.symm y = e.symm.toAffineMap.linear y + e.symm 0 := by
      simpa only [AffineEquiv.coe_toAffineMap, Pi.add_apply] using hd
    rw [heq, map_add]
    rfl
  have hcompare (x y : W) : k x ≤ k y ↔ l (e.symm x) ≤ l (e.symm y) := by
    rw [hval x, hval y, add_le_add_iff_right]
  refine ⟨k, Set.ext fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' := hl ▸ hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    apply (hcompare (e w) (e x)).mpr
    simpa only [e.symm_apply_apply] using hx'.2 w hw
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, fun w hw => ?_⟩
    have hm := (hcompare (e w) (e x)).mp (hmax (e w) ⟨w, hw, rfl⟩)
    simpa only [e.symm_apply_apply] using hm

/-- An affine equivalence continuous in both directions preserves and reflects
exposure of subsets. -/
theorem image_affineEquiv_iff {e : V ≃ᵃ[R] W}
    (he : Continuous e) (hes : Continuous e.symm) :
    IsExposed R (e '' P) (e '' F) ↔ IsExposed R P F := by
  constructor
  · intro hF
    have hback := hF.image_affineEquiv e.symm he
    have hP : e.symm '' (e '' P) = P := e.toEquiv.symm_image_image P
    have hFset : e.symm '' (e '' F) = F := e.toEquiv.symm_image_image F
    rwa [hP, hFset] at hback
  · intro hF
    exact hF.image_affineEquiv e hes

end IsExposed

namespace IsExposed

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {P F : Set V}

/-- An exposed subset meeting the relative interior of its ambient set is the whole set.
Neither convexity nor finite dimensionality is required. -/
theorem eq_of_mem_intrinsicInterior (hF : IsExposed ℝ P F) {x : V}
    (hxF : x ∈ F) (hx : x ∈ intrinsicInterior ℝ P) : F = P := by
  obtain ⟨l, hl⟩ := hF ⟨x, hxF⟩
  have hxmax := hl ▸ hxF
  let g : V →ᵃ[ℝ] ℝ := l.toLinearMap.toAffineMap - AffineMap.const ℝ V (l x)
  have hg : ∀ p ∈ P, g p = 0 :=
    g.eq_zero_on_of_mem_intrinsicInterior
      (fun p hp => sub_nonpos.mpr (hxmax.2 p hp)) hx (sub_self _)
  apply Set.Subset.antisymm hF.subset
  intro p hp
  rw [hl]
  exact ⟨hp, fun q hq => (hxmax.2 q hq).trans (le_of_eq (sub_eq_zero.mp (hg p hp)).symm)⟩

end IsExposed

namespace ContinuousLinearMap

section OrderedRing

variable {K V : Type*} [Ring K] [PartialOrder K] [TopologicalSpace K]
  [AddCommMonoid V] [TopologicalSpace V] [Module K V]

/-- When a level set meets a set, the maximizers of the corresponding closed
half-space cut are exactly that level set. No convexity is required. -/
@[simp]
theorem toExposed_inter_le (l : V →L[K] K) (P : Set V) (c : K)
    (hne : (P ∩ {x | l x = c}).Nonempty) :
    l.toExposed (P ∩ {x | l x ≤ c}) = P ∩ {x | l x = c} := by
  obtain ⟨y, hy, hly⟩ := hne
  have hly : l y = c := hly
  ext x
  constructor
  · rintro ⟨⟨hx, hlx⟩, hmax⟩
    exact ⟨hx, le_antisymm hlx (by simpa only [hly] using hmax y ⟨hy, hly.le⟩)⟩
  · rintro ⟨hx, hlx⟩
    exact ⟨⟨hx, hlx.le⟩, fun z hz => hz.2.trans hlx.ge⟩

end OrderedRing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Subtracting a multiple of a height constant on the base preserves all
comparisons of functional values there, and therefore preserves its maximizers. -/
theorem toExposed_sub_smul_of_eq (l f : V →L[ℝ] ℝ) (P : Set V) (a c : ℝ)
    (hfP : ∀ x ∈ P, f x = c) :
    (l - a • f).toExposed P = l.toExposed P := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    have hm := hmax y hy
    simpa only [sub_apply, smul_apply, smul_eq_mul, hfP x hx, hfP y hy,
      sub_le_sub_iff_right] using hm
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    simpa only [sub_apply, smul_apply, smul_eq_mul, hfP x hx, hfP y hy,
      sub_le_sub_iff_right] using hmax y hy

end ContinuousLinearMap

namespace ContinuousLinearMap

section Ring

variable {K V : Type*} [Ring K] [PartialOrder K]
  [TopologicalSpace K] [AddCommMonoid V] [Module K V] [TopologicalSpace V]
  {P : Set V}

/-- A maximizer identifies all other maximizers by equality of functional values. -/
theorem mem_toExposed_iff_of_mem (l : V →L[K] K) {y : V} (hy : y ∈ l.toExposed P)
    {x : V} : x ∈ l.toExposed P ↔ x ∈ P ∧ l x = l y := by
  constructor
  · intro hx
    exact ⟨hx.1, le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, fun z hz => heq ▸ hy.2 z hz⟩

end Ring

section Ring

variable {K V : Type*} [Ring K] [PartialOrder K]
  [TopologicalSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] {P : Set V}

/-- An exposing functional vanishes on the direction of its exposed set. -/
theorem vectorSpan_toExposed_le_ker (l : V →L[K] K) (P : Set V) :
    vectorSpan K (l.toExposed P) ≤ l.toLinearMap.ker := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro v ⟨x, hx, y, hy, rfl⟩
  exact LinearMap.mem_ker.mpr (by
    simp only [ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub]
    exact sub_eq_zero.mpr ((l.mem_toExposed_iff_of_mem hy).mp hx).2)

/-- An exposing functional of a nonempty proper face is nonzero on the parent direction. -/
theorem comp_vectorSpan_ne_zero (l : V →L[K] K) (hne : (l.toExposed P).Nonempty)
    (hproper : l.toExposed P ≠ P) : l.toLinearMap.comp (vectorSpan K P).subtype ≠ 0 := by
  obtain ⟨y, hy⟩ := hne
  intro hzero
  apply hproper
  refine Set.Subset.antisymm (fun x hx => hx.1) fun x hx => ?_
  apply (l.mem_toExposed_iff_of_mem hy).mpr
  refine ⟨hx, sub_eq_zero.mp ?_⟩
  have hv := LinearMap.congr_fun hzero ⟨x - y, vsub_mem_vectorSpan K hx hy.1⟩
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, map_sub,
    ContinuousLinearMap.coe_coe, LinearMap.zero_apply] using hv

end Ring

section DivisionRing

variable {K V : Type*} [DivisionRing K] [PartialOrder K]
  [TopologicalSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] {P : Set V}

/-- On the parent direction, the kernel of a facet's exposing functional is exactly
its tangent direction. Only the parent direction needs to be finite-dimensional. -/
theorem ker_comp_vectorSpan_of_toExposed (l : V →L[K] K)
    [FiniteDimensional K (vectorSpan K P)] (hne : (l.toExposed P).Nonempty)
    (hdim : Module.finrank K (vectorSpan K (l.toExposed P)) + 1 =
      Module.finrank K (vectorSpan K P)) :
    (l.toLinearMap.comp (vectorSpan K P).subtype).ker =
      (vectorSpan K (l.toExposed P)).comap (vectorSpan K P).subtype := by
  have hle : vectorSpan K (l.toExposed P) ≤ vectorSpan K P :=
    vectorSpan_mono K (fun _ hx => hx.1)
  have hproper : l.toExposed P ≠ P := by
    intro heq
    rw [heq] at hdim
    omega
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero
    (l.comp_vectorSpan_ne_zero hne hproper)
  have hsub : (vectorSpan K (l.toExposed P)).comap (vectorSpan K P).subtype ≤
      (l.toLinearMap.comp (vectorSpan K P).subtype).ker :=
    Submodule.comap_mono (l.vectorSpan_toExposed_le_ker P)
  have hfin := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  exact (Submodule.eq_of_le_of_finrank_eq hsub (by omega)).symm

end DivisionRing

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] {P : Set V}

/-- Two functionals exposing the same facet determine the same outward conormal ray
on the parent direction; their ambient kernels need not coincide. -/
theorem sameRay_comp_vectorSpan_of_toExposed_eq (l m : V →L[K] K)
    [FiniteDimensional K (vectorSpan K P)]
    (hne : (l.toExposed P).Nonempty) (heq : l.toExposed P = m.toExposed P)
    (hdim : Module.finrank K (vectorSpan K (l.toExposed P)) + 1 =
      Module.finrank K (vectorSpan K P)) :
    SameRay K (l.toLinearMap.comp (vectorSpan K P).subtype)
      (m.toLinearMap.comp (vectorSpan K P).subtype) := by
  have hproper : l.toExposed P ≠ P := by
    intro heq
    rw [heq] at hdim
    omega
  have hsubset : l.toExposed P ⊆ P := fun _ hx => hx.1
  obtain ⟨x, hxP, hxF⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hsubset hproper)
  have hnecopy := hne
  obtain ⟨y, hy⟩ := hnecopy
  have hy' : y ∈ m.toExposed P := heq ▸ hy
  have hxF' : x ∉ m.toExposed P := heq ▸ hxF
  have hl : 0 < l y - l x := sub_pos.mpr <|
    lt_of_le_of_ne (hy.2 x hxP) (fun hxy => hxF
      ((l.mem_toExposed_iff_of_mem hy).mpr ⟨hxP, hxy⟩))
  have hm : 0 < m y - m x := sub_pos.mpr <|
    lt_of_le_of_ne (hy'.2 x hxP) (fun hxy => hxF'
      ((m.mem_toExposed_iff_of_mem hy').mpr ⟨hxP, hxy⟩))
  have hk : (l.toLinearMap.comp (vectorSpan K P).subtype).ker =
      (m.toLinearMap.comp (vectorSpan K P).subtype).ker := by
    rw [l.ker_comp_vectorSpan_of_toExposed hne hdim,
      m.ker_comp_vectorSpan_of_toExposed (heq ▸ hne) (heq ▸ hdim), heq]
  obtain ⟨c, hc, hcm⟩ := LinearMap.exists_pos_smul_eq_of_ker_le_ker _ _ hk.le
    (v := ⟨y - x, vsub_mem_vectorSpan K hy.1 hxP⟩) (by simpa using hl) (by simpa using hm)
  rw [← hcm]
  exact SameRay.sameRay_pos_smul_right _ hc

end ContinuousLinearMap

namespace IsExposed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {P F : Set V} [FiniteDimensional ℝ (vectorSpan ℝ P)]

/-- A nonempty exposed subset with the same affine-direction dimension as its
base is the whole base. This also holds for a nonconvex base, and only its
affine direction needs to be finite-dimensional. -/
theorem eq_of_finrank_vectorSpan_eq (hF : IsExposed ℝ P F) (hne : F.Nonempty)
    (hdim : Module.finrank ℝ (vectorSpan ℝ F) = Module.finrank ℝ (vectorSpan ℝ P)) :
    F = P := by
  obtain ⟨l, hl⟩ := hF hne
  have hdir := Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hF.subset) hdim
  have hker : vectorSpan ℝ F ≤ LinearMap.ker l.toLinearMap := by
    rw [hl]
    exact l.vectorSpan_toExposed_le_ker P
  apply Set.Subset.antisymm hF.subset
  intro x hx
  obtain ⟨z, hz⟩ := hne
  have hxz := vsub_mem_vectorSpan ℝ hx (hF.subset hz)
  rw [← hdir] at hxz
  have hlxz := hker hxz
  have he : l x = l z := sub_eq_zero.mp (by simpa only [LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] using hlxz)
  have hz' := hl ▸ hz
  rw [hl]
  exact ⟨hx, fun y hy => by simpa only [he] using hz'.2 y hy⟩

/-- Distinct exposed facets containing a common nonempty facet meet exactly in
that common facet. The ambient set need not be convex or polyhedral, and only
its affine direction needs to be finite-dimensional. -/
theorem inter_eq_of_common_facet {G Q : Set V}
    (hF : IsExposed ℝ P F) (hG : IsExposed ℝ P G)
    (hQ : IsExposed ℝ F Q) (hne : Q.Nonempty) (hQG : Q ⊆ G) (hFG : F ≠ G)
    (hFd : Module.finrank ℝ (vectorSpan ℝ F) + 1 =
      Module.finrank ℝ (vectorSpan ℝ P))
    (hGd : Module.finrank ℝ (vectorSpan ℝ G) + 1 =
      Module.finrank ℝ (vectorSpan ℝ P))
    (hQd : Module.finrank ℝ (vectorSpan ℝ Q) + 1 =
      Module.finrank ℝ (vectorSpan ℝ F)) : F ∩ G = Q := by
  have : FiniteDimensional ℝ (vectorSpan ℝ F) :=
    Submodule.finiteDimensional_of_le (vectorSpan_mono ℝ hF.subset)
  have : FiniteDimensional ℝ (vectorSpan ℝ G) :=
    Submodule.finiteDimensional_of_le (vectorSpan_mono ℝ hG.subset)
  have : FiniteDimensional ℝ (vectorSpan ℝ (F ∩ G)) :=
    Submodule.finiteDimensional_of_le (vectorSpan_mono ℝ Set.inter_subset_left)
  have hQI : Q ⊆ F ∩ G := Set.subset_inter hQ.subset hQG
  have hIn := hne.mono hQI
  have hIF := (hF.inter hG).mono hF.subset Set.inter_subset_left
  have hIG := (hF.inter hG).mono hG.subset Set.inter_subset_right
  have hle := Submodule.finrank_mono
    (vectorSpan_mono ℝ (Set.inter_subset_left : F ∩ G ⊆ F))
  have hge := Submodule.finrank_mono (vectorSpan_mono ℝ hQI)
  have hlt : Module.finrank ℝ (vectorSpan ℝ (F ∩ G)) <
      Module.finrank ℝ (vectorSpan ℝ F) := by
    by_contra! hn
    have heF := hIF.eq_of_finrank_vectorSpan_eq hIn (by omega)
    have heG := hIG.eq_of_finrank_vectorSpan_eq hIn (by omega)
    exact hFG (heF.symm.trans heG)
  exact ((hQ.mono Set.inter_subset_left hQI).eq_of_finrank_vectorSpan_eq hne (by omega)).symm

/-- An exposed facet is maximal among proper exposed subsets of its parent. -/
theorem eq_of_subset_of_finrank_add_one {G : Set V} (hF : IsExposed ℝ P F)
    (hne : F.Nonempty)
    (hdim : Module.finrank ℝ (vectorSpan ℝ F) + 1 = Module.finrank ℝ (vectorSpan ℝ P))
    (hG : IsExposed ℝ P G) (hFG : F ⊆ G) (hproper : G ≠ P) : F = G := by
  have : FiniteDimensional ℝ (vectorSpan ℝ G) :=
    Submodule.finiteDimensional_of_le (vectorSpan_mono ℝ hG.subset)
  have hle := Submodule.finrank_mono (vectorSpan_mono ℝ hG.subset)
  have hlt : Module.finrank ℝ (vectorSpan ℝ G) < Module.finrank ℝ (vectorSpan ℝ P) := by
    have hneG : G.Nonempty := hne.mono hFG
    have hneq : Module.finrank ℝ (vectorSpan ℝ G) ≠ Module.finrank ℝ (vectorSpan ℝ P) :=
      fun he => hproper (hG.eq_of_finrank_vectorSpan_eq hneG he)
    omega
  have hlow := Submodule.finrank_mono (vectorSpan_mono ℝ hFG)
  exact (hF.mono hG.subset hFG).eq_of_finrank_vectorSpan_eq hne (by omega)

end IsExposed

namespace IsExposed

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  {P F : Set V} [FiniteDimensional K (vectorSpan K P)]

/-- The canonical outward conormal of a nonempty exposed facet, as a ray of linear
functionals on the parent direction. No ambient inner product or full-dimensionality
is required. -/
noncomputable def outwardNormal (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : Module.finrank K (vectorSpan K F) + 1 = Module.finrank K (vectorSpan K P)) :
    Module.Ray K (Module.Dual K (vectorSpan K P)) := by
  let l := (hF hne).choose
  have hl : F = l.toExposed P := (hF hne).choose_spec
  exact rayOfNeZero K (l.toLinearMap.comp (vectorSpan K P).subtype)
    (l.comp_vectorSpan_ne_zero (hl ▸ hne) (by
      intro heq
      have hFP := hl.trans heq
      rw [hFP] at hdim
      omega))

/-- Any exposing functional computes the canonical outward conormal after restriction
to the parent direction. In particular, the result is independent of the inequality. -/
theorem outwardNormal_eq_ray (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : Module.finrank K (vectorSpan K F) + 1 = Module.finrank K (vectorSpan K P))
    (l : V →L[K] K) (hl : F = l.toExposed P)
    (hl0 : l.toLinearMap.comp (vectorSpan K P).subtype ≠ 0) :
    hF.outwardNormal hne hdim = rayOfNeZero K _ hl0 := by
  apply (ray_eq_iff _ _).mpr
  have hm : F = (hF hne).choose.toExposed P := (hF hne).choose_spec
  exact (hF hne).choose.sameRay_comp_vectorSpan_of_toExposed_eq l
    (hm ▸ hne) (hm.symm.trans hl) (hm ▸ hdim)

private theorem exists_pos_smul_outwardNormal (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : Module.finrank K (vectorSpan K F) + 1 = Module.finrank K (vectorSpan K P))
    (l : V →L[K] K) (hl : F = l.toExposed P) :
    ∃ c : K, 0 < c ∧ c • (hF.outwardNormal hne hdim).someVector =
      l.toLinearMap.comp (vectorSpan K P).subtype := by
  have hl0 := l.comp_vectorSpan_ne_zero (hl ▸ hne) (by
    rw [← hl]
    intro heq
    rw [heq] at hdim
    omega)
  have hr := (ray_eq_iff (hF.outwardNormal hne hdim).someVector_ne_zero hl0).mp
    ((hF.outwardNormal hne hdim).someVector_ray.trans
      (hF.outwardNormal_eq_ray hne hdim l hl hl0))
  exact hr.exists_pos_left (hF.outwardNormal hne hdim).someVector_ne_zero hl0

/-- The chosen representative of the outward conormal has the facet direction as its kernel,
inside the parent direction. -/
@[simp]
theorem ker_outwardNormal (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : Module.finrank K (vectorSpan K F) + 1 = Module.finrank K (vectorSpan K P)) :
    (hF.outwardNormal hne hdim).someVector.ker =
      (vectorSpan K F).comap (vectorSpan K P).subtype := by
  obtain ⟨l, hl'⟩ := hF hne
  have hl : F = l.toExposed P := hl'
  obtain ⟨c, hc, hcl⟩ := exists_pos_smul_outwardNormal hF hne hdim l hl
  calc
    _ = (l.toLinearMap.comp (vectorSpan K P).subtype).ker := by
      rw [← hcl, LinearMap.ker_smul _ c (ne_of_gt hc)]
    _ = _ := by
      rw [l.ker_comp_vectorSpan_of_toExposed (hl ▸ hne) (hl ▸ hdim), ← hl]

/-- The outward conormal is nonnegative on every vector from the parent to the facet. -/
theorem outwardNormal_apply_nonneg (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : Module.finrank K (vectorSpan K F) + 1 = Module.finrank K (vectorSpan K P))
    {x y : V} (hx : x ∈ P) (hy : y ∈ F) :
    0 ≤ (hF.outwardNormal hne hdim).someVector
      ⟨y - x, vsub_mem_vectorSpan K (hF.subset hy) hx⟩ := by
  obtain ⟨l, hl'⟩ := hF hne
  have hl : F = l.toExposed P := hl'
  obtain ⟨c, hc, hcl⟩ := exists_pos_smul_outwardNormal hF hne hdim l hl
  have hv := LinearMap.congr_fun hcl ⟨y - x, vsub_mem_vectorSpan K (hF.subset hy) hx⟩
  have hle := (hl ▸ hy).2 x hx
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
    Submodule.subtype_apply, ContinuousLinearMap.coe_coe, map_sub] at hv
  exact (mul_nonneg_iff_of_pos_left hc).mp (hv.symm ▸ sub_nonneg.mpr hle)

/-- The outward conormal vanishes from a parent point to a facet point exactly when
both points lie in the facet. -/
@[simp]
theorem outwardNormal_apply_eq_zero_iff (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : Module.finrank K (vectorSpan K F) + 1 = Module.finrank K (vectorSpan K P))
    {x y : V} (hx : x ∈ P) (hy : y ∈ F) :
    (hF.outwardNormal hne hdim).someVector
      ⟨y - x, vsub_mem_vectorSpan K (hF.subset hy) hx⟩ = 0 ↔ x ∈ F := by
  obtain ⟨l, hl'⟩ := hF hne
  have hl : F = l.toExposed P := hl'
  obtain ⟨c, hc, hcl⟩ := exists_pos_smul_outwardNormal hF hne hdim l hl
  have hv := LinearMap.congr_fun hcl ⟨y - x, vsub_mem_vectorSpan K (hF.subset hy) hx⟩
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply,
    Submodule.subtype_apply, ContinuousLinearMap.coe_coe, map_sub] at hv
  have hxiff : x ∈ F ↔ l x = l y := by
    rw [hl, l.mem_toExposed_iff_of_mem (hl ▸ hy), and_iff_right hx]
  rw [hxiff]
  constructor
  · intro hz
    rw [hz, mul_zero] at hv
    exact (sub_eq_zero.mp hv.symm).symm
  · intro heq
    rw [heq, sub_self] at hv
    exact (mul_eq_zero.mp hv).resolve_left (ne_of_gt hc)

/-- The outward conormal is strictly positive towards the facet from every parent
point outside the facet. -/
@[simp]
theorem outwardNormal_apply_pos_iff (hF : IsExposed K P F) (hne : F.Nonempty)
    (hdim : Module.finrank K (vectorSpan K F) + 1 = Module.finrank K (vectorSpan K P))
    {x y : V} (hx : x ∈ P) (hy : y ∈ F) :
    0 < (hF.outwardNormal hne hdim).someVector
      ⟨y - x, vsub_mem_vectorSpan K (hF.subset hy) hx⟩ ↔ x ∉ F := by
  rw [lt_iff_le_and_ne, and_iff_right (hF.outwardNormal_apply_nonneg hne hdim hx hy),
    ne_comm, Ne, hF.outwardNormal_apply_eq_zero_iff hne hdim hx hy]

end IsExposed
