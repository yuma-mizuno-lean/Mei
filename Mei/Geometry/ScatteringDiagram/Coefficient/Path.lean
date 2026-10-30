/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.LocalSystem
import Mathlib.Topology.Perfect

/-!
# Transport of coefficient sections along polygonal paths

A section of the coefficient local system obeys transport along every admissible
segment contained in its open domain, even when no single convex chart contains
that segment. Use `coefficientLocalSystem_segment_of_subset` to compute the value
at the final off-wall endpoint by applying the signed segment transport to the
initial value. For a contained admissible polygonal path, use
`coefficientLocalSystem_path` with the same endpoint values and the path transport.
Both results apply to arbitrary open domains in the regular space.

The sheaf, its local equations and coefficient evaluation are the existing
`coefficientLocalSystem`, `coefficientLocalSystem_segment` and
`DenseBasisTransport.value`. No global consistency or commutativity is assumed.
-/

public section

open Set CategoryTheory TopologicalSpace Opposite TopCat Mei.Convex Filter Topology
open scoped unitInterval

universe u v w z

namespace Mei.FiniteWallDiagram

variable {N : Type u} {V : Type v} [AddCommGroup N] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : FinitePolyhedralComplex h} {H : Type w} [Group H]
  (D : FiniteWallDiagram C H)

section Segment

variable {U : Opens C.regularSpace} (x y : C.coefficientPoints)
  (hx : x.val ∈ U) (hy : y.val ∈ U)
  (e : (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V))) ⟶
    ⟨y.val.val, y.property⟩)
  (hseg : segment ℝ x.val.val y.val.val ⊆ Subtype.val '' (U : Set C.regularSpace))

include e in
private theorem segment_regular (t : unitInterval) :
    AffineMap.lineMap x.val.val y.val.val (t : ℝ) ∉
      singularSupport (fun P : C.walls => (P : Set V)) :=
  e.down.regular (t : ℝ) t.property

private def segmentCurve : C(unitInterval, U) := by
  let f : C(unitInterval, C.regularSpace) :=
    ⟨fun t => ⟨AffineMap.lineMap x.val.val y.val.val (t : ℝ), segment_regular x y e t⟩,
      (AffineMap.lineMap_continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hf : ∀ t, f t ∈ U := by
    intro t
    obtain ⟨q, hq, heq⟩ := hseg (lineMap_mem_segment ℝ _ _ t.property)
    have heq' : q = f t := Subtype.ext heq
    exact heq' ▸ hq
  exact ⟨fun t => ⟨f t, hf t⟩, f.continuous.subtype_mk hf⟩

private theorem segmentCurve_zero : segmentCurve x y e hseg 0 = ⟨x.val, hx⟩ := by
  apply Subtype.ext
  exact Subtype.ext (AffineMap.lineMap_apply_zero _ _)

private theorem segmentCurve_one : segmentCurve x y e hseg 1 = ⟨y.val, hy⟩ := by
  apply Subtype.ext
  exact Subtype.ext (AffineMap.lineMap_apply_one _ _)

private theorem dense_segment_parameters :
    Dense {t : unitInterval | (segmentCurve x y e hseg t).val ∈ C.coefficientPoints} := by
  have hfin : (Subtype.val ⁻¹'
      (Prod.snd '' WallComplement.crossings
        (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V)))
        ⟨y.val.val, y.property⟩) : Set unitInterval).Finite :=
    (e.down.finite_crossings.image Prod.snd).preimage Subtype.val_injective.injOn
  have hd := dense_univ.sdiff_finite hfin
  rw [univ_sdiff] at hd
  apply hd.mono
  intro t ht P hp
  apply ht
  refine ⟨(P, (t : ℝ)), ?_, rfl⟩
  rw [WallComplement.mem_crossings]
  exact ⟨t.property, hp⟩

private def parameterPoint (t : unitInterval)
    (ht : (segmentCurve x y e hseg t).val ∈ C.coefficientPoints) : C.coefficientPoints :=
  ⟨(segmentCurve x y e hseg t).val, ht⟩

private def initialSegment (t : unitInterval)
    (ht : (segmentCurve x y e hseg t).val ∈ C.coefficientPoints) :
    (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V))) ⟶
      ⟨(parameterPoint x y e hseg t ht).val.val, ht⟩ :=
  ⟨e.down.subsegment ⟨le_rfl, zero_le_one⟩ t.property
    (AffineMap.lineMap_apply_zero _ _).symm rfl⟩

private def betweenSegment (a b : unitInterval)
    (ha : (segmentCurve x y e hseg a).val ∈ C.coefficientPoints)
    (hb : (segmentCurve x y e hseg b).val ∈ C.coefficientPoints) :
    (⟨(parameterPoint x y e hseg a ha).val.val, ha⟩ :
      WallComplement (fun P : C.walls => (P : Set V))) ⟶
      ⟨(parameterPoint x y e hseg b hb).val.val, hb⟩ :=
  ⟨e.down.subsegment a.property b.property rfl rfl⟩

variable (M : Type z) [MulAction H M]
  (s : (D.coefficientLocalSystem M).presheaf.obj (op U))

private noncomputable def normalizedValue
    (t : {t : unitInterval // (segmentCurve x y e hseg t).val ∈ C.coefficientPoints}) : M :=
  (D.pathProduct (initialSegment x y e hseg t.val t.property).toPath)⁻¹ •
    (D.coefficientTransport M).value s (parameterPoint x y e hseg t.val t.property)
      (segmentCurve x y e hseg t.val).property

private theorem normalizedValue_eq_of_le
    (a b : {t : unitInterval // (segmentCurve x y e hseg t).val ∈ C.coefficientPoints})
    (hab : a.val ≤ b.val)
    (hv : D.pathProduct (betweenSegment x y e hseg a.val b.val a.property b.property).toPath •
      (D.coefficientTransport M).value s (parameterPoint x y e hseg a.val a.property)
        (segmentCurve x y e hseg a.val).property =
      (D.coefficientTransport M).value s (parameterPoint x y e hseg b.val b.property)
        (segmentCurve x y e hseg b.val).property) :
    D.normalizedValue x y e hseg M s a = D.normalizedValue x y e hseg M s b := by
  have hp := D.pathProduct_prefix (y := ⟨y.val.val, y.property⟩)
    a.val.property b.val.property hab rfl rfl
    (initialSegment x y e hseg a.val a.property)
    (initialSegment x y e hseg b.val b.property)
    (betweenSegment x y e hseg a.val b.val a.property b.property)
  dsimp only [normalizedValue]
  rw [← hv, hp, mul_inv_rev, mul_smul, inv_smul_smul]

private theorem normalizedValue_eq_in_chart {B : Opens C.regularSpace}
    (hB : B ∈ C.coefficientCharts) (hBU : B ≤ U)
    (a b : {t : unitInterval // (segmentCurve x y e hseg t).val ∈ C.coefficientPoints})
    (ha : (segmentCurve x y e hseg a.val).val ∈ B)
    (hb : (segmentCurve x y e hseg b.val).val ∈ B) :
    D.normalizedValue x y e hseg M s a = D.normalizedValue x y e hseg M s b := by
  have hv (q r : {t : unitInterval //
      (segmentCurve x y e hseg t).val ∈ C.coefficientPoints})
      (hq : (segmentCurve x y e hseg q.val).val ∈ B)
      (hr : (segmentCurve x y e hseg r.val).val ∈ B) :
      D.pathProduct (betweenSegment x y e hseg q.val r.val q.property r.property).toPath •
        (D.coefficientTransport M).value s (parameterPoint x y e hseg q.val q.property)
          (segmentCurve x y e hseg q.val).property =
        (D.coefficientTransport M).value s (parameterPoint x y e hseg r.val r.property)
          (segmentCurve x y e hseg r.val).property := by
    have hv := D.coefficientLocalSystem_segment M hB le_rfl
      (C.coefficientChart_preconnected hB)
      ((D.coefficientLocalSystem M).presheaf.map (homOfLE hBU).op s)
      (parameterPoint x y e hseg q.val q.property)
      (parameterPoint x y e hseg r.val r.property) hq hr
    have hv' :
        D.pathProduct (C.coefficientSegment B hB
          (parameterPoint x y e hseg q.val q.property)
          (parameterPoint x y e hseg r.val r.property) hq hr).toPath •
          (D.coefficientTransport M).value
            ((D.coefficientTransport M).sheaf.presheaf.map (homOfLE hBU).op s)
            (parameterPoint x y e hseg q.val q.property) hq =
          (D.coefficientTransport M).value
            ((D.coefficientTransport M).sheaf.presheaf.map (homOfLE hBU).op s)
            (parameterPoint x y e hseg r.val r.property) hr := hv.symm
    -- Unfold the private point constructor to align the restriction endpoints.
    erw [(D.coefficientTransport M).value_restrict,
      (D.coefficientTransport M).value_restrict] at hv'
    have heq : C.coefficientSegment B hB
        (parameterPoint x y e hseg q.val q.property)
        (parameterPoint x y e hseg r.val r.property) hq hr =
        betweenSegment x y e hseg q.val r.val q.property r.property :=
      PLift.ext (Subsingleton.elim _ _)
    rwa [heq] at hv'
  by_cases hab : a.val ≤ b.val
  · exact D.normalizedValue_eq_of_le x y e hseg M s a b hab (hv a b ha hb)
  · exact (D.normalizedValue_eq_of_le x y e hseg M s b a
      (le_of_not_ge hab) (hv b a hb ha)).symm

private theorem normalizedValue_near (t : unitInterval) :
    ∃ m : M, ∀ᶠ a : {t : unitInterval //
      (segmentCurve x y e hseg t).val ∈ C.coefficientPoints}
      in Filter.comap Subtype.val (𝓝 t), D.normalizedValue x y e hseg M s a = m := by
  obtain ⟨B, hB, htB, hBU⟩ := Opens.isBasis_iff_nbhd.mp C.coefficientCharts_isBasis
    (segmentCurve x y e hseg t).property
  have ho : IsOpen {r : unitInterval | (segmentCurve x y e hseg r).val ∈ B} :=
    B.isOpen.preimage (continuous_subtype_val.comp (segmentCurve x y e hseg).continuous)
  obtain ⟨a, ha, haB⟩ := (dense_segment_parameters x y e hseg).exists_mem_open ho ⟨t, htB⟩
  refine ⟨D.normalizedValue x y e hseg M s ⟨a, ha⟩, ?_⟩
  have hn0 : ∀ᶠ r : unitInterval in 𝓝 t, (segmentCurve x y e hseg r).val ∈ B :=
    ho.mem_nhds htB
  have hn := hn0.comap
    (Subtype.val : {t : unitInterval //
      (segmentCurve x y e hseg t).val ∈ C.coefficientPoints} → unitInterval)
  filter_upwards [hn] with b hb
  exact D.normalizedValue_eq_in_chart x y e hseg M s hB hBU b ⟨a, ha⟩ hb haB

private theorem normalizedValue_eq
    (a b : {t : unitInterval // (segmentCurve x y e hseg t).val ∈ C.coefficientPoints}) :
    D.normalizedValue x y e hseg M s a = D.normalizedValue x y e hseg M s b := by
  let hd := (dense_segment_parameters x y e hseg).isDenseInducing_val.dense
  let k := LocallyConstant.extendOfDenseRange Subtype.val hd
    (D.normalizedValue x y e hseg M s) (D.normalizedValue_near x y e hseg M s)
  have hk (q : {t : unitInterval //
      (segmentCurve x y e hseg t).val ∈ C.coefficientPoints}) :
      k q.val = D.normalizedValue x y e hseg M s q :=
    LocallyConstant.extendOfDenseRange_apply _ _ _ _ q
  exact (hk a).symm.trans
    ((k.isLocallyConstant.apply_eq_of_preconnectedSpace a.val b.val).trans (hk b))

private theorem transport_between
    (a b : {t : unitInterval // (segmentCurve x y e hseg t).val ∈ C.coefficientPoints})
    (hab : a.val ≤ b.val) :
    D.pathProduct (betweenSegment x y e hseg a.val b.val a.property b.property).toPath •
      (D.coefficientTransport M).value s (parameterPoint x y e hseg a.val a.property)
        (segmentCurve x y e hseg a.val).property =
      (D.coefficientTransport M).value s (parameterPoint x y e hseg b.val b.property)
        (segmentCurve x y e hseg b.val).property := by
  have hp := D.pathProduct_prefix (y := ⟨y.val.val, y.property⟩)
    a.val.property b.val.property hab rfl rfl
    (initialSegment x y e hseg a.val a.property)
    (initialSegment x y e hseg b.val b.property)
    (betweenSegment x y e hseg a.val b.val a.property b.property)
  calc
    _ = D.pathProduct (initialSegment x y e hseg b.val b.property).toPath •
        D.normalizedValue x y e hseg M s a := by
      dsimp only [normalizedValue]
      rw [hp, mul_smul, smul_inv_smul]
    _ = D.pathProduct (initialSegment x y e hseg b.val b.property).toPath •
        D.normalizedValue x y e hseg M s b :=
      congrArg _ (D.normalizedValue_eq x y e hseg M s a b)
    _ = _ := smul_inv_smul _ _

include hx hy hseg in
/-- Every section obeys transport along any contained admissible segment.
The open domain need not be convex or contained in a single transport chart. -/
theorem coefficientLocalSystem_segment_of_subset :
    D.coefficientPathTransport M e.toPath ((D.coefficientTransport M).value s x hx) =
      (D.coefficientTransport M).value s y hy := by
  have hz : (segmentCurve x y e hseg 0).val ∈ C.coefficientPoints := by
    rw [segmentCurve_zero x y hx e hseg]
    exact x.property
  have ho : (segmentCurve x y e hseg 1).val ∈ C.coefficientPoints := by
    rw [segmentCurve_one x y hy e hseg]
    exact y.property
  have hv := D.transport_between x y e hseg M s ⟨0, hz⟩ ⟨1, ho⟩ bot_le
  let a : {q : C.coefficientPoints // q.val ∈ U} :=
    ⟨parameterPoint x y e hseg 0 hz, (segmentCurve x y e hseg 0).property⟩
  let b : {q : C.coefficientPoints // q.val ∈ U} :=
    ⟨parameterPoint x y e hseg 1 ho, (segmentCurve x y e hseg 1).property⟩
  have hv' : ∀ d : WallComplement.AdmissibleSegment
      (⟨a.val.val.val, a.val.property⟩ : WallComplement (fun P : C.walls => (P : Set V)))
      ⟨b.val.val.val, b.val.property⟩,
      D.pathProduct (Quiver.Hom.toPath (PLift.up d)) •
        (D.coefficientTransport M).value s a.val a.property =
        (D.coefficientTransport M).value s b.val b.property := by
    intro d
    have heq : betweenSegment x y e hseg 0 1 hz ho = PLift.up d :=
      PLift.ext (Subsingleton.elim _ _)
    rwa [heq] at hv
  have ha : a = ⟨x, hx⟩ :=
    by
      dsimp only [a, parameterPoint]
      exact Subtype.ext (Subtype.ext
        (congrArg (fun q : U => q.val) (segmentCurve_zero x y hx e hseg)))
  have hb : b = ⟨y, hy⟩ :=
    by
      dsimp only [b, parameterPoint]
      exact Subtype.ext (Subtype.ext
        (congrArg (fun q : U => q.val) (segmentCurve_one x y hy e hseg)))
  rw [ha, hb] at hv'
  cases e with
  | up he => simpa only [coefficientPathTransport_apply] using hv' he

end Segment

section Polygonal

variable {U : Opens C.regularSpace} (M : Type z) [MulAction H M]
  (s : (D.coefficientLocalSystem M).presheaf.obj (op U))

private theorem segment_transport_of_val_eq
    {a b : WallComplement (fun P : C.walls => (P : Set V))} (e : a ⟶ b)
    (x y : C.coefficientPoints) (hx : x.val ∈ U) (hy : y.val ∈ U)
    (ha : a.val = x.val.val) (hb : b.val = y.val.val)
    (hseg : segment ℝ a.val b.val ⊆ Subtype.val '' (U : Set C.regularSpace)) :
    D.pathProduct e.toPath • (D.coefficientTransport M).value s x hx =
      (D.coefficientTransport M).value s y hy := by
  have hxa : (⟨x.val.val, x.property⟩ :
      WallComplement (fun P : C.walls => (P : Set V))) = a := WallComplement.ext ha.symm
  have hyb : (⟨y.val.val, y.property⟩ :
      WallComplement (fun P : C.walls => (P : Set V))) = b := WallComplement.ext hb.symm
  have hs : ∀ d : WallComplement.AdmissibleSegment
      (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V)))
      ⟨y.val.val, y.property⟩,
      D.pathProduct (Quiver.Hom.toPath (PLift.up d)) •
        (D.coefficientTransport M).value s x hx =
        (D.coefficientTransport M).value s y hy := by
    intro d
    simpa only [coefficientPathTransport_apply] using
      D.coefficientLocalSystem_segment_of_subset x y hx hy (PLift.up d)
        (by simpa only [ha, hb] using hseg) M s
  rw [hxa, hyb] at hs
  cases e with
  | up he => exact hs he

private theorem path_transport_of_val_eq
    {a b : WallComplement (fun P : C.walls => (P : Set V))} (p : AdmissiblePLPath a b)
    (hpath : range p.toContinuousPath ⊆ Subtype.val '' (U : Set C.regularSpace))
    (x y : C.coefficientPoints) (hx : x.val ∈ U) (hy : y.val ∈ U)
    (ha : a.val = x.val.val) (hb : b.val = y.val.val) :
    D.pathProduct p • (D.coefficientTransport M).value s x hx =
      (D.coefficientTransport M).value s y hy := by
  induction p generalizing y with
  | nil =>
    have hxy : x = y := Subtype.ext (Subtype.ext (ha.symm.trans hb))
    subst y
    simp only [pathProduct_nil, one_smul]
  | @cons b c p e ih =>
    rw [Quiver.Path.toContinuousPath_cons, Path.trans_range] at hpath
    obtain ⟨z, hzU, hz⟩ := hpath (Or.inl p.toContinuousPath.target_mem_range)
    let z' : C.coefficientPoints := ⟨z, by
      intro P
      rw [hz]
      exact b.notMem P⟩
    have hp := ih (fun q hq => hpath (Or.inl hq)) z' hzU hz.symm
    have he := D.segment_transport_of_val_eq M s e z' y hzU hy hz.symm hb (by
      intro q hq
      exact hpath (Or.inr (by simpa only [Path.range_segment] using hq)))
    rw [pathProduct_cons, mul_smul, hp, he]

/-- A coefficient section relates its endpoint values by the original signed
transport along every admissible polygonal path contained in its open domain.
Neither the open nor the path need lie in a single convex chart. -/
theorem coefficientLocalSystem_path (x y : C.coefficientPoints)
    (hx : x.val ∈ U) (hy : y.val ∈ U)
    (p : AdmissiblePLPath
      (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V)))
      ⟨y.val.val, y.property⟩)
    (hpath : range p.toContinuousPath ⊆ Subtype.val '' (U : Set C.regularSpace)) :
    D.coefficientPathTransport M p ((D.coefficientTransport M).value s x hx) =
      (D.coefficientTransport M).value s y hy := by
  simpa only [coefficientPathTransport_apply] using
    D.path_transport_of_val_eq M s p hpath x y hx hy rfl rfl

end Polygonal

end Mei.FiniteWallDiagram
