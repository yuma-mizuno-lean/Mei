/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.LocalSystem

/-!
# Transport of coefficient sections along polygonal paths

A section of the coefficient local system obeys transport along every admissible
segment contained in its open domain, without requiring the domain itself to lie
in a single convex chart. Use `coefficientLocalSystem_segment_of_subset` to compute the value
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

variable (M : Type z) [MulAction H M]
  (s : (D.coefficientLocalSystem M).presheaf.obj (op U))

include hx hy hseg in
/-- Every section obeys transport along any contained admissible segment.
The open domain need not be convex or contained in a single transport chart. -/
theorem coefficientLocalSystem_segment_of_subset :
    D.coefficientPathTransport M e.toPath ((D.coefficientTransport M).value s x hx) =
      (D.coefficientTransport M).value s y hy := by
  -- Thicken the compact segment to a convex transport chart inside the domain.
  have ho : IsOpen (Subtype.val '' (U : Set C.regularSpace)) :=
    C.isOpen_regularLocus.isOpenMap_subtype_val _ U.isOpen
  have hs : IsCompact (segment ℝ x.val.val y.val.val) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨δ, hδ, hδU⟩ := hs.exists_thickening_subset_open ho hseg
  let B : Opens C.regularSpace :=
    ⟨Subtype.val ⁻¹' Metric.thickening δ (segment ℝ x.val.val y.val.val),
      Metric.isOpen_thickening.preimage continuous_subtype_val⟩
  have hBimage : Subtype.val '' (B : Set C.regularSpace) =
      Metric.thickening δ (segment ℝ x.val.val y.val.val) :=
    Set.image_preimage_eq_of_subset (hδU.trans (Set.image_subset_range _ _))
  have hB : B ∈ C.coefficientCharts := by
    rw [C.mem_coefficientCharts, hBimage]
    exact (convex_segment x.val.val y.val.val).thickening δ
  have hBU : B ≤ U := by
    intro q hq
    obtain ⟨r, hr, heq⟩ := hδU hq
    exact (Subtype.ext heq) ▸ hr
  have hxB : x.val ∈ B := Metric.self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
  have hyB : y.val ∈ B := Metric.self_subset_thickening hδ _ (right_mem_segment ℝ _ _)
  have hv := D.coefficientLocalSystem_segment M hB le_rfl
    (C.coefficientChart_preconnected hB)
    ((D.coefficientLocalSystem M).presheaf.map (homOfLE hBU).op s) x y hxB hyB
  rw [(D.coefficientTransport M).value_restrict,
    (D.coefficientTransport M).value_restrict] at hv
  have heq : C.coefficientSegment B hB x y hxB hyB = e :=
    PLift.ext (Subsingleton.elim _ _)
  simpa only [heq, coefficientPathTransport_apply] using hv.symm

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
