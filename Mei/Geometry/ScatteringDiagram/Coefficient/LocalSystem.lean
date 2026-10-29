/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.Transport
public import Mei.Topology.Sheaves.DenseBasisTransport
public import Mei.Topology.Sheaves.LocallyConstant
public import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus

/-!
# The coefficient local system of a finite wall diagram

On the complement of singular support, convex open sets carry coherent segment
transport. Their off-wall points are dense, and the segment cocycle makes their
locally parallel coefficients into a sheaf on the entire regular locus, including
regular wall points. Its sections are recorded only off the walls. Evaluation on
a preconnected subopen of a convex chart identifies its sections with the
coefficient type, proving local constancy without global consistency of the diagram.

We use `coefficientPathTransport_triangle` and `DenseBasisTransport.sheaf`, whose
local-predicate construction is Mathlib's `PrelocalPredicate.sheafify`. The wall
transport interpretation follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Set Topology Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V H : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {C : FinitePolyhedralComplex h}
  [Group H] (D : FiniteWallDiagram C H) (M : Type*) [MulAction H M]

/-- The coefficient representation as coherent transport on the dense off-wall
part of the regular locus. The first crossing acts first. -/
def coefficientTransport : DenseBasisTransport C.coefficientPoints M where
  dense := C.dense_coefficientPoints
  basis := C.coefficientCharts
  isBasis := C.coefficientCharts_isBasis
  transport U hU x y hx hy :=
    D.coefficientPathTransport M (C.coefficientSegment U hU x y hx hy).toPath
  transport_trans U hU x y z hx hy hz := by
    apply D.coefficientPathTransport_triangle M
    apply Set.disjoint_left.mpr
    intro q hq hsing
    have hqU : q ∈ Subtype.val '' (U : Set C.regularSpace) :=
      convexHull_min (by
        intro a ha
        simp only [mem_insert_iff, mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · exact ⟨x.val, hx, rfl⟩
        · exact ⟨y.val, hy, rfl⟩
        · exact ⟨z.val, hz, rfl⟩) ((C.mem_coefficientCharts U).mp hU) hq
    obtain ⟨q, _, rfl⟩ := hqU
    exact q.property hsing
  transport_restrict {U V} hU hV hUV x y hx hy := by
    have he : C.coefficientSegment U hU x y hx hy =
        C.coefficientSegment V hV x y (hUV hx) (hUV hy) := by
      apply PLift.ext
      rfl
    exact congrArg (D.coefficientPathTransport M) (congrArg Quiver.Hom.toPath he)

/-- The represented basis is precisely the convex regular opens. -/
@[simp]
theorem coefficientTransport_basis : (D.coefficientTransport M).basis = C.coefficientCharts :=
  (rfl)

/-- Local transport computes the original signed path-product action. -/
@[simp]
theorem coefficientTransport_transport (U : Opens C.regularSpace)
    (hU : U ∈ C.coefficientCharts) (x y : C.coefficientPoints)
    (hx : x.val ∈ U) (hy : y.val ∈ U) :
    (D.coefficientTransport M).transport U (by simpa using hU) x y hx hy =
      D.coefficientPathTransport M (C.coefficientSegment U hU x y hx hy).toPath := (rfl)

/-- The sheaf of locally parallel coefficient functions on the regular locus.
Only off-wall values are recorded; the local equations impose wall crossing. -/
abbrev coefficientLocalSystem : C.regularSpace.Sheaf (Type _) :=
  (D.coefficientTransport M).sheaf

/-- On a preconnected subopen of a convex regular chart, sections obey the
signed segment-transport equation, including when that segment crosses a wall. -/
theorem coefficientLocalSystem_segment {B U : Opens C.regularSpace}
    (hB : B ∈ C.coefficientCharts) (hUB : U ≤ B) (hcU : IsPreconnected (U : Set C.regularSpace))
    (s : (D.coefficientLocalSystem M).presheaf.obj (op U))
    (x y : C.coefficientPoints) (hx : x.val ∈ U) (hy : y.val ∈ U) :
    (D.coefficientTransport M).value s y hy =
      D.pathProduct (C.coefficientSegment B hB x y (hUB hx) (hUB hy)).toPath •
        (D.coefficientTransport M).value s x hx := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hcU
  have hp := (D.coefficientTransport M).parallel_of_le hB hUB s x y hx hy
  rw [D.coefficientTransport_transport M B hB x y (hUB hx) (hUB hy)] at hp
  simpa only [coefficientPathTransport_apply] using hp.symm

/-- Every regular point has a neighborhood with bijective restrictions to
nonempty preconnected opens. No global consistency hypothesis is needed. -/
instance coefficientLocalSystem_hasLocallyBijectivePreconnectedRestrictions :
    (D.coefficientLocalSystem M).HasLocallyBijectivePreconnectedRestrictions where
  exists_bijective_restrictions x := by
    obtain ⟨B, hB, hxB, _⟩ := Opens.isBasis_iff_nbhd.mp C.coefficientCharts_isBasis
      (Opens.mem_top x)
    exact ⟨B, hxB, fun V hVB hne hcV =>
      (D.coefficientTransport M).restriction_bijective hB le_rfl
        (C.coefficientChart_preconnected hB) hVB hne hcV⟩

end Mei.FiniteWallDiagram
