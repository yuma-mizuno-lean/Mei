/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel
public import Mei.Geometry.Convex.Polyhedron.Path.Comparison

/-!
# Detecting completed KS equivalence by regular germs

For abelian ray algebras, two completed KS diagrams are equivalent exactly when
their completed local labels agree at every point regular for both sequences of
complexes. The complexes may change at every cutoff, and consistency is not needed.
Thus recovering the regular germs of an indexed presentation suffices to recover
the original completed diagram up to equivalence.

The proof compares simultaneous crossing products on all-order segments, then uses
`CompletedDiagram.equivalent_of_pathProduct_eq` to recover arbitrary finite tests.
It reuses `CompletedDiagram.germLabel`, the uniqueness of the supported ray of a
nonidentity finite label, and `Quiver.Path.weight_eq_of_map_vertices_eq`.
The germ interpretation follows Bridgeland, *Scattering diagrams, Hall algebras
and stability conditions*, Definition 2.3 and §§2–3 (arXiv:1603.00416v4), and
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex WallComplement

namespace Mei

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [Module.Free ℤ N] [IsAbelianRays d ℒ]

namespace KSComplex

variable {C E : FinitePolyhedralComplex h} {k : ℕ}
  (D : KSComplex s d ℒ C k) (F : KSComplex s d ℒ E k)

private theorem crossingEventProduct_eq_of_localLabel_eq
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    {x' y' : WallComplement (fun P : E.walls => (P : Set V))}
    (e : x ⟶ y) (e' : x' ⟶ y') (hx : x.val = x'.val) (hy : y.val = y'.val)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hlabel : D.localLabel (AffineMap.lineMap x.val y.val t) (e.down.regular t ht) =
      F.localLabel (AffineMap.lineMap x'.val y'.val t) (e'.down.regular t ht)) :
    crossingEventProduct (fun P => s.normal (D.degree P)) D.label
        D.commute_label_of_affineSpan_eq e t =
      crossingEventProduct (fun P => s.normal (F.degree P)) F.label
        F.commute_label_of_affineSpan_eq e' t := by
  classical
  have empty_event {B : FinitePolyhedralComplex h} (A : KSComplex s d ℒ B k)
      {u v : WallComplement (fun P : B.walls => (P : Set V))} (a : u ⟶ v)
      (hmiss : ∀ P : B.walls, AffineMap.lineMap u.val v.val t ∉ (P : Set V)) :
      signedCrossingEvent (fun P => s.normal (A.degree P)) u v t = ∅ := by
    ext ⟨P, z⟩
    simp only [mem_signedCrossingEvent, mem_crossings, Finset.notMem_empty, iff_false]
    exact fun hP => hmiss P hP.1.2
  by_cases hP : ∃ P : C.walls, AffineMap.lineMap x.val y.val t ∈ (P : Set V)
  · obtain ⟨P, hP⟩ := hP
    rw [D.localLabel_of_mem _ _ P hP] at hlabel
    rw [crossingEventProduct_singleton _ _ _ e t _
      (C.signedCrossingEvent_eq_singleton _ e ((mem_crossings _ _ _ _).mpr ⟨ht, hP⟩))]
    by_cases hQ : ∃ Q : E.walls, AffineMap.lineMap x'.val y'.val t ∈ (Q : Set V)
    · obtain ⟨Q, hQ⟩ := hQ
      rw [F.localLabel_of_mem _ _ Q hQ] at hlabel
      rw [crossingEventProduct_singleton _ _ _ e' t _
        (E.signedCrossingEvent_eq_singleton _ e' ((mem_crossings _ _ _ _).mpr ⟨ht, hQ⟩))]
      by_cases hzero : D.label P = 1
      · simp [← hlabel, hzero]
      · have hsign := D.normal_pos_iff_of_label_eq F P Q hzero hlabel (y.val - x.val)
        simp only [← hx, ← hy, ← hsign, hlabel]
    · have hmiss : ∀ Q : E.walls, AffineMap.lineMap x'.val y'.val t ∉ (Q : Set V) := by
        simpa using hQ
      rw [F.localLabel_of_notMem _ _ hmiss] at hlabel
      rw [crossingEventProduct_empty _ _ _ e' t (empty_event F e' hmiss)]
      simp [hlabel]
  · have hmiss : ∀ P : C.walls, AffineMap.lineMap x.val y.val t ∉ (P : Set V) := by
      simpa using hP
    rw [D.localLabel_of_notMem _ _ hmiss] at hlabel
    rw [crossingEventProduct_empty _ _ _ e t (empty_event D e hmiss)]
    by_cases hQ : ∃ Q : E.walls, AffineMap.lineMap x'.val y'.val t ∈ (Q : Set V)
    · obtain ⟨Q, hQ⟩ := hQ
      rw [F.localLabel_of_mem _ _ Q hQ] at hlabel
      rw [crossingEventProduct_singleton _ _ _ e' t _
        (E.signedCrossingEvent_eq_singleton _ e' ((mem_crossings _ _ _ _).mpr ⟨ht, hQ⟩))]
      simp [← hlabel]
    · exact (crossingEventProduct_empty _ _ _ e' t
        (empty_event F e' (by simpa using hQ))).symm

end KSComplex

namespace CompletedDiagram

variable {C E : ℕ → FinitePolyhedralComplex h}
  (D : CompletedDiagram s d ℒ C) (F : CompletedDiagram s d ℒ E)

private theorem projection_pathProduct_eq_weight (k : ℕ) {x y : Point C}
    (p : Quiver.Path x y) :
    CompletedGroup.projection k (D.pathProduct p) = MulOpposite.unop
      (p.weight fun e => MulOpposite.op (segmentPathProduct
        (fun P => s.normal ((D.diagram k).degree P)) (D.diagram k).label
        (D.diagram k).commute_label_of_affineSpan_eq
        ((CommonWallComplement.projectionPrefunctor k).map e))) := by
  let A := (D.diagram k).toFiniteWallDiagram
  rw [projection_pathProduct, A.pathProduct_eq_wallPathProduct
    (fun a b hab => by simpa only [A, KSComplex.toFiniteWallDiagram_label] using
      (D.diagram k).commute_label_of_affineSpan_eq a b hab)]
  -- The final reflexivity steps identify tower operations with the concrete BCH operations.
  induction p with
  | nil =>
      simp only [Prefunctor.mapPath_nil, Quiver.Path.wallPathProduct_nil,
        Quiver.Path.weight_nil, MulOpposite.unop_one]
      rfl
  | cons p e ih =>
      simp only [Prefunctor.mapPath_cons, Quiver.Path.wallPathProduct_cons,
        Quiver.Path.weight_cons, MulOpposite.unop_mul, ih]
      simp only [A, funext (D.diagram k).toFiniteWallDiagram_normal,
        funext (D.diagram k).toFiniteWallDiagram_label, MulOpposite.unop_op]
      rfl

/-- Equality of regular completed germs determines the equivalence class of an
abelian-ray KS diagram. Only points regular at every cutoff of both diagrams
need to be tested. -/
theorem equivalent_of_germLabel_eq
    (hlabel : ∀ θ
      (hD : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V)))
      (hF : ∀ k, θ ∉ singularSupport (fun P : (E k).walls => (P : Set V))),
      D.germLabel θ hD = F.germLabel θ hF) : D.Equivalent F := by
  apply D.equivalent_of_pathProduct_eq F
  intro x y x' y' p q hpq
  apply CompletedGroup.ext
  intro k
  let wD {u v : Point C} (e : u ⟶ v) := MulOpposite.op
    (segmentPathProduct (fun P => s.normal ((D.diagram k).degree P)) (D.diagram k).label
      (D.diagram k).commute_label_of_affineSpan_eq
      ((CommonWallComplement.projectionPrefunctor k).map e))
  let wF {u v : Point E} (e : u ⟶ v) := MulOpposite.op
    (segmentPathProduct (fun P => s.normal ((F.diagram k).degree P)) (F.diagram k).label
      (F.diagram k).commute_label_of_affineSpan_eq
      ((CommonWallComplement.projectionPrefunctor k).map e))
  rw [D.projection_pathProduct_eq_weight k p, F.projection_pathProduct_eq_weight k q]
  apply congrArg MulOpposite.unop
  refine p.weight_eq_of_map_vertices_eq q CommonWallComplement.val CommonWallComplement.val
    wD wF ?_ hpq
  intro u v u' v' e e' hu hv
  apply congrArg MulOpposite.op
  apply segmentPathProduct_eq_of_crossingEventProduct_eq
  intro t ht
  apply (D.diagram k).crossingEventProduct_eq_of_localLabel_eq (F.diagram k) _ _ hu hv ht
  have hregD (l : ℕ) := (e.down l).regular t ht
  have hregF (l : ℕ) := (e'.down l).regular t ht
  have hg := congrArg (CompletedGroup.projection k)
    (hlabel (AffineMap.lineMap u.val v.val t) hregD (by
      simpa only [CommonWallComplement.projection_val, hu, hv] using hregF))
  -- Tower projections use the categorical carrier of the same concrete BCH quotient.
  convert hg using 1 <;> first
    | rfl
    | (simp only [projection_germLabel, CommonWallComplement.projectionPrefunctor_obj,
        CommonWallComplement.projection_val, hu, hv]; rfl)

/-- For abelian rays, equality of all common regular completed germs is
equivalent to equality of path products at every finite order. -/
theorem equivalent_iff_germLabel_eq : D.Equivalent F ↔
    ∀ θ
      (hD : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V)))
      (hF : ∀ k, θ ∉ singularSupport (fun P : (E k).walls => (P : Set V))),
      D.germLabel θ hD = F.germLabel θ hF := by
  constructor
  · intro hDF θ hD hF
    exact D.germLabel_eq_of_equivalent θ hD F hDF hF
  · exact D.equivalent_of_germLabel_eq F

end CompletedDiagram
end Mei
