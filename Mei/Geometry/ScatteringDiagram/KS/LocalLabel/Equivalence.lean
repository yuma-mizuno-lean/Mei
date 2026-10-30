/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel
public import Mei.Combinatorics.Quiver.Path
import Mei.Algebra.BigOperators.Group.Finset.Ordered

/-!
# Detecting completed KS equivalence by regular germs

Two completed KS diagrams are equivalent exactly when
their completed local labels agree at every point regular for both sequences of
complexes. The complexes may change at every cutoff, and consistency is not needed.
Thus recovering the regular germs of an indexed presentation suffices to recover
the original completed diagram up to equivalence.

The proof compares ordered crossing products on all-order segments, inserting identity
factors over the union of crossing times, then uses
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
  [Module.Free ℤ N]

namespace KSComplex

variable {C E : FinitePolyhedralComplex h} {k : ℕ}
  (D : KSComplex s d ℒ C k) (F : KSComplex s d ℒ E k)

open Classical in
private def crossingFactor
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (_e : x ⟶ y) (t : ℝ) : d.truncatedGroup ℒ k :=
  if hp : ∃ P : C.walls, (P, t) ∈ crossings x y then
    if 0 < s.normal (D.degree hp.choose) (y.val - x.val) then
      (D.label hp.choose)⁻¹ else D.label hp.choose
  else 1

omit [Module.Free ℤ N] in
private theorem crossingFactor_of_mem
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (e : x ⟶ y) {t : ℝ} (P : C.walls) (hP : (P, t) ∈ crossings x y) :
    D.crossingFactor e t =
      if 0 < s.normal (D.degree P) (y.val - x.val) then (D.label P)⁻¹ else D.label P := by
  classical
  have hp : ∃ Q : C.walls, (Q, t) ∈ crossings x y := ⟨P, hP⟩
  have heq : hp.choose = P := congrArg (fun a => a.val.1)
    (C.crossing_time_injective e (a₁ := ⟨(_, t), hp.choose_spec⟩)
      (a₂ := ⟨(P, t), hP⟩) rfl)
  simp only [crossingFactor, dite_eq_left hp, heq]

omit [Module.Free ℤ N] in
private theorem crossingFactor_of_notMem
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (e : x ⟶ y) {t : ℝ} (ht : t ∉ orderedCrossingTimes e) :
    D.crossingFactor e t = 1 := by
  classical
  exact dite_eq_right (fun hp => ht ((mem_orderedCrossingTimes e t).mpr hp))

private theorem crossingFactor_eq_of_localLabel_eq
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    {x' y' : WallComplement (fun P : E.walls => (P : Set V))}
    (e : x ⟶ y) (e' : x' ⟶ y') (hx : x.val = x'.val) (hy : y.val = y'.val)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hlabel : D.localLabel (AffineMap.lineMap x.val y.val t) (e.down.regular t ht) =
      F.localLabel (AffineMap.lineMap x'.val y'.val t) (e'.down.regular t ht)) :
    D.crossingFactor e t = F.crossingFactor e' t := by
  classical
  by_cases hP : ∃ P : C.walls, (P, t) ∈ crossings x y
  · obtain ⟨P, hP⟩ := hP
    rw [D.localLabel_of_mem _ _ P ((mem_crossings _ _ _ _).mp hP).2] at hlabel
    rw [D.crossingFactor_of_mem e P hP]
    by_cases hQ : ∃ Q : E.walls, (Q, t) ∈ crossings x' y'
    · obtain ⟨Q, hQ⟩ := hQ
      rw [F.localLabel_of_mem _ _ Q ((mem_crossings _ _ _ _).mp hQ).2] at hlabel
      rw [F.crossingFactor_of_mem e' Q hQ]
      by_cases hzero : D.label P = 1
      · simp [← hlabel, hzero]
      · have hsign := D.normal_pos_iff_of_label_eq F P Q hzero hlabel (y.val - x.val)
        simp only [← hx, ← hy, ← hsign, hlabel]
    · have hmiss : ∀ Q : E.walls, AffineMap.lineMap x'.val y'.val t ∉ (Q : Set V) := by
        intro Q hQ'
        exact hQ ⟨Q, (mem_crossings _ _ _ _).mpr ⟨ht, hQ'⟩⟩
      rw [F.localLabel_of_notMem _ _ hmiss] at hlabel
      rw [F.crossingFactor_of_notMem e' (by simpa only [mem_orderedCrossingTimes] using hQ)]
      simp [hlabel]
  · have hmiss : ∀ P : C.walls, AffineMap.lineMap x.val y.val t ∉ (P : Set V) := by
      intro P hP'
      exact hP ⟨P, (mem_crossings _ _ _ _).mpr ⟨ht, hP'⟩⟩
    rw [D.localLabel_of_notMem _ _ hmiss] at hlabel
    rw [D.crossingFactor_of_notMem e (by simpa only [mem_orderedCrossingTimes] using hP)]
    by_cases hQ : ∃ Q : E.walls, (Q, t) ∈ crossings x' y'
    · obtain ⟨Q, hQ⟩ := hQ
      rw [F.localLabel_of_mem _ _ Q ((mem_crossings _ _ _ _).mp hQ).2] at hlabel
      rw [F.crossingFactor_of_mem e' Q hQ]
      simp [← hlabel]
    · exact (F.crossingFactor_of_notMem e'
        (by simpa only [mem_orderedCrossingTimes] using hQ)).symm

omit [Module.Free ℤ N] in
private theorem pathProduct_toPath_eq_prod
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (e : x ⟶ y) (T : Finset ℝ)
    (hcover : ∀ t ∈ orderedCrossingTimes e, t ∈ T) :
    D.toFiniteWallDiagram.pathProduct e.toPath =
      (T.sort.reverse.map (D.crossingFactor e)).prod := by
  classical
  have htimes : (C.orderedCrossings e).map Prod.snd = orderedCrossingTimes e := by
    apply (List.pairwise_map.mpr (C.pairwise_orderedCrossings e)).eq_of_mem_iff
      (pairwise_orderedCrossingTimes e)
    intro t
    simp only [List.mem_map, mem_orderedCrossingTimes]
    constructor
    · rintro ⟨⟨P, u⟩, hP, rfl⟩
      exact ⟨P, (C.mem_orderedCrossings e _).mp hP⟩
    · rintro ⟨P, hP⟩
      exact ⟨(P, t), (C.mem_orderedCrossings e _).mpr hP, rfl⟩
  have hprod : D.toFiniteWallDiagram.pathProduct e.toPath =
      ((orderedCrossingTimes e).reverse.map (D.crossingFactor e)).prod := by
    rw [FiniteWallDiagram.pathProduct_toPath, ← htimes]
    simp only [List.map_reverse, List.map_map, Function.comp_def]
    apply congrArg List.prod
    apply congrArg List.reverse
    apply List.map_congr_left
    intro a ha
    simpa only [toFiniteWallDiagram_normal, toFiniteWallDiagram_label] using
      (D.crossingFactor_of_mem e a.1 ((C.mem_orderedCrossings e a).mp ha)).symm
  have hsort : (orderedCrossingTimes e).toFinset.sort = orderedCrossingTimes e :=
    (Finset.sortedLT_sort _).pairwise.eq_of_mem_iff (pairwise_orderedCrossingTimes e) (by simp)
  rw [hprod]
  simp only [List.map_reverse, List.prod_reverse_noncomm, List.map_map, Function.comp_def]
  apply congrArg Inv.inv
  simpa only [hsort] using Finset.prod_map_sort_subset
    (s := (orderedCrossingTimes e).toFinset) (t := T)
    (fun t ht => hcover t (List.mem_toFinset.mp ht))
    (fun t => (D.crossingFactor e t)⁻¹)
    (fun t _ ht => by rw [D.crossingFactor_of_notMem e (by simpa using ht), inv_one])

end KSComplex

namespace CompletedDiagram

variable {C E : ℕ → FinitePolyhedralComplex h}
  (D : CompletedDiagram s d ℒ C) (F : CompletedDiagram s d ℒ E)

omit [Module.Free ℤ N] in
private theorem projection_pathProduct_eq_weight (k : ℕ) {x y : Point C}
    (p : Quiver.Path x y) :
    CompletedGroup.projection k (D.pathProduct p) = MulOpposite.unop
      (p.weight fun e => MulOpposite.op ((D.diagram k).toFiniteWallDiagram.pathProduct
        (((CommonWallComplement.projectionPrefunctor k).map e).toPath))) := by
  rw [projection_pathProduct]
  -- Tower operations and the concrete BCH operations are definitionally equal.
  induction p with
  | nil =>
      simp only [Prefunctor.mapPath_nil, FiniteWallDiagram.pathProduct_nil,
        Quiver.Path.weight_nil, MulOpposite.unop_one]
      rfl
  | cons p e ih =>
      simp only [Prefunctor.mapPath_cons, FiniteWallDiagram.pathProduct_cons,
        Quiver.Path.weight_cons, MulOpposite.unop_mul, ih, MulOpposite.unop_op]
      rfl

/-- Equality of regular completed germs determines the equivalence class of a
KS diagram. Only points regular at every cutoff of both diagrams
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
    ((D.diagram k).toFiniteWallDiagram.pathProduct
      (((CommonWallComplement.projectionPrefunctor k).map e).toPath))
  let wF {u v : Point E} (e : u ⟶ v) := MulOpposite.op
    ((F.diagram k).toFiniteWallDiagram.pathProduct
      (((CommonWallComplement.projectionPrefunctor k).map e).toPath))
  rw [D.projection_pathProduct_eq_weight k p, F.projection_pathProduct_eq_weight k q]
  apply congrArg MulOpposite.unop
  refine p.weight_eq_of_map_vertices_eq q CommonWallComplement.val CommonWallComplement.val
    wD wF ?_ hpq
  intro u v u' v' e e' hu hv
  apply congrArg MulOpposite.op
  let a := (CommonWallComplement.projectionPrefunctor k).map e
  let b := (CommonWallComplement.projectionPrefunctor k).map e'
  let T := (orderedCrossingTimes a).toFinset ∪ (orderedCrossingTimes b).toFinset
  rw [(D.diagram k).pathProduct_toPath_eq_prod a T
      (fun t ht => Finset.mem_union_left _ (List.mem_toFinset.mpr ht)),
    (F.diagram k).pathProduct_toPath_eq_prod b T
      (fun t ht => Finset.mem_union_right _ (List.mem_toFinset.mpr ht))]
  congr 1
  apply List.map_congr_left
  intro t ht
  have ht : t ∈ orderedCrossingTimes a ∨ t ∈ orderedCrossingTimes b := by
    simpa only [T, List.mem_reverse, Finset.mem_sort, Finset.mem_union, List.mem_toFinset] using ht
  have ht : t ∈ Icc (0 : ℝ) 1 := ht.elim
    (fun ht => Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes a ht))
    (fun ht => Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes b ht))
  apply (D.diagram k).crossingFactor_eq_of_localLabel_eq (F.diagram k) a b hu hv ht
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

/-- Equality of all common regular completed germs is
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
