/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction.Completion
public import Mei.Geometry.ScatteringDiagram.KS.Equivalence

/-!
# Consistent KS diagrams are reconstructions

Every consistent completed KS diagram is equivalent to the middle-factor
reconstruction of its transport from the positive degree point to the negative one.
Consequently two consistent completed diagrams are equivalent exactly when these
transports agree, and each consistent diagram is equivalent to the reconstruction of
a unique completed BCH element.

The finite input is a sign computation for an arbitrary KS complex. A wall crossed at
a point `c` of a segment from `v` to `y`, where every retained degree is positive at
`v`, has a label supported on degrees vanishing at `c`, and these are negative at `y`.
Starting the segment at a generic point `v` of the open set where every retained degree
is positive, the product from the positive side to `y` lies in the negative sign subgroup
at `y`. Symmetrically, the product from `y` to the negative side lies in the positive
sign subgroup. In a consistent complex the chamber transport is therefore their ordered
product, and uniqueness of sign factorization identifies the product to `y` with the
negative factor of the chamber transport at `y`. Every path product is then the quotient
of these negative factors at its endpoints, which is also the path product of the
reconstruction.

This is the classification of consistent diagrams by their chamber transport in
Tom Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, §3,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416). It uses `PositiveDegrees.signFactorizationEquiv`, the orthogonal wall labels of
`KSComplex`, Mei's generic two-segment paths
`Mei.Convex.exists_mem_open_two_transverse_lineMaps`, and the reconstruction
`PositiveDegrees.reconstruct`. No finite generation of the positive monoid is needed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei

namespace KSComplex

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {C : FinitePolyhedralComplex h} {k : ℕ} (D : KSComplex s d ℒ C k)

/-- A wall label lies in the sign subgroup of `σ` for `φ` as soon as every retained
nonzero degree vanishing at one point of the wall has sign `σ` under `φ`. -/
theorem label_mem_bchSubgroup_signSubalgebra (P : C.walls) {θ : V}
    (hθ : θ ∈ (P : Set V)) {φ : N →+ ℝ} {σ : SignType}
    (hφ : ∀ n ∈ d.cutoff k \ {0}, s.evaluation θ n = 0 → SignType.sign (φ n) = σ) :
    D.label P ∈ (signSubalgebra (d.truncatedGrading ℒ k) φ σ).bchSubgroup := by
  refine LieSubalgebra.bchSubgroup_le_bchSubgroup.mpr ?_ (D.label_mem P)
  intro x hx
  rw [mem_orthogonalLieSubalgebra_iff] at hx
  rw [mem_signSubalgebra_iff]
  intro n hn
  by_cases hb : d.truncatedGrading ℒ k n = ⊥
  · simpa only [hb, Submodule.mem_bot] using
      (DirectSum.decompose (d.truncatedGrading ℒ k) x n).property
  · exact hx _ ⟨θ, hθ, rfl⟩ n fun h0 =>
      hn (hφ n (d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hb) h0)

/-- If a segment from a point of nonzero sign `σ` vanishes before its endpoint, then
the endpoint has the opposite sign. -/
private theorem sign_eq_neg_of_lineMap_eq_zero {σ : SignType} (hσ : σ ≠ 0) {a b t : ℝ}
    (ha : SignType.sign a = σ) (ht : t ∈ Icc (0 : ℝ) 1) (ht1 : t ≠ 1)
    (hz : (1 - t) * a + t * b = 0) : SignType.sign b = -σ := by
  have hpos : 0 < 1 - t := sub_pos.2 (lt_of_le_of_ne ht.2 ht1)
  rcases σ with _ | _ | _
  · exact (hσ rfl).elim
  · have ha' : a < 0 := sign_eq_neg_one_iff.mp ha
    exact sign_eq_one_iff.mpr (by nlinarith [mul_neg_of_pos_of_neg hpos ha', ht.1])
  · have ha' : 0 < a := sign_eq_one_iff.mp ha
    exact sign_eq_neg_one_iff.mpr (by nlinarith [mul_pos hpos ha', ht.1])

/-- Starting where every retained nonzero degree has the nonzero sign `σ`, every
allowed point `y` is reached by an admissible path whose product lies in the sign
subgroup of `-σ` at `y`. -/
theorem exists_pathProduct_mem_bchSubgroup_signSubalgebra {σ : SignType} (hσ : σ ≠ 0)
    {x : WallComplement (fun P : C.walls => (P : Set V))}
    (hx : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (s.evaluation x.val n) = σ)
    (y : WallComplement (fun P : C.walls => (P : Set V))) :
    ∃ p : AdmissiblePLPath x y, D.toFiniteWallDiagram.pathProduct p ∈
      (signSubalgebra (d.truncatedGrading ℒ k) (s.evaluation y.val) (-σ)).bchSubgroup := by
  let := h.finiteDimensional
  have heval (u v : V) (t : ℝ) (n : N) : s.evaluation (AffineMap.lineMap u v t) n =
      (1 - t) * s.evaluation u n + t * s.evaluation v n := by
    simp [AffineMap.lineMap_apply_module]
  -- The open convex region where every retained degree has sign `σ`.
  let U : Set V := {θ | ∀ n ∈ d.cutoff k \ {0}, SignType.sign (s.evaluation θ n) = σ}
  have hσU : IsOpen {a : ℝ | SignType.sign a = σ} ∧ Convex ℝ {a : ℝ | SignType.sign a = σ} := by
    rcases σ with _ | _ | _
    · exact (hσ rfl).elim
    · have he : {a : ℝ | SignType.sign a = SignType.neg} = Iio 0 := by
        ext a
        exact sign_eq_neg_one_iff
      rw [he]
      exact ⟨isOpen_Iio, convex_Iio 0⟩
    · have he : {a : ℝ | SignType.sign a = SignType.pos} = Ioi 0 := by
        ext a
        exact sign_eq_one_iff
      rw [he]
      exact ⟨isOpen_Ioi, convex_Ioi 0⟩
  have hUeq : U = ⋂ n ∈ d.cutoff k \ {0}, s.normal n ⁻¹' {a | SignType.sign a = σ} := by
    ext θ
    simp [U]
  have hU : IsOpen U := by
    rw [hUeq]
    exact (d.finite_cutoff k).sdiff.isOpen_biInter fun n _ =>
      hσU.1.preimage (s.normal n).continuous_of_finiteDimensional
  have hUc : Convex ℝ U := by
    rw [hUeq]
    exact convex_iInter₂ fun n _ => hσU.2.linear_preimage (s.normal n)
  obtain ⟨v, hvU, hv, htrans, hreg⟩ := exists_mem_open_two_transverse_lineMaps
    (fun P : C.walls => (P : Set V))
    (fun P => C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property))
    (fun P => C.finrank_direction_add_one_of_mem_walls P.property) x.notMem y.notMem
    hU ⟨x.val, hx⟩
  let z : WallComplement (fun P : C.walls => (P : Set V)) := ⟨v, hv⟩
  have hxz : WallComplement.AdmissibleSegment x z :=
    ⟨fun P _ => (htrans P).1, fun t _ => (hreg t).1⟩
  have hyz : WallComplement.AdmissibleSegment y z :=
    ⟨fun P _ => (htrans P).2, fun t _ => (hreg t).2⟩
  refine ⟨((Quiver.Path.nil : AdmissiblePLPath x x).cons (PLift.up hxz)).cons
    (PLift.up hyz.symm), D.toFiniteWallDiagram.pathProduct_mem _ ?_⟩
  rintro ⟨j, P, t⟩ hj
  simp only [Quiver.Path.mem_crossingEvents_cons, Quiver.Path.crossingEvents_nil,
    Set.mem_empty_iff_false, false_or, WallComplement.mem_crossings] at hj
  rw [toFiniteWallDiagram_label]
  rcases hj with ⟨-, ht, hP⟩ | ⟨-, ht, hP⟩
  · -- On the first segment no retained degree vanishes, since `U` is convex.
    refine D.label_mem_bchSubgroup_signSubalgebra P hP fun n hn h0 => ?_
    have hs := hUc.lineMap_mem (hx : x.val ∈ U) hvU ht n hn
    rw [h0, sign_zero] at hs
    exact (hσ hs.symm).elim
  · -- On the second segment a vanishing retained degree has sign `-σ` at `y`.
    refine D.label_mem_bchSubgroup_signSubalgebra P hP fun n hn h0 => ?_
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact y.notMem P (by simpa using hP)
    exact sign_eq_neg_of_lineMap_eq_zero hσ (hvU n hn) ht ht1 ((heval _ _ _ _).symm.trans h0)

/-- In a consistent KS complex, the product from a point positive on every retained
nonzero degree to an allowed point `y` is the negative sign factor at `y` of the
product to any point negative on every retained nonzero degree. -/
theorem pathProduct_eq_signFactorizationEquiv_symm_neg
    (hD : D.toFiniteWallDiagram.Consistent)
    {x y z : WallComplement (fun P : C.walls => (P : Set V))}
    (hx : ∀ n ∈ d.cutoff k \ {0}, 0 < s.evaluation x.val n)
    (hz : ∀ n ∈ d.cutoff k \ {0}, s.evaluation z.val n < 0)
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x z) :
    D.toFiniteWallDiagram.pathProduct p =
      ((PositiveDegrees.signFactorizationEquiv ℒ (s.evaluation y.val) d k).symm
        (D.toFiniteWallDiagram.pathProduct q) .neg : d.truncatedGroup ℒ k) := by
  let F := D.toFiniteWallDiagram
  obtain ⟨a, ha⟩ := D.exists_pathProduct_mem_bchSubgroup_signSubalgebra
    (σ := .pos) (by decide) (fun n hn => sign_pos (hx n hn)) y
  obtain ⟨b, hb⟩ := D.exists_pathProduct_mem_bchSubgroup_signSubalgebra
    (σ := .neg) (by decide) (fun n hn => sign_neg (hz n hn)) y
  have hq : F.pathProduct q = (F.pathProduct b)⁻¹ * 1 * F.pathProduct a := by
    rw [(FiniteWallDiagram.consistent_def F).mp hD q (a.comp b.reverse), F.pathProduct_comp,
      F.pathProduct_reverse, mul_one]
  -- The ordered sign factors of the chamber product at `y`.
  let c : ∀ σ, (signSubalgebra (d.truncatedGrading ℒ k) (s.evaluation y.val) σ).bchSubgroup
    | .pos => ⟨(F.pathProduct b)⁻¹, inv_mem hb⟩
    | .zero => 1
    | .neg => ⟨F.pathProduct a, ha⟩
  have hc : (PositiveDegrees.signFactorizationEquiv ℒ (s.evaluation y.val) d k).symm
      (F.pathProduct q) = c := by
    rw [Equiv.symm_apply_eq, PositiveDegrees.signFactorizationEquiv_apply, hq]
    rfl
  rw [hc]
  exact (FiniteWallDiagram.consistent_def F).mp hD p a

end KSComplex

namespace CompletedDiagram

open PositiveDegrees

section General

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {C E : ℕ → FinitePolyhedralComplex h} (D : CompletedDiagram s d ℒ C)

/-- Every finite path product of a consistent completed diagram is the quotient of the
negative sign factors at its endpoints of the transport from the positive degree point
to the negative one, with the target factor on the left. -/
theorem pathProduct_eq_signFactorizationEquiv_symm_neg_mul_inv (hD : D.Consistent) (k : ℕ)
    {x y : WallComplement (fun P : (C k).walls => (P : Set V))}
    (p : AdmissiblePLPath x y) :
    (D.diagram k).toFiniteWallDiagram.pathProduct p =
      ((signFactorizationEquiv ℒ (s.evaluation y.val) d k).symm
          (CompletedGroup.projection k (D.transport hD D.degreePoint D.negDegreePoint)) .neg :
        d.truncatedGroup ℒ k) *
      ((signFactorizationEquiv ℒ (s.evaluation x.val) d k).symm
          (CompletedGroup.projection k (D.transport hD D.degreePoint D.negDegreePoint)) .neg :
        d.truncatedGroup ℒ k)⁻¹ := by
  let := h.finiteDimensional
  let F := (D.diagram k).toFiniteWallDiagram
  have hpos : ∀ n ∈ d.cutoff k \ {0},
      0 < s.evaluation D.degreePoint.val n := fun n hn => by
    rw [degreePoint_val, KSSpace.evaluation_degreePoint]
    exact Int.cast_pos.mpr (d.degree_pos (d.mem_cutoff.mp hn.1).1 hn.2)
  have hneg : ∀ n ∈ d.cutoff k \ {0},
      s.evaluation D.negDegreePoint.val n < 0 := fun n hn => by
    rw [negDegreePoint_val, map_neg, AddMonoidHom.neg_apply, KSSpace.evaluation_degreePoint]
    exact neg_neg_of_pos (Int.cast_pos.mpr (d.degree_pos (d.mem_cutoff.mp hn.1).1 hn.2))
  have hpoly := fun P : (C k).walls =>
    (C k).isConvexPolyhedron ((C k).mem_cells_of_mem_walls P.property)
  have hdim := fun P : (C k).walls => (C k).finrank_direction_add_one_of_mem_walls P.property
  obtain ⟨a, -⟩ := AdmissiblePLPath.exists_length_eq_two hpoly hdim
    (CommonWallComplement.projection k D.degreePoint) x
  obtain ⟨b, -⟩ := AdmissiblePLPath.exists_length_eq_two hpoly hdim
    (CommonWallComplement.projection k D.degreePoint) y
  obtain ⟨c, -⟩ := AdmissiblePLPath.exists_length_eq_two hpoly hdim
    (CommonWallComplement.projection k D.degreePoint)
    (CommonWallComplement.projection k D.negDegreePoint)
  have hDk := (consistent_iff D).mp hD k
  rw [D.projection_transport hD k c, (FiniteWallDiagram.consistent_def F).mp hDk p
      (a.reverse.comp b), F.pathProduct_comp, F.pathProduct_reverse,
    (D.diagram k).pathProduct_eq_signFactorizationEquiv_symm_neg hDk hpos hneg b c,
    (D.diagram k).pathProduct_eq_signFactorizationEquiv_symm_neg hDk hpos hneg a c]

/-- Two consistent completed diagrams are equivalent exactly when their transports
from the positive degree point to the negative one agree. -/
theorem equivalent_iff_transport_eq (F : CompletedDiagram s d ℒ E)
    (hD : D.Consistent) (hF : F.Consistent) :
    D.Equivalent F ↔ D.transport hD D.degreePoint D.negDegreePoint =
      F.transport hF F.degreePoint F.negDegreePoint := by
  constructor
  · intro hDF
    classical
    let := h.finiteDimensional
    -- Join the degree points by one path admissible for both sequences of complexes.
    let A : ℕ ⊕ ℕ → FinitePolyhedralComplex h := Sum.elim C E
    let W : ∀ j, (A j).walls → Set V := fun j P => (P : Set V)
    let u : CommonWallComplement W := ⟨s.degreePoint d, fun j => by
      rcases j with k | k
      · exact fun P => (D.diagram k).degreePoint_not_mem P
      · exact fun P => (F.diagram k).degreePoint_not_mem P⟩
    let w : CommonWallComplement W := ⟨-s.degreePoint d, fun j => by
      rcases j with k | k
      · exact fun P => (D.diagram k).neg_degreePoint_not_mem P
      · exact fun P => (F.diagram k).neg_degreePoint_not_mem P⟩
    obtain ⟨r, -⟩ := CommonWallComplement.exists_length_eq_two
      (fun j P => (A j).isConvexPolyhedron ((A j).mem_cells_of_mem_walls P.property))
      (fun j P => (A j).finrank_direction_add_one_of_mem_walls P.property) u w
    let p := (CommonWallComplement.reindexPrefunctor (W := W) Sum.inl).mapPath r
    let q := (CommonWallComplement.reindexPrefunctor (W := W) Sum.inr).mapPath r
    have hu : (CommonWallComplement.reindexPrefunctor (W := W) Sum.inl).obj u =
        D.degreePoint := CommonWallComplement.ext (by simp [u])
    have hw : (CommonWallComplement.reindexPrefunctor (W := W) Sum.inl).obj w =
        D.negDegreePoint := CommonWallComplement.ext (by simp [w])
    have hu' : (CommonWallComplement.reindexPrefunctor (W := W) Sum.inr).obj u =
        F.degreePoint := CommonWallComplement.ext (by simp [u])
    have hw' : (CommonWallComplement.reindexPrefunctor (W := W) Sum.inr).obj w =
        F.negDegreePoint := CommonWallComplement.ext (by simp [w])
    rw [← hu, ← hw, ← hu', ← hw', D.transport_eq_pathProduct hD p,
      F.transport_eq_pathProduct hF q]
    exact hDF.pathProduct_eq p q ((CommonWallComplement.vertices_reindex Sum.inl r).trans
      (CommonWallComplement.vertices_reindex Sum.inr r).symm)
  · intro he
    rw [equivalent_iff]
    intro k x y x' y' p q hv
    have hx : x.val = x'.val := by
      simpa using congrArg List.head? hv
    have hy : y.val = y'.val := by
      simpa [List.getLast?_eq_getLast_of_ne_nil p.vertices_ne_nil,
        List.getLast?_eq_getLast_of_ne_nil q.vertices_ne_nil] using congrArg List.getLast? hv
    rw [D.pathProduct_eq_signFactorizationEquiv_symm_neg_mul_inv hD k p,
      F.pathProduct_eq_signFactorizationEquiv_symm_neg_mul_inv hF k q, he, hx, hy]

end General

section Reconstruct

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {C : ℕ → FinitePolyhedralComplex h.continuousDual}
  (D : CompletedDiagram (KSSpace.continuousDual h) d ℒ C)

/-- A consistent completed diagram is equivalent to the reconstruction of its transport
from the positive degree point to the negative one. -/
theorem equivalent_reconstruct_transport (hD : D.Consistent) :
    D.Equivalent (d.reconstruct h ℒ (D.transport hD D.degreePoint D.negDegreePoint)) := by
  let g := D.transport hD D.degreePoint D.negDegreePoint
  rw [D.equivalent_iff_transport_eq _ hD (d.consistent_reconstruct h ℒ g),
    d.transport_reconstruct h ℒ g]

/-- Every consistent completed diagram is equivalent to the reconstruction of exactly
one completed BCH group element. -/
theorem existsUnique_equivalent_reconstruct (hD : D.Consistent) :
    ∃! g : d.completedBCHGroup ℒ, D.Equivalent (d.reconstruct h ℒ g) := by
  refine ⟨_, D.equivalent_reconstruct_transport hD,
    fun g (hg : D.Equivalent (d.reconstruct h ℒ g)) => ?_⟩
  rw [D.equivalent_iff_transport_eq _ hD (d.consistent_reconstruct h ℒ g),
    d.transport_reconstruct h ℒ g] at hg
  exact hg.symm

end Reconstruct

end CompletedDiagram

end Mei
