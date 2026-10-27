/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Transport
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Transport
public import Mei.Geometry.Convex.PolyhedralCochain.Exact
import Mei.Geometry.Convex.PolyhedralCochain.Crossing
import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Path
import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus

/-!
# Consistency after central cochain correction

If the retained crossing-defect cochain minus the new wall logarithms is closed,
then the actual corrected directed diagram is consistent at the next cutoff.
Polyhedral exactness supplies a finite potential. Its facets may introduce new
walls through the original loop or its basepoint. Perturb the entire loop into
the combined full, retained-adapted and potential-facet wall family, preserving
the original transport. Representative-invariant pairings and endpoint Stokes
then kill the corrected loop logarithm.

The proof uses `PolyhedralCochain.exists_outgoing_primitive`, global endpoint
Stokes, `DirectedDiagram.log_levelPathProduct_eq_crossingSum_add_restrict`, and
`DirectedDiagram.coe_loopObstruction_eq_neg_wallCrossingSum_defect`.
The moving-basepoint argument follows
`DirectedDiagram.LevelEquivalent.consistent`. This is the consistency step in
Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, proof of Theorem 2.6. No higher-order consistency, facet coverage of
the original diagram, or common admissibility of the original loop is assumed.
-/

public section

noncomputable section

open Set Mei Mei.Convex WallComplement BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι κ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι) (E : DirectedDiagram (d := d) h H κ)
  {k : ℕ} (s : Set ι) [DecidablePred (· ∈ s)] (hs : D.active k ⊆ s)
  (hretained : (D.restrict s).LevelEquivalent E (k + 1))
  (σ : (E.adaptedComplex (k + 1)).walls → OrientedCell h 1)
  (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
  (cross : ∀ Q, E.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property))
  (hk : E.LevelConsistent k)
  (b : WallComplement (fun j : E.active k => (E.wall j).support))
  (t : (E.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
  (ht : ∀ (P : (E.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (x : WallComplement (fun j : E.active k => (E.wall j).support)),
    x.val ∈ interior (P : Set V) →
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = E.levelTransport k hk b x)
  (ω : D.active (k + 1) → OrientedCell h 1)
  (hω : ∀ j, (ω j).carrier = (D.wall j).support)
  (hν : ∀ j : D.active (k + 1), j.val ∉ s → ∀ v : V,
    SignType.sign (h.realCharacter (D.wall j).normal v) =
      (ω j).orientation.evalSign (fun _ : Fin 1 => v))

include hs hretained hσ ht hω hν

/-- Closedness of the retained crossing defects minus the added wall logarithms
implies consistency of the actual corrected diagram at the next order. The
original loops need only be admissible for that diagram: extra adapted walls
and facets of a chosen primitive impose no additional hypothesis on them. -/
theorem levelConsistent_succ_of_closed_residual
    (hclosed :
      let _ := Fintype.ofFinite (D.active (k + 1))
      PolyhedralCochain.coboundary (PolyhedralCochain.ofFinsupp (R := R)
        ((∑ Q, Finsupp.single (σ Q)
            ((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1))) -
          ∑ j : D.active (k + 1), Finsupp.single (ω j)
            (if j.val ∈ s then 0 else
              log (CompletedGroup.projection (k + 1) (D.wall j).label)))) = 0) :
    D.LevelConsistent (k + 1) := by
  classical
  have := h.finiteDimensional
  let := Fintype.ofFinite (D.active (k + 1))
  let A := ∑ Q, Finsupp.single (σ Q)
    ((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1))
  let c := fun j : D.active (k + 1) => if j.val ∈ s then 0 else
    log (CompletedGroup.projection (k + 1) (D.wall j).label)
  let B := ∑ j : D.active (k + 1), Finsupp.single (ω j) (c j)
  -- A primitive may introduce additional facets. Include all of them in the perturbation.
  obtain ⟨_, F, hF, _⟩ := PolyhedralCochain.exists_outgoing_primitive
    (PolyhedralCochain.ofFinsupp (R := R) (A - B)) hclosed
  let K := PolyhedralCochain.coboundaryPresentation (R := R) F
  have hFK : PolyhedralCochain.ofFinsupp (R := R) (A - B) =
      PolyhedralCochain.ofFinsupp K := by
    rw [PolyhedralCochain.ofFinsupp_coboundaryPresentation,
      ← PolyhedralCochain.coboundary_ofFinsupp, hF]
  let υ : D.active (k + 1) ⊕
      ((E.adaptedComplex (k + 1)).walls ⊕ (Σ P : F.support, P.val.boundaryFacets)) →
      OrientedCell h 1 := Sum.elim ω (Sum.elim σ (fun a => a.2.val))
  let W := fun j => (υ j).carrier
  have hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j) := by
    intro j
    obtain ⟨Q, hQ⟩ := isRationalNormalPolyhedron_iff.mp (υ j).rational
    simpa only [W, hQ] using Q.isConvexPolyhedron
  have hdim (j) : Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V := (υ j).finrank_direction_add
  let FD : WallComplement W ⥤q
      WallComplement (fun j : D.active (k + 1) => (D.wall j).support) :=
    WallComplement.wallCoverPrefunctor
    (fun j : D.active (k + 1) => (D.wall j).isConvexPolyhedron.isClosed)
    (fun j z hz => ⟨Sum.inl j, by simpa only [W, υ, Sum.elim_inl, hω] using hz,
      by simp only [W, υ, Sum.elim_inl, hω]; exact subset_rfl,
      by simp only [W, υ, Sum.elim_inl, hω]⟩)
  let FE : WallComplement W ⥤q
      WallComplement (fun Q : (E.adaptedComplex (k + 1)).walls => (Q : Set V)) :=
    WallComplement.wallCoverPrefunctor
    (fun Q : (E.adaptedComplex (k + 1)).walls =>
      ((E.adaptedComplex (k + 1)).isConvexPolyhedron
        ((E.adaptedComplex (k + 1)).mem_cells_of_mem_walls Q.property)).isClosed)
    (fun Q z hz => ⟨Sum.inr (Sum.inl Q),
      by simpa only [W, υ, Sum.elim_inr, Sum.elim_inl, hσ] using hz,
      by simp only [W, υ, Sum.elim_inr, Sum.elim_inl, hσ]; exact subset_rfl,
      by simp only [W, υ, Sum.elim_inr, Sum.elim_inl, hσ]⟩)
  have hAcov : ∀ τ ∈ A.support, ∃ j, τ = υ j := by
    intro τ hτ
    obtain ⟨Q, _, hQ⟩ := Finsupp.mem_support_finsetSum τ hτ
    exact ⟨.inr (.inl Q), ((Finsupp.mem_support_single _ _ _).mp hQ).1⟩
  have hBcov : ∀ τ ∈ B.support, ∃ j, τ = υ j := by
    intro τ hτ
    obtain ⟨j, _, hj⟩ := Finsupp.mem_support_finsetSum τ hτ
    exact ⟨.inl j, ((Finsupp.mem_support_single _ _ _).mp hj).1⟩
  have hABcov : ∀ τ ∈ (A - B).support, ∃ j, τ = υ j := by
    intro τ hτ
    rcases Finset.mem_union.mp (Finsupp.support_sub hτ) with hτ | hτ
    · exact hAcov τ hτ
    · exact hBcov τ hτ
  have hKcov : ∀ τ ∈ K.support, ∃ j, τ = υ j := by
    have hsum : K = ∑ P ∈ F.support, ∑ τ ∈ P.boundaryFacets, Finsupp.single τ (F P) := by
      dsimp only [K]
      conv_lhs => rw [← Finsupp.sum_single F]
      simp only [map_sum, PolyhedralCochain.coboundaryPresentation_single, Finsupp.sum]
    intro τ hτ
    rw [hsum] at hτ
    obtain ⟨P, hP, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
    obtain ⟨η, hη, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
    exact ⟨.inr (.inr ⟨⟨P, hP⟩, ⟨η, hη⟩⟩),
      ((Finsupp.mem_support_single _ _ _).mp hτ).1⟩
  -- Every perturbed segment is transverse to both representatives of the residual.
  have htrans {u v : WallComplement W} (e : u ⟶ v)
      (g : OrientedCell h 1 →₀ d.truncatedLie ℒ (k + 1))
      (hg : ∀ τ ∈ g.support, ∃ j, τ = υ j) :
      ∀ τ ∈ g.support, τ.IsTransverse ![u.val, v.val] := by
    intro τ hτ
    obtain ⟨j, rfl⟩ := hg τ hτ
    exact e.down.isTransverse_orientedCell j
  have hpair {u v : WallComplement W} (q : AdmissiblePLPath u v) :
      q.addWeightOfEPs (fun a b => OrientedCell.intersectionPairing (R := R)
        ![a.val, b.val] (A - B)) =
      q.addWeightOfEPs (fun a b => OrientedCell.intersectionPairing (R := R)
        ![a.val, b.val] K) := by
    induction q with
    | nil => simp only [Quiver.Path.addWeightOfEPs_nil]
    | cons q e ih =>
      rw [Quiver.Path.addWeightOfEPs_cons, Quiver.Path.addWeightOfEPs_cons, ih,
        PolyhedralCochain.intersectionPairing_eq_of_ofFinsupp_eq hFK
          (htrans e (A - B) hABcov) (htrans e K hKcov)]
  apply (D.levelConsistent_iff_loops (k + 1)).mpr
  intro x p
  cases p with
  | nil => simp
  | @cons y _ p e =>
    -- Move both copies of the basepoint together, keeping the original product fixed.
    let loop := p.cons e
    obtain ⟨ε, hε, hstable⟩ := D.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt (k + 1) loop
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp p.vertices_head?
    have hv : loop.vertices.map WallComplement.val =
        x.val :: (l.map WallComplement.val ++ [x.val]) := by
      simp only [loop, Quiver.Path.vertices_cons, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, hl, List.cons_append]
    obtain ⟨a, q, hnear⟩ := AdmissiblePLPath.exists_loop_forall₂_dist_lt hpoly hdim x.val
      (l := l.map WallComplement.val) hε
    let qD := FD.mapPath q
    let qE := FE.mapPath q
    have hvD : qD.vertices.map WallComplement.val = q.vertices.map WallComplement.val := by
      simp only [qD, FD, Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
        WallComplement.wallCoverPrefunctor_obj_val]
    have hvE : qE.vertices.map WallComplement.val = q.vertices.map WallComplement.val := by
      simp only [qE, FE, Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
        WallComplement.wallCoverPrefunctor_obj_val]
    -- The two projected paths compute the added and retained contributions separately.
    have hnew : qD.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] B) = -qD.wallCrossingSum
          (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal) c := by
      have he := fun {u v : WallComplement (fun j => (ω j).carrier)}
        (r : AdmissiblePLPath u v) =>
          r.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum (R := R)
            (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal) c
            (fun j hj => hν j (by intro hjs; simp only [c, hjs, ite_true, ne_self_iff_false] at hj))
      have hcar : (fun j => (ω j).carrier) =
          (fun j : D.active (k + 1) => (D.wall j).support) := funext hω
      rw [hcar] at he
      exact he qD
    have hold : qE.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] A) =
        log (E.levelPathProduct (k + 1) ((E.adaptedPathPrefunctor (k + 1)).mapPath qE)) := by
      have hy : (FE.obj a).val ∉ ((E.adaptedComplex (k + 1)).codimensionAtLeast 1).support := by
        rw [(E.adaptedComplex (k + 1)).support_codimensionAtLeast_one_eq_iUnion_walls
          (E.support_adaptedComplex (k + 1))]
        intro hy
        obtain ⟨Q, hQ⟩ := mem_iUnion.mp hy
        exact (FE.obj a).notMem Q hQ
      obtain ⟨P, ⟨hP, hyP⟩, _⟩ :=
        (E.adaptedComplex (k + 1)).exists_unique_mem_interior_cellsOfCodimension_zero
          (E.support_adaptedComplex (k + 1)) hy
      have he := fun {u v : WallComplement (fun Q => (σ Q).carrier)}
        (r : AdmissiblePLPath u v) =>
          r.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum (R := R)
            (fun Q => h.realCharacter (cross Q).normal)
            (fun Q => ((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1)))
            (fun Q _ v => (cross Q).sign_normal v)
      have hcar : (fun Q => (σ Q).carrier) =
          (fun Q : (E.adaptedComplex (k + 1)).walls => (Q : Set V)) := funext hσ
      rw [hcar] at he
      have hlog := coe_loopObstruction_eq_neg_wallCrossingSum_defect
        σ hσ cross hk b t ht qE ⟨P, hP⟩ hyP
      rw [E.coe_loopObstruction] at hlog
      exact (he qE).trans hlog.symm
    have hprod := ((D.restrict s).levelEquivalent_def E (k + 1)).mp hretained
      ((D.restrictPathPrefunctor s (k + 1)).mapPath qD)
      ((E.adaptedPathPrefunctor (k + 1)).mapPath qE)
      (by simpa only [D.vertices_restrictPathPrefunctor, D.restrictPathPrefunctor_obj_val,
        Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
        E.adaptedPathPrefunctor_obj_val] using hvD.trans hvE.symm)
    have hA := qE.addWeightOfEPs_eq_of_map_vertices_eq q WallComplement.val WallComplement.val
      (fun u v => OrientedCell.intersectionPairing (R := R) ![u, v] A) hvE
    have hB := qD.addWeightOfEPs_eq_of_map_vertices_eq q WallComplement.val WallComplement.val
      (fun u v => OrientedCell.intersectionPairing (R := R) ![u, v] B) hvD
    have hzero : q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] (A - B)) = 0 := by
      -- Quotient invariance replaces the residual by the boundary of the chosen potential.
      rw [hpair]
      have he := PolyhedralCochain.addWeightOfEPs_intersectionPairing_coboundaryPresentation_eq_sub
        (R := R) F (fun P hP τ hτ => ⟨.inr (.inr ⟨⟨P, hP⟩, ⟨τ, hτ⟩⟩), rfl⟩) q
      exact he.trans (sub_self _)
    have hlog : log (D.levelPathProduct (k + 1) qD) = 0 := by
      simp only [map_sub] at hzero
      rw [Quiver.Path.addWeightOfEPs_sub, ← hA, ← hB, hold, hnew] at hzero
      rw [D.log_levelPathProduct_eq_crossingSum_add_restrict s hs qD, hprod]
      rw [sub_neg_eq_add] at hzero
      exact (add_comm _ _).trans hzero
    have hone : D.levelPathProduct (k + 1) qD = 1 := by
      apply log_injective
      rw [hlog, log_one]
    exact (hstable qD (by rwa [hv, hvD])).symm.trans hone

end Mei.DirectedDiagram

