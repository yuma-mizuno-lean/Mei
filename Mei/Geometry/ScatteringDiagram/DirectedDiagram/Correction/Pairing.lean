/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Transport
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Transport
import Mei.Geometry.Convex.PolyhedralCochain.Crossing
import TauCeti.Combinatorics.Quiver.PathWeight

/-!
# Corrected loop transport as a residual cochain pairing

Retain all walls active at the preceding cutoff. On a loop admissible for the
union of the retained adapted walls and the complete active family, the logarithm
of the full transport is the sum of segment pairings with the retained crossing
defects minus the logarithmic cochain of the added walls. Thus the residual
cochain used in the correction construction computes actual corrected transport,
without constructing a new chamber trivialization for the combined diagram.

The comparison uses
`DirectedDiagram.log_levelPathProduct_eq_crossingSum_add_restrict`,
`DirectedDiagram.coe_loopObstruction_eq_neg_wallCrossingSum_defect`, and
`Quiver.Path.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum`.
Tau Ceti's `Prefunctor.addWeight_mapPath` identifies the geometric segment
pairings on the projected paths. The subtraction sign comes from the inversion
of a stored wall label at a positive crossing. This is the transport comparison
in Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, proof of Theorem 2.6. Closedness of the residual and perturbation of
arbitrary original loops into the common admissible family are separate steps.
-/

public section

noncomputable section

open Set Mei Mei.Convex WallComplement BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  {k : ℕ} (s : Set ι) [DecidablePred (· ∈ s)]

/-- On every loop admissible for the union of retained adapted walls and the
complete active family, based in a retained full cell, the corrected transport
logarithm is the integrated pairing with the residual
crossing-defect presentation. Only added walls need their displayed orientations
to agree with their normals; retained indices have zero correction coefficient.
Neither closedness nor consistency at the new cutoff is assumed. -/
theorem log_levelPathProduct_eq_residual_pairing
    (hs : D.active k ⊆ s)
    (σ : ((D.restrict s).adaptedComplex (k + 1)).walls → OrientedCell h 1)
    (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
    (cross : ∀ Q, (D.restrict s).AdaptedWallCrossing (l := k + 1) (σ Q)
      ((hσ Q).symm ▸ Q.property))
    (hk : (D.restrict s).LevelConsistent k)
    (b : WallComplement (fun j : (D.restrict s).active k => ((D.restrict s).wall j).support))
    (t : ((D.restrict s).adaptedComplex (k + 1)).cellsOfCodimension 0 →
      d.truncatedGroup ℒ (k + 1))
    (ht : ∀ (P : ((D.restrict s).adaptedComplex (k + 1)).cellsOfCodimension 0)
      (x : WallComplement (fun j : (D.restrict s).active k => ((D.restrict s).wall j).support)),
      x.val ∈ interior (P : Set V) →
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) =
        (D.restrict s).levelTransport k hk b x)
    (τ : D.active (k + 1) → OrientedCell h 1)
    (hτ : ∀ j, (τ j).carrier = (D.wall j).support)
    (hν : ∀ j : D.active (k + 1), j.val ∉ s → ∀ v : V,
      SignType.sign (h.realCharacter (D.wall j).normal v) =
        (τ j).orientation.evalSign (fun _ : Fin 1 => v)) :
    let _ := Fintype.ofFinite ((D.restrict s).adaptedComplex (k + 1)).walls
    let _ := Fintype.ofFinite (D.active (k + 1))
    let W := Sum.elim
      (fun Q : ((D.restrict s).adaptedComplex (k + 1)).walls => (Q : Set V))
      (fun j : D.active (k + 1) => (D.wall j).support)
    let F := WallComplement.restrictPrefunctor W Sum.inr
    ∀ {x : WallComplement W} (p : AdmissiblePLPath x x)
      (P : ((D.restrict s).adaptedComplex (k + 1)).cellsOfCodimension 0),
      x.val ∈ interior (P : Set V) →
      log (D.levelPathProduct (k + 1) (F.mapPath p)) =
        p.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val]
          ((∑ Q, Finsupp.single (σ Q) ((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1))) -
            ∑ j : D.active (k + 1), Finsupp.single (τ j)
              (if j.val ∈ s then 0 else
                log (CompletedGroup.projection (k + 1) (D.wall j).label)))) := by
  classical
  let := Fintype.ofFinite ((D.restrict s).adaptedComplex (k + 1)).walls
  let := Fintype.ofFinite (D.active (k + 1))
  dsimp only
  intro x p P hx
  let A := D.restrict s
  let W := Sum.elim (fun Q : (A.adaptedComplex (k + 1)).walls => (Q : Set V))
    (fun j : D.active (k + 1) => (D.wall j).support)
  let F := WallComplement.restrictPrefunctor W Sum.inr
  let G := WallComplement.restrictPrefunctor W Sum.inl
  let pD := F.mapPath p
  let pA := G.mapPath p
  let a := fun Q => ((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1))
  let c := fun j : D.active (k + 1) => if j.val ∈ s then 0 else
    log (CompletedGroup.projection (k + 1) (D.wall j).label)
  let f := ∑ Q, Finsupp.single (σ Q) (a Q)
  let g := ∑ j : D.active (k + 1), Finsupp.single (τ j) (c j)
  -- Forgetting different admissibility conditions retains precisely the same
  -- geometric vertices, hence the same retained directed transport.
  have hret : A.levelPathProduct (k + 1)
      ((D.restrictPathPrefunctor s (k + 1)).mapPath pD) =
      A.levelPathProduct (k + 1) ((A.adaptedPathPrefunctor (k + 1)).mapPath pA) := by
    apply A.levelPathProduct_eq_of_vertices_eq
    have hv := congrArg (List.map WallComplement.val)
      (Prefunctor.vertices_mapPath (A.adaptedPathPrefunctor (k + 1)) pA)
    have hvA : ((A.adaptedPathPrefunctor (k + 1)).mapPath pA).vertices.map
        WallComplement.val = pA.vertices.map WallComplement.val := by
      refine hv.trans ?_
      rw [List.map_map]
      apply List.map_congr_left
      intro z _
      exact A.adaptedPathPrefunctor_obj_val (k + 1) z
    exact (D.vertices_restrictPathPrefunctor s (k + 1) pD).trans
      ((WallComplement.vertices_restrictPrefunctor W Sum.inr p).trans
        ((WallComplement.vertices_restrictPrefunctor W Sum.inl p).symm.trans hvA.symm))
  have hpairA : pA.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
      ![u.val, v.val] f) =
      -pA.wallCrossingSum (fun Q => h.realCharacter (cross Q).normal) a := by
    have he : ∀ {u v : WallComplement (fun Q => (σ Q).carrier)}
        (q : AdmissiblePLPath u v),
        q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val] f) =
          -q.wallCrossingSum (fun Q => h.realCharacter (cross Q).normal) a :=
      fun q => q.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum _ a
        (fun Q _ v => (cross Q).sign_normal v)
    -- Rewrite carriers so the pairing API accepts the actual adapted path.
    rw [show (fun Q => (σ Q).carrier) =
      (fun Q : (A.adaptedComplex (k + 1)).walls => (Q : Set V)) from funext hσ] at he
    exact he pA
  have hlogA := coe_loopObstruction_eq_neg_wallCrossingSum_defect
    σ hσ cross hk b t ht pA P hx
  rw [coe_loopObstruction] at hlogA
  have hretPair : log (A.levelPathProduct (k + 1)
      ((D.restrictPathPrefunctor s (k + 1)).mapPath pD)) =
      pA.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] f) := by
    rw [hret]
    exact hlogA.trans hpairA.symm
  -- Added logarithms contribute the negative geometric intersection pairing.
  have hpairD : pD.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
      ![u.val, v.val] g) =
      -pD.wallCrossingSum (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal) c := by
    have he : ∀ {u v : WallComplement (fun j => (τ j).carrier)}
        (q : AdmissiblePLPath u v),
        q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val] g) =
          -q.wallCrossingSum (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal) c :=
      fun q => q.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum _ c
        (fun j hj => hν j (by intro hjs; simp only [c, hjs, ite_true, ne_self_iff_false] at hj))
    -- Rewrite carriers so the pairing API accepts the actual directed path.
    rw [show (fun j => (τ j).carrier) =
      (fun j : D.active (k + 1) => (D.wall j).support) from funext hτ] at he
    exact he pD
  -- Pull both projected weights back to the original common path.
  have hA : pA.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
      ![u.val, v.val] f) = p.addWeightOfEPs (fun u v =>
        OrientedCell.intersectionPairing (R := R) ![u.val, v.val] f) := by
    exact G.addWeight_mapPath (fun {u v} _ =>
      OrientedCell.intersectionPairing (R := R) ![u.val, v.val] f) p
  have hD : pD.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
      ![u.val, v.val] g) = p.addWeightOfEPs (fun u v =>
        OrientedCell.intersectionPairing (R := R) ![u.val, v.val] g) := by
    exact F.addWeight_mapPath (fun {u v} _ =>
      OrientedCell.intersectionPairing (R := R) ![u.val, v.val] g) p
  have hsub : ∀ {u v : WallComplement W} (q : AdmissiblePLPath u v),
      q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] (f - g)) =
      q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] f) -
      q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] g) := by
    intro u v q
    induction q with
    | nil => simp only [Quiver.Path.addWeightOfEPs_nil, sub_self]
    | cons q e ih =>
      rw [Quiver.Path.addWeightOfEPs_cons, ih]
      simp only [Quiver.Path.addWeightOfEPs_cons, map_sub]
      abel
  rw [hsub p, ← hA, ← hD, ← hretPair, hpairD,
    D.log_levelPathProduct_eq_crossingSum_add_restrict s hs pD]
  dsimp only [A, c]
  rw [sub_neg_eq_add]
  exact add_comm _ _

end Mei.DirectedDiagram
