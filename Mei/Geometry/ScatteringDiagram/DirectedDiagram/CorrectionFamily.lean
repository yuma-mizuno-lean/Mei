/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.CorrectionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Algebra.Lie.Graded.Truncation.Transition

/-!
# Finite families of joint correction walls

At the next order after a consistent cutoff, the logarithm of every loop product
has only the newly retained degree. For sufficiently small loops at the joints
of the adapted complex, assemble one outgoing swept wall for each nonzero
homogeneous component. The index retains both the joint and the actual degree,
including when distinct indices produce coincident supports. It is finite, and
every wall is first active at exactly the correction order. At each joint, the
sum of the new wall logarithms is the negative of the original loop logarithm.

This combines `DirectedDiagram.exists_outgoingWall_joint_obstruction` with
homogeneity of the truncation kernel and `DirectSum.sum_support_decompose`.
It is the finite-family assembly in the degree induction of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6. The loops are supplied as actual admissible paths; their
positive meridian orientation and the geometric identities needed for
consistency of the corrected diagram are separate requirements.
-/

public section

noncomputable section

open Set Mei Mei.Convex BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

variable {k : ℕ}
  (x : (D.adaptedComplex (k + 1)).joints →
    WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
  (p : ∀ J, AdmissiblePLPath (x J) (x J))

open Classical in
/-- Joint-degree pairs with nonzero homogeneous loop logarithm. The index uses
actual degrees, rather than all primitive generators of bounded degree. -/
abbrev JointCorrectionIndex :=
  Σ J : (D.adaptedComplex (k + 1)).joints,
    (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
      (log (D.levelPathProduct (k + 1) (p J)))).support

/-- Lower-order consistency forces each nonzero loop component to have exactly
the correction degree. This does not require the loop to be local. -/
theorem degree_jointCorrectionIndex (hk : D.LevelConsistent k)
    (a : D.JointCorrectionIndex x p) : d.degree a.2.val = (k : ℤ) + 1 := by
  classical
  have hne : (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
      (log (D.levelPathProduct (k + 1) (p a.1))) a.2.val : d.truncatedLie ℒ (k + 1)) ≠ 0 :=
    fun hz => (DFinsupp.mem_support_toFun _ _).mp a.2.property (Subtype.ext hz)
  have hker : log (D.levelPathProduct (k + 1) (p a.1)) ∈
      (d.truncationMap ℒ (Nat.le_succ k)).ker := by
    rw [LieHom.mem_ker, ← LieHom.log_bchGroupMap,
      D.truncation_levelPathProduct (Nat.le_succ k),
      (D.levelConsistent_iff_loops k).mp hk, log_one]
  have hck := d.ker_truncationMap_isHomogeneous ℒ (Nat.le_succ k) a.2.val hker
  have hc := (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
    (log (D.levelPathProduct (k + 1) (p a.1))) a.2.val).property
  have hlo := d.lt_degree_of_mem_ker_truncationMap ℒ (Nat.le_succ k) hc hck hne
  have hpiece : d.truncatedGrading ℒ (k + 1) a.2.val ≠ ⊥ := by
    intro he
    exact hne (by simpa only [he, Submodule.mem_bot] using hc)
  have hhi := (d.mem_cutoff.mp (d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hpiece).1).2
  omega

/-- Whenever one correction wall negates each nonzero component of a joint
loop logarithm, the finite sum of those wall logarithms negates the entire
logarithm. Empty supports are included. -/
private theorem sum_log_joint_correction_eq
    (E : DirectedDiagram (d := d) h H (D.JointCorrectionIndex x p))
    (hlog : ∀ a : D.JointCorrectionIndex x p,
      log (CompletedGroup.projection (k + 1) (E.wall a).label) =
        -(DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
          (log (D.levelPathProduct (k + 1) (p a.1))) a.2.val : d.truncatedLie ℒ (k + 1)))
    (J : (D.adaptedComplex (k + 1)).joints) :
    letI := Classical.decEq (d.truncatedLie ℒ (k + 1))
    ∑ n : (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
      (log (D.levelPathProduct (k + 1) (p J)))).support,
      log (CompletedGroup.projection (k + 1) (E.wall ⟨J, n⟩).label) =
      -log (D.levelPathProduct (k + 1) (p J)) := by
  classical
  simp only [hlog, Finset.sum_neg_distrib]
  congr 1
  let f := DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
    (log (D.levelPathProduct (k + 1) (p J)))
  exact (Finset.sum_coe_sort f.support
    (fun n => (f n : d.truncatedLie ℒ (k + 1)))).trans
      (DirectSum.sum_support_decompose (d.truncatedGrading ℒ (k + 1))
        (log (D.levelPathProduct (k + 1) (p J))))

/-- Near every adapted joint, the nonzero components of local loop logarithms
assemble into a finite outgoing diagram. Each label has a pure birth logarithm
at order `k + 1`, is nontrivial exactly from that order on, and negates the
corresponding component. The sum at each joint negates its entire loop
logarithm. No consistency of the new diagram is asserted. -/
theorem exists_joint_correction_family [Module.Free ℤ Γ]
    (hk : D.LevelConsistent k)
    (q : (D.adaptedComplex (k + 1)).joints → V)
    (hq : ∀ J : (D.adaptedComplex (k + 1)).joints, q J ∈ intrinsicInterior ℝ (J : Set V))
    (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k + 1 ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ r : (D.adaptedComplex (k + 1)).joints → ℝ, (∀ J, 0 < r J) ∧
      ∀ (x : (D.adaptedComplex (k + 1)).joints →
          WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
        (p : ∀ J, AdmissiblePLPath (x J) (x J)),
        (∀ J z, z ∈ (p J).vertices → z.val ∈ Metric.ball (q J) (r J)) →
        ∃ E : DirectedDiagram (d := d) h H (D.JointCorrectionIndex x p),
          (∀ a : D.JointCorrectionIndex x p,
            (E.wall a).Outgoing ∧
            (E.wall a).support = Convex.sweep (a.1 : Set V) (i (ρ a.2.val)) ∧
            a.2.val ∈ (E.wall a).ray.rayDegrees ∧
            (∃ b ∈ ℒ a.2.val, (E.wall a).label = d.expToCompletion ℒ (-b)) ∧
            (∀ l : ℕ, a ∈ E.active l ↔ k + 1 ≤ l) ∧
            log (CompletedGroup.projection (k + 1) (E.wall a).label) =
              -(DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
                (log (D.levelPathProduct (k + 1) (p a.1))) a.2.val :
                  d.truncatedLie ℒ (k + 1))) ∧
          ∀ J : (D.adaptedComplex (k + 1)).joints,
            letI := Classical.decEq (d.truncatedLie ℒ (k + 1))
            ∑ n : (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
                (log (D.levelPathProduct (k + 1) (p J)))).support,
              log (CompletedGroup.projection (k + 1) (E.wall ⟨J, n⟩).label) =
                -log (D.levelPathProduct (k + 1) (p J)) := by
  classical
  have hlocal := fun J : (D.adaptedComplex (k + 1)).joints =>
    D.exists_outgoingWall_joint_obstruction J.property (hq J) initial hfull hpure
  choose r hr hwall using hlocal
  refine ⟨r, hr, fun x p hp => ?_⟩
  have hex (a : D.JointCorrectionIndex x p) :=
    hwall a.1 (x a.1) (p a.1) (hp a.1) a.2.val
      (by simpa using D.degree_jointCorrectionIndex x p hk a)
      (fun hz => (DFinsupp.mem_support_toFun _ _).mp a.2.property (Subtype.ext hz))
  choose W b hout hsupp hray hnormal hb hlabel hclass hborn hlog hne using hex
  refine ⟨ofFinite W, ?_, ?_⟩
  · intro a
    simp only [ofFinite_wall]
    refine ⟨hout a, hsupp a, hray a,
      ⟨b a, H.wall_le_piece _ _ (hb a), hlabel a⟩, ?_, hlog a⟩
    intro l
    rw [mem_active, ofFinite_wall]
    constructor
    · intro ha
      by_contra hl
      exact ha (hborn a l (by omega))
    · intro hl
      have ha : a ∈ (ofFinite W).active (k + 1) := by
        simpa only [mem_active, ofFinite_wall] using hne a
      simpa only [mem_active, ofFinite_wall] using (ofFinite W).active_mono hl ha
  · exact D.sum_log_joint_correction_eq x p (ofFinite W)
      (fun a => by simpa only [ofFinite_wall] using hlog a)

end Mei.DirectedDiagram
