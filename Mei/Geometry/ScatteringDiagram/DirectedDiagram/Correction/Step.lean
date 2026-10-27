/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Potential
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Consistency
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Orientation
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Refinement

/-!
# A consistent outgoing correction at the next order

Given lower-order chamber lifts, full initial hyperplanes and lower homogeneous
noninitial logarithms, add finitely many outgoing walls and obtain consistency
at the next order. Every added wall has a homogeneous logarithm born exactly at
that order. The original indexed walls are retained literally, and all previous
finite-order transports are preserved.

The construction combines `DirectedDiagram.exists_joint_correction_potential`
with `DirectedDiagram.levelConsistent_succ_of_closed_residual`. The potential
identity proves closedness of the residual in the central kernel. Its image in
the ambient truncated Lie algebra is the residual of the actual combined wall
family, including coincident indexed supports. No closedness or next-order
consistency assumption is required.

This is the central correction step in Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, proof of Theorem 2.6, and
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Mei Mei.Convex BCHGroup

universe u v

namespace Mei.DirectedDiagram

variable {Γ : Type u} {V : Type v} {Λ R L ι : Type*}
  [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ] [Module.Free ℤ Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι} {k : ℕ}

/-- A lower-order consistent diagram with full initial hyperplanes and lower
pure birth logarithms admits a finite outgoing extension consistent at the next
order. The extension preserves all lower-order transport, retains every old
indexed wall, and adds only homogeneous walls born exactly at the new order.
The chamber data are for the original diagram at the successive cutoffs. -/
theorem exists_consistent_outgoing_extension
    (σ : (D.adaptedComplex (k + 1)).walls → OrientedCell h 1)
    (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
    (cross : ∀ Q, D.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property))
    (hk : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support))
    (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
    (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
      (x : WallComplement (fun j : D.active k => (D.wall j).support)),
      x.val ∈ interior (P : Set V) →
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)
    (τ : (D.adaptedComplex (k + 1)).joints → OrientedCell h 2)
    (hτ : ∀ J, (τ J).carrier = (J : Set V))
    (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ a : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a})
    (hpure : ∀ j ∉ initial, ∃ n : Γ, d.degree n < k + 1 ∧
      ∃ a ∈ ℒ n, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ (κ : Type (max u v)) (_ : Fintype κ)
      (F : DirectedDiagram (d := d) h H (ι ⊕ κ)),
      (∀ j, F.wall (.inl j) = D.wall j) ∧
      F.LevelConsistent (k + 1) ∧
      (∀ l ≤ k, F.LevelEquivalent D l) ∧
      ∀ a, (F.wall (.inr a)).Outgoing ∧
        (∃ n ∈ (F.wall (.inr a)).ray.rayDegrees, d.degree n = (k : ℤ) + 1 ∧
          ∃ z ∈ ℒ n, (F.wall (.inr a)).label = d.expToCompletion ℒ z) ∧
        ∀ l, Sum.inr a ∈ F.active l ↔ k + 1 ≤ l := by
  classical
  obtain ⟨κ, _, E, η, c, f, hE, hpotential⟩ :=
    exists_joint_correction_potential σ hσ cross hk b t ht τ hτ initial hfull hpure
  -- The sum index keeps every old wall and each new correction as separate occurrences.
  let F : DirectedDiagram (d := d) h H (ι ⊕ κ) :=
    { wall := Sum.elim D.wall E.wall
      finite_active := fun l => by
        apply (((D.finite_active l).image Sum.inl).union
          ((E.finite_active l).image Sum.inr)).subset
        rintro (j | a) hj
        · exact Or.inl ⟨j, hj, rfl⟩
        · exact Or.inr ⟨a, hj, rfl⟩ }
  have hleft (j) : F.wall (.inl j) = D.wall j := rfl
  have hright (a) : F.wall (.inr a) = E.wall a := rfl
  let s : Set (ι ⊕ κ) := range Sum.inl
  have hretained (l : ℕ) : (F.restrict s).LevelEquivalent D l := by
    apply Refinement.levelEquivalent (Refinement.ofEquiv
      (Equiv.ofInjective (Sum.inl : ι → ι ⊕ κ) Sum.inl_injective) ?_) l
    intro j
    rw [restrict_wall, Equiv.ofInjective_apply]
    exact (hleft j).symm
  have hactive (l : ℕ) (hl : l ≤ k) : F.active l ⊆ s := by
    rintro (j | a) hj
    · exact ⟨j, rfl⟩
    · have ha : a ∈ E.active l := by simpa only [mem_active, hright] using hj
      have hb := ((hE a).2.2.2.2.1 l).mp ha
      omega
  let ω : F.active (k + 1) → OrientedCell h 1 := fun j =>
    match j.val with
    | .inl j => (D.wall j).toOrientedCell
    | .inr a => η a
  have hω (j : F.active (k + 1)) : (ω j).carrier = (F.wall j).support := by
    rcases j with ⟨j | a, hj⟩
    · exact (D.wall j).toOrientedCell_carrier
    · exact (hE a).1.symm
  have hν (j : F.active (k + 1)) (hj : j.val ∉ s) (v : V) :
      SignType.sign (h.realCharacter (F.wall j).normal v) =
        (ω j).orientation.evalSign (fun _ : Fin 1 => v) := by
    rcases j with ⟨j | a, ha⟩
    · exact (hj ⟨j, rfl⟩).elim
    · exact (hE a).2.1 v
  let π := d.truncationMap ℒ (Nat.le_succ k)
  let A := crossingDefectCochain σ hσ cross hk b t ht
  let B := ∑ a, PolyhedralCochain.mk (R := R) (η a) (c a)
  have hclosed : PolyhedralCochain.coboundary (A - B) = 0 := by
    rw [← hpotential, PolyhedralCochain.coboundary_coboundary]
  have hclosed' : PolyhedralCochain.coboundary
      (PolyhedralCochain.map π.ker.subtype (A - B)) = 0 := by
    rw [← PolyhedralCochain.map_coboundary, hclosed, map_zero]
  let := Fintype.ofFinite (F.active (k + 1))
  -- All corrections are visible at the new cutoff; only they contribute to the omitted sum.
  let e : κ → F.active (k + 1) := fun a => ⟨.inr a, by
    rw [F.mem_active, hright, ← E.mem_active]
    exact ((hE a).2.2.2.2.1 (k + 1)).mpr le_rfl⟩
  have he : Function.Injective e := fun a b hab =>
    Sum.inr_injective (congrArg Subtype.val hab)
  let newCoeff := fun j : F.active (k + 1) => if j.val ∈ s then 0 else
    log (CompletedGroup.projection (k + 1) (F.wall j).label)
  have hnew : (∑ j : F.active (k + 1), PolyhedralCochain.mk (R := R) (ω j) (newCoeff j)) =
      PolyhedralCochain.map π.ker.subtype B := by
    simp only [B, map_sum, PolyhedralCochain.map_mk, Submodule.subtype_apply]
    symm
    apply Fintype.sum_of_injective e he
    · intro j hj
      rcases j with ⟨j | a, hja⟩
      · simp only [newCoeff, s, mem_range_self, ite_true, map_zero]
      · exact (hj ⟨a, Subtype.ext rfl⟩).elim
    · intro a
      have hn : (e a).val ∉ s := by simp [e, s]
      simp only [newCoeff, hn, ite_false, e, ω, hright, (hE a).2.2.2.2.2]
  have hA : (∑ Q, PolyhedralCochain.mk (R := R) (σ Q)
      ((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1))) =
      PolyhedralCochain.map π.ker.subtype A := by
    simp only [A, crossingDefectCochain_def, map_sum, PolyhedralCochain.map_mk,
      Submodule.subtype_apply]
  have hconsistent : F.LevelConsistent (k + 1) := by
    apply F.levelConsistent_succ_of_closed_residual D s (hactive k le_rfl)
      (hretained (k + 1)) σ hσ cross hk b t ht ω hω hν
    have hresidual := congrArg PolyhedralCochain.coboundary
      (congrArg₂ (· - ·) hA hnew)
    simp only [map_sub] at hclosed'
    simp only [map_sub, map_sum, PolyhedralCochain.ofFinsupp_single]
    simp only [map_sub, map_sum] at hresidual
    exact hresidual.trans hclosed'
  refine ⟨κ, inferInstance, F, hleft, hconsistent, ?_, ?_⟩
  · intro l hl
    exact (F.levelEquivalent_restrict (hactive l hl)).trans (hretained l)
  · intro a
    obtain ⟨_, _, hout, hpureE, hborn, _⟩ := hE a
    exact ⟨hout, hpureE, fun l => by simpa only [mem_active, hright] using hborn l⟩

end Mei.DirectedDiagram
