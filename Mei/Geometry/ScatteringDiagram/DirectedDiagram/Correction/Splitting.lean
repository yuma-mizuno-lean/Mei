/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Step
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Splitting

/-!
# Kernel corrections over a split extension

Let `π : ℒ → ℳ` be a fixed-degree graded Lie homomorphism with a graded Lie section `s`,
both preserving wall spaces. Consider a diagram whose walls are either lifted along `s`,
with arbitrary supports, or have labels in the kernel of `π` and are full hyperplanes or
born at lower order. If its image under `π` is consistent at the next order, the diagram
admits a finite outgoing extension consistent at that order. Every added wall has a
homogeneous logarithm in the kernel of `π`, so the image of the extension under `π`
adds only trivial labels.

Thus the quotient diagram is held fixed through the correction, and no support
hypothesis is imposed on the lifted walls. This is the one-order step of relative
completion over a split extension: it combines `LoopProjection.ofSplitting` with
`LoopProjection.exists_consistent_outgoing_extension`, then reads off kernel membership
from the projection-fixed correction logarithms using
`PositiveDegrees.projection_expToCompletion_eq_one_iff`.
-/

public section

noncomputable section

open Set Mei Mei.Convex BCHGroup

universe u v w

namespace Mei.DirectedDiagram

variable {Γ : Type u} {V : Type v} {Λ R ι : Type*} {L L' : Type w}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq Γ] [Module.Free ℤ Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ} {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  {D : DirectedDiagram (d := d) h H ι} {k : ℕ}

/-- Over a split extension, a lower-order consistent diagram whose quotient is consistent
at the next order admits a finite outgoing extension consistent at the next order. The
lifted walls may have arbitrary supports. Every added wall is born exactly at the new
order with a homogeneous logarithm in the kernel of `π`, so its image under `π` is
trivial. The extension preserves all lower-order transport and retains every old wall. -/
theorem exists_consistent_kernel_extension
    (π : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (s : GradedLieHom (PositiveDegreeMap.id d) ℳ ℒ) (hsπ : ∀ x, π (s x) = x)
    (hπ : ∀ n m, ∀ x ∈ H.wall n m, π x ∈ H'.wall n m)
    (hs : ∀ n m, ∀ x ∈ H'.wall n m, s x ∈ H.wall n m)
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
    (hq : (D.map π hπ).LevelConsistent (k + 1)) (lifted : Set ι)
    (hlift : ∀ j ∈ lifted, ∃ y, (D.wall j).label = s.completedMap y)
    (hker : ∀ j ∉ lifted, π.completedMap (D.wall j).label = 1)
    (hfull : ∀ j ∉ lifted, (∃ a : ℝ,
        (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a}) ∨
      ∃ n : Γ, d.degree n < k + 1 ∧ ∃ a ∈ ℒ n, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ (κ : Type (max u v)) (_ : Fintype κ)
      (F : DirectedDiagram (d := d) h H (ι ⊕ κ)),
      (∀ j, F.wall (.inl j) = D.wall j) ∧
      F.LevelConsistent (k + 1) ∧
      (∀ l ≤ k, F.LevelEquivalent D l) ∧
      ∀ a, (F.wall (.inr a)).Outgoing ∧
        (∃ n ∈ (F.wall (.inr a)).ray.rayDegrees, d.degree n = (k : ℤ) + 1 ∧
          ∃ z ∈ ℒ n, π z = 0 ∧ (F.wall (.inr a)).label = d.expToCompletion ℒ z) ∧
        (∀ l, Sum.inr a ∈ F.active l ↔ k + 1 ≤ l) ∧
        π.completedMap (F.wall (.inr a)).label = 1 := by
  obtain ⟨κ, _, F, hleft, hF, heq, hnew⟩ :=
    (LoopProjection.ofSplitting π s hsπ D hπ hs hq lifted hlift hker
      hfull).exists_consistent_outgoing_extension σ hσ cross hk b t ht τ hτ
  refine ⟨κ, inferInstance, F, hleft, hF, heq, fun a => ?_⟩
  obtain ⟨hout, ⟨n, hn, hdeg, z, hz, hlabel⟩, hborn, hfix⟩ := hnew a
  -- The correction logarithm is fixed by `id - s ∘ π`, hence killed by `π`.
  rw [LoopProjection.ofSplitting_toLinearMap] at hfix
  have h0 := truncatedMap_eq_zero_of_splittingProjection_eq π s hsπ (k + 1) hfix
  have hproj : CompletedGroup.projection (k + 1) (π.completedMap (F.wall (.inr a)).label) = 1 := by
    rw [π.projection_completedMap_of_le (k + 1) (a := k + 1) (by simp)]
    apply log_injective
    have h1 := LieHom.log_bchGroupMap (π.truncatedMap (k + 1) (by simp))
      (CompletedGroup.projection (k + 1) (F.wall (.inr a)).label)
    exact h1.trans (h0.trans log_one.symm)
  rw [hlabel, GradedLieHom.completedMap_expToCompletion] at hproj
  have hπz : π z = 0 := by
    rcases (d.projection_expToCompletion_eq_one_iff ℳ (π.map_mem hz) (k + 1)).mp hproj with
      hzero | hlt
    · exact hzero
    · simp only [PositiveDegreeMap.id_apply] at hlt
      push_cast at hlt
      omega
  refine ⟨hout, ⟨n, hn, hdeg, z, hz, hπz, hlabel⟩, hborn, ?_⟩
  rw [hlabel, GradedLieHom.completedMap_expToCompletion, hπz, PositiveDegrees.expToCompletion_zero]

end Mei.DirectedDiagram
