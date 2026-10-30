/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Presentation
public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel

/-!
# Local labels of indexed KS presentations

At a regular point of the complex of an indexed presentation, its local label is
the product of precisely the active indexed labels whose supports contain the
point. This includes points off every support, where the product is empty.
Repeated supports retain their separate factors, and cancellation is allowed.
The same formula computes each projection of the completed local germ, even when
the complexes change with the cutoff.

This bridges the cellwise construction `IndexedWallPresentation.toKSComplex`
and `CompletedDiagram.germLabel`: recovering an arbitrary completed diagram from
indexed walls requires recovering these products at regular points. It uses the
relative-interior support criterion of `IndexedWallPresentation.levelComplex`
and Mathlib's `Finset.noncommProd` and `Finset.noncommProd_toFinset`.

The conventions follow Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, §1.1 (arXiv:1411.1394v2), and Bridgeland, *Scattering diagrams, Hall
algebras and stability conditions*, Definition 2.3 (arXiv:1603.00416v4).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.IndexedWallPresentation

variable {N V R L ι : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (D : IndexedWallPresentation s d ℒ ι)

variable [Module.Free ℤ N] [IsAbelianRays d ℒ]

/-- The finite local label is the unordered product of the active indexed
labels through the point. No consistency or noncancellation hypothesis is needed. -/
@[simp]
theorem localLabel_toKSComplex (k : ℕ) (θ : V)
    (hθ : θ ∉ singularSupport (fun Q : (D.levelComplex k).walls => (Q : Set V))) :
    (D.toKSComplex k).localLabel θ hθ =
      (D.wallIndices k {θ}).noncommProd
        (fun j : D.active k => CompletedGroup.projection k (D.wall j).label)
        (D.wallIndices_singleton_pairwise_commute k θ
          (fun hs => hθ (D.singularSupport_active_subset k hs))) := by
  classical
  by_cases hQ : ∃ Q : (D.levelComplex k).walls, θ ∈ (Q : Set V)
  · obtain ⟨Q, hQ⟩ := hQ
    have hint := mem_intrinsicInterior_of_notMem_singularSupport hQ hθ
    rw [KSComplex.localLabel_of_mem _ θ hθ Q hQ, toKSComplex_label]
    exact Finset.noncommProd_congr
      (D.wallIndices_singleton_eq
        ((D.levelComplex k).mem_cells_of_mem_walls Q.property) hint).symm
      (fun _ _ => rfl) _
  · have hempty : D.wallIndices k {θ} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨Q, hQw, hθQ, -⟩ := D.exists_mem_levelComplex_walls_subset k j
        (singleton_subset_iff.mp (D.mem_wallIndices.mp hj))
      exact hQ ⟨⟨Q, hQw⟩, hθQ⟩
    rw [KSComplex.localLabel_of_notMem _ θ hθ (by simpa using hQ)]
    exact ((Finset.noncommProd_congr hempty (fun _ _ => rfl) _).trans
      (Finset.noncommProd_empty _ _)).symm

/-- Any enumeration without repetitions of the active incident indices computes
the local label. Distinct indices with identical support remain separate factors. -/
theorem localLabel_toKSComplex_eq_prod (k : ℕ) (θ : V)
    (hθ : θ ∉ singularSupport (fun Q : (D.levelComplex k).walls => (Q : Set V)))
    (l : List (D.active k)) (hl : l.Nodup)
    (hm : ∀ j, j ∈ l ↔ θ ∈ (D.wall j).support) :
    (D.toKSComplex k).localLabel θ hθ =
      (l.map fun j : D.active k => CompletedGroup.projection k (D.wall j).label).prod := by
  classical
  have he : D.wallIndices k {θ} = l.toFinset := by
    ext j
    simp only [mem_wallIndices, singleton_subset_iff, List.mem_toFinset]
    exact (hm j).symm
  rw [D.localLabel_toKSComplex k θ hθ]
  exact (Finset.noncommProd_congr he (fun _ _ => rfl) _).trans
    (Finset.noncommProd_toFinset l _ _ hl)

/-- Each projection of the completed local germ is the finite product of the
active indexed labels through that point, with no stabilization assumption. -/
@[simp↓]
theorem projection_germLabel_toCompletedDiagram (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun Q : (D.levelComplex k).walls => (Q : Set V)))
    (k : ℕ) :
    CompletedGroup.projection k (D.toCompletedDiagram.germLabel θ hθ) =
      (D.wallIndices k {θ}).noncommProd
        (fun j : D.active k => CompletedGroup.projection k (D.wall j).label)
        (D.wallIndices_singleton_pairwise_commute k θ
          (fun hs => hθ k (D.singularSupport_active_subset k hs))) := by
  rw [CompletedDiagram.projection_germLabel, toCompletedDiagram_diagram,
    D.localLabel_toKSComplex k θ (hθ k)]

end Mei.IndexedWallPresentation
