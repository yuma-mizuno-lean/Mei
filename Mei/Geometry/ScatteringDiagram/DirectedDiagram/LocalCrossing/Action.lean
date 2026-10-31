/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.Geometry.ScatteringDiagram.WallSpace.NormalVelocity

/-!
# Normal degree under combined regular wall labels

A combined regular crossing preserves and reflects each normal-degree fiber of
a filtered coefficient quotient. The normal can be chosen from any incident
wall. The indexed labels can lie on different supported rays and have opposite
coorientations; each signed factor preserves the same fiber because the normal
kernels agree. No wall-annihilation or consistency hypothesis is needed.

The proof combines `DirectedDiagram.combinedLabel_eq_prod`,
`DirectedWallSpaces.wall_eq_of_ker_eq` and
`DirectedWallSpaces.truncatedExpLieAction_mem_normalDegreeSubmodule_iff`.
This is the normal-velocity condition for whole-component propagation in
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L M V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  (ℳ : Γ → Submodule R M) [SetLike.GradedBracket ℒ ℳ]

local notation "walls" k => fun j : D.active k => DirectedWall.support (DirectedDiagram.wall D j)

/-- A combined regular wall label preserves and reflects every normal-degree
submodule of a filtered quotient. The normal may be chosen from any incident
wall, even when the incident labels lie on different supported rays. -/
theorem truncatedBCHAction_combinedLabel_mem_normalDegreeSubmodule_iff
    (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F] (k : ℕ)
    (θ v : V) (hθ : θ ∉ singularSupport (walls k))
    (j : D.active k) (hj : θ ∈ (D.wall j).support) (z : ℤ) (a : F.quotient k) :
    F.truncatedBCHAction d ℒ k (D.combinedLabel k θ v hθ) a ∈
        (normalDegreeSubmodule ρ ℳ (D.wall j).normal z).map (F.submodule (k + 1)).mkQ ↔
      a ∈ (normalDegreeSubmodule ρ ℳ (D.wall j).normal z).map
        (F.submodule (k + 1)).mkQ := by
  classical
  -- Enumerate every incident wall; equal kernels let each factor use the chosen normal.
  let S := (Set.toFinite {b : D.active k | θ ∈ (D.wall b).support}).toFinset
  rw [D.combinedLabel_eq_prod k θ v hθ S.toList S.nodup_toList (by simp [S])]
  let N := (normalDegreeSubmodule ρ ℳ (D.wall j).normal z).map
    (F.submodule (k + 1)).mkQ
  have hfactor (b : D.active k) (hb : b ∈ S.toList) :
      ∀ a : F.quotient k, F.truncatedBCHAction d ℒ k
        ((CompletedGroup.projection k (D.wall b).label : d.truncatedGroup ℒ k) ^
          (if 0 < h.realCharacter (D.wall b).normal v then -1 else 1 : ℤ)) a ∈ N ↔ a ∈ N := by
    have hbθ : θ ∈ (D.wall b).support := by simpa [S] using hb
    have hker := (D.wall b).normal_ker_eq_of_direction_eq (D.wall j)
      (congrArg AffineSubspace.direction
        (affineSpan_eq_of_notMem_singularSupport (W := walls k) hθ hbθ hj))
    have hg := (H.mem_wallGroup _ _ _).mp
      ((H.wallGroup (D.wall b).ray (D.wall b).normal).zpow_mem (D.wall b).label_mem
        (if 0 < h.realCharacter (D.wall b).normal v then -1 else 1 : ℤ)) k
    rw [H.mem_truncatedRayLieSubalgebra] at hg
    obtain ⟨x, hx, he⟩ := hg
    have hg' : BCHGroup.log ((CompletedGroup.projection k (D.wall b).label : d.truncatedGroup ℒ k) ^
        (if 0 < h.realCharacter (D.wall b).normal v then -1 else 1 : ℤ)) ∈
        H.truncatedRayLieSubalgebra (D.wall b).ray (D.wall j).normal k := by
      apply (H.mem_truncatedRayLieSubalgebra ..).mpr
      refine ⟨x, ?_, ?_⟩
      · rwa [← H.raySubmodule_eq_of_ker_eq (D.wall b).ray hker]
      · simpa only [map_zpow] using he
    intro a
    have hact := F.truncatedBCHAction_apply d ℒ k
      (CompletedGroup.projection k (D.wall b).label ^
        (if 0 < h.realCharacter (D.wall b).normal v then -1 else 1 : ℤ)) a
    exact (Iff.of_eq (congrArg (fun x => x ∈ N) hact)).trans
      (H.truncatedExpLieAction_mem_normalDegreeSubmodule_iff ℳ F hg' z a)
  have hprod : ∀ a : F.quotient k,
      F.truncatedBCHAction d ℒ k
        ((S.toList.map fun b : D.active k =>
          (CompletedGroup.projection k (D.wall b).label : d.truncatedGroup ℒ k) ^
          (if 0 < h.realCharacter (D.wall b).normal v then -1 else 1 : ℤ)).prod) a ∈ N ↔
        a ∈ N := by
    apply List.prod_induction
      (p := fun g => ∀ a : F.quotient k, F.truncatedBCHAction d ℒ k g a ∈ N ↔ a ∈ N)
    · intro x y hx hy a
      simpa only [map_mul, LinearEquiv.mul_apply] using (hx _).trans (hy a)
    · simp
    · intro g hg
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      exact hfactor b hb
  exact hprod a

end Mei.DirectedDiagram
