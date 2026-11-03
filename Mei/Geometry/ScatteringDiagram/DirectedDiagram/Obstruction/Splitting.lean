/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Map.Basic

/-!
# Loop projections of split extensions

Let `π : ℒ → ℳ` be a fixed-degree graded Lie homomorphism with a graded Lie section
`s`, both preserving wall spaces. At each order, `id - s ∘ π` is a graded projection
onto the truncated kernel of `π` that preserves wall spaces. It fixes every loop
logarithm of a diagram whose image under `π` is consistent at that order, since the
loop products then lie in the kernel.

The projection kills every label lifted along `s`. Hence a diagram consisting of
lifted walls with arbitrary supports, together with kernel walls that are full
hyperplanes or have lower pure birth, has a loop projection at every order where its
quotient is consistent. The joint obstruction and correction step for loop
projections in `Obstruction/Basic.lean`, `Localization.lean` and
`Correction/Step.lean` then apply with the quotient diagram held fixed, and the
corrections they add have logarithms in the kernel of `π`.

This is the relative completion input of the split-extension argument in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Appendix C.3,
used for module probes. The kernel need not be abelian for these statements.
-/

public section

noncomputable section

open Set Mei Mei.Convex WallComplement BCHGroup

namespace Mei.DirectedDiagram

universe u

variable {Γ Λ R V ι : Type*} {L L' : Type u}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] [DecidableEq Γ]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}

variable (π : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (s : GradedLieHom (PositiveDegreeMap.id d) ℳ ℒ) (hsπ : ∀ x, π (s x) = x)

/-- The order-`k` projection `id - s ∘ π` onto the truncated kernel of `π`. -/
def splittingProjection (k : ℕ) : d.truncatedLie ℒ k →ₗ[R] d.truncatedLie ℒ k :=
  LinearMap.id - (s.truncatedMap k (by simp)).toLinearMap.comp
    (π.truncatedMap k (by simp)).toLinearMap

theorem splittingProjection_apply (k : ℕ) (x : d.truncatedLie ℒ k) :
    splittingProjection π s k x =
      x - s.truncatedMap k (by simp) (π.truncatedMap k (by simp) x) := (rfl)

include hsπ in
/-- On truncations, `π` is a retraction of the section. -/
theorem truncatedMap_truncatedMap_of_section (k : ℕ) (y : d.truncatedLie ℳ k) :
    π.truncatedMap k (by simp) (s.truncatedMap k (by simp) y) = y := by
  have hid : (π.truncatedMap k (by simp)).comp (s.truncatedMap k (by simp)) = LieHom.id := by
    apply (d.degreeIdeal ℳ k).lieHom_qext
    intro x
    simp [LieIdeal.mkQ_apply, hsπ]
  exact DFunLike.congr_fun hid y

include hsπ in
/-- The projection kills the truncation of every element lifted along the section. -/
theorem splittingProjection_truncatedMap (k : ℕ) (y : d.truncatedLie ℳ k) :
    splittingProjection π s k (s.truncatedMap k (by simp) y) = 0 := by
  rw [splittingProjection_apply, truncatedMap_truncatedMap_of_section π s hsπ, sub_self]

/-- The projection fixes every element of the truncated kernel of `π`. -/
theorem splittingProjection_of_map_eq_zero (k : ℕ) {x : d.truncatedLie ℒ k}
    (hx : π.truncatedMap k (by simp) x = 0) : splittingProjection π s k x = x := by
  rw [splittingProjection_apply, hx, map_zero, sub_zero]

include hsπ in
/-- An element fixed by the projection lies in the truncated kernel of `π`. In particular
the corrections produced from a split-extension loop projection have logarithms in the
kernel. -/
theorem truncatedMap_eq_zero_of_splittingProjection_eq (k : ℕ) {x : d.truncatedLie ℒ k}
    (hx : splittingProjection π s k x = x) : π.truncatedMap k (by simp) x = 0 := by
  rw [← hx, splittingProjection_apply, map_sub, truncatedMap_truncatedMap_of_section π s hsπ,
    sub_self]

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (D : DirectedDiagram (d := d) h H ι)
  (hπ : ∀ n m, ∀ x ∈ H.wall n m, π x ∈ H'.wall n m)
  (hs : ∀ n m, ∀ x ∈ H'.wall n m, s x ∈ H.wall n m)

include hπ hs hsπ in
/-- A split extension gives a loop projection at every order where the quotient diagram
is consistent. Lifted walls have arbitrary supports; every other wall has a label in the
kernel of `π` whose support is a full hyperplane or whose logarithm is homogeneous of
lower degree. -/
def LoopProjection.ofSplitting {k : ℕ} (hq : (D.map π hπ).LevelConsistent k)
    (lifted : Set ι)
    (hlift : ∀ j ∈ lifted, ∃ y, (D.wall j).label = s.completedMap y)
    (hker : ∀ j ∉ lifted, π.completedMap (D.wall j).label = 1)
    (hfull : ∀ j ∉ lifted, (∃ b : ℝ,
        (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b}) ∨
      ∃ m : Γ, d.degree m < k ∧ ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    D.LoopProjection k where
  toLinearMap := splittingProjection π s k
  decompose_map x n := by
    rw [splittingProjection_apply, DirectSum.decompose_sub, DFinsupp.sub_apply,
      Submodule.coe_sub, s.decompose_truncatedMap, π.decompose_truncatedMap,
      splittingProjection_apply]
  map_wall n m x hx :=
    Submodule.sub_mem _ hx (s.truncatedMap_mem_truncated_wall hs k
      (π.truncatedMap_mem_truncated_wall hπ k hx))
  map_log_loop {x} p := by
    apply splittingProjection_of_map_eq_zero
    rw [← LieHom.log_bchGroupMap, ← D.levelPathProduct_mapPathPrefunctor π hπ k p,
      (levelConsistent_iff_loops _ k).mp hq, log_one]
  full_of_ne_zero j n hn hne := by
    by_cases hj : j.val ∈ lifted
    · obtain ⟨y, hy⟩ := hlift j hj
      refine (hne ?_).elim
      have hl : log (CompletedGroup.projection k (D.wall j).label) =
          s.truncatedMap k (by simp) (log (CompletedGroup.projection k y)) := by
        rw [hy, s.projection_completedMap_of_le k (a := k) (by simp)]
        exact LieHom.log_bchGroupMap _ _
      rw [hl, s.decompose_truncatedMap, splittingProjection_truncatedMap π s hsπ]
    · have hk : π.truncatedMap k (by simp)
          (log (CompletedGroup.projection k (D.wall j).label)) = 0 := by
        have h1 := LieHom.log_bchGroupMap (π.truncatedMap k (by simp))
          (CompletedGroup.projection k (D.wall j).label)
        have h2 : (π.truncatedMap k (by simp)).bchGroupMap
            (CompletedGroup.projection k (D.wall j).label) = 1 := by
          rw [← π.projection_completedMap_of_le k (by simp), hker j hj, map_one]
          rfl
        rw [← h1, h2, log_one]
      rcases hfull j hj with hfull | ⟨m, hm, a, ha, he⟩
      · exact hfull
      · have hmn : m ≠ n := by intro he; subst m; omega
        refine (hne ?_).elim
        have hk' : π.truncatedMap k (by simp) (DirectSum.decompose (d.truncatedGrading ℒ k)
            (log (CompletedGroup.projection k (D.wall j).label)) n : d.truncatedLie ℒ k) = 0 := by
          rw [← π.decompose_truncatedMap, hk, DirectSum.decompose_zero]
          rfl
        rw [splittingProjection_of_map_eq_zero π s k hk', he,
          PositiveDegrees.projection_expToCompletion, log_exp]
        exact DirectSum.decompose_of_mem_ne (d.truncatedGrading ℒ k)
          ((d.mem_truncatedGrading_iff ℒ).mpr ⟨a, ha, rfl⟩) hmn

@[simp]
theorem LoopProjection.ofSplitting_toLinearMap {k : ℕ} (hq : (D.map π hπ).LevelConsistent k)
    (lifted : Set ι)
    (hlift : ∀ j ∈ lifted, ∃ y, (D.wall j).label = s.completedMap y)
    (hker : ∀ j ∉ lifted, π.completedMap (D.wall j).label = 1)
    (hfull : ∀ j ∉ lifted, (∃ b : ℝ,
        (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b}) ∨
      ∃ m : Γ, d.degree m < k ∧ ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    (LoopProjection.ofSplitting π s hsπ D hπ hs hq lifted hlift hker hfull).toLinearMap =
      splittingProjection π s k := (rfl)

end Mei.DirectedDiagram
