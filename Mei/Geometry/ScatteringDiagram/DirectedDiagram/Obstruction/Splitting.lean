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
`s`, both preserving wall spaces. At each order, `GradedLieHom.idSubSectionComp`, the map
`id - s ∘ π`, is then an idempotent graded map onto the truncated kernel of `π` that
preserves wall spaces. It fixes every loop logarithm of a diagram whose image under `π`
is consistent at that order, since the loop products then lie in the kernel.

The map kills every label lifted along `s`. Hence a diagram consisting of lifted walls
with arbitrary supports, together with walls that are full hyperplanes or whose
logarithms are homogeneous of lower degree, has a loop projection at every order where
its quotient is consistent. Given also consistency of the diagram at the preceding
order, the correction step for loop projections in `Correction/Step.lean` then applies
with the quotient diagram held fixed, and the corrections it adds have logarithms in
the kernel of `π`.

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

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (D : DirectedDiagram (d := d) h H ι)
  (hπ : ∀ n m, ∀ x ∈ H.wall n m, π x ∈ H'.wall n m)
  (hs : ∀ n m, ∀ x ∈ H'.wall n m, s x ∈ H.wall n m)

include hπ hs hsπ in
/-- A split extension gives a loop projection at every order where the quotient diagram
is consistent. Lifted walls have arbitrary supports; every other wall is a full hyperplane
or has a logarithm homogeneous of lower degree. -/
def LoopProjection.ofSplitting {k : ℕ} (hq : (D.map π hπ).LevelConsistent k)
    (lifted : Set ι)
    (hlift : ∀ j ∈ lifted, ∃ y, (D.wall j).label = s.completedMap y)
    (hfull : ∀ j ∉ lifted, (∃ b : ℝ,
        (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b}) ∨
      ∃ m : Γ, d.degree m < k ∧ ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    D.LoopProjection k where
  toLinearMap := π.idSubSectionComp s k
  isIdempotentElem := GradedLieHom.isIdempotentElem_idSubSectionComp hsπ k
  decompose_map x n := by
    rw [GradedLieHom.idSubSectionComp_apply, DirectSum.decompose_sub, DFinsupp.sub_apply,
      Submodule.coe_sub, s.decompose_truncatedMap, π.decompose_truncatedMap,
      GradedLieHom.idSubSectionComp_apply]
  map_wall n m x hx := by
    rw [GradedLieHom.idSubSectionComp_apply]
    exact Submodule.sub_mem _ hx (s.truncatedMap_mem_truncated_wall hs k
      (π.truncatedMap_mem_truncated_wall hπ k hx))
  map_log_loop {x} p := by
    apply GradedLieHom.idSubSectionComp_of_map_eq_zero
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
      rw [hl, s.decompose_truncatedMap, GradedLieHom.idSubSectionComp_truncatedMap hsπ]
    · rcases hfull j hj with hfull | ⟨m, hm, a, ha, he⟩
      · exact hfull
      · have hmn : m ≠ n := by intro he; subst m; omega
        refine (hne ?_).elim
        rw [he, PositiveDegrees.projection_expToCompletion, log_exp,
          DirectSum.decompose_of_mem_ne (d.truncatedGrading ℒ k)
            ((d.mem_truncatedGrading_iff ℒ).mpr ⟨a, ha, rfl⟩) hmn]
        exact map_zero _

@[simp]
theorem LoopProjection.ofSplitting_toLinearMap {k : ℕ} (hq : (D.map π hπ).LevelConsistent k)
    (lifted : Set ι)
    (hlift : ∀ j ∈ lifted, ∃ y, (D.wall j).label = s.completedMap y)
    (hfull : ∀ j ∉ lifted, (∃ b : ℝ,
        (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b}) ∨
      ∃ m : Γ, d.degree m < k ∧ ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    (LoopProjection.ofSplitting (π := π) (s := s) (hsπ := hsπ) (D := D) (hπ := hπ) (hs := hs) hq
      lifted hlift hfull).toLinearMap =
      π.idSubSectionComp s k := (rfl)

end Mei.DirectedDiagram
