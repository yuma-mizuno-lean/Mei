/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel.Homogeneous

/-!
# Recovering regular germs from homogeneous walls

At a point regular for every finite complex, the active homogeneous walls
through that point recover each finite projection of the original completed
germ by an unordered product. Each retained nonzero logarithmic coefficient
occurs exactly once, even when the complexes change with the cutoff.

The argument uses `CompletedDiagram.homogeneousWall_label_eq_germLabel`,
`CompletedDiagram.existsUnique_homogeneousWall_iff` and
`PositiveDegrees.projection_eq_noncommProd_homogeneousFactor`. Abelian rays
ensure that the logarithmic coefficients of a regular germ commute. This is
the local recovery of homogeneous presentations in Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), with the
completed germs of Bridgeland, *Scattering diagrams, Hall algebras and stability
conditions*, Definition 2.3 (arXiv:1603.00416v4).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.CompletedDiagram

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [Module.Free ℤ N]
  {C : ℕ → FinitePolyhedralComplex h} (D : CompletedDiagram s d ℒ C)

/-- The active homogeneous walls through a point at a fixed cutoff. -/
def homogeneousGermIndices (k : ℕ) (θ : V) : Finset (HomogeneousWallIndex d C) := by
  classical
  exact (D.homogeneousPresentation.finite_active k).toFinset.filter
    (fun a => θ ∈ (D.homogeneousWall a).support)

@[simp]
theorem mem_homogeneousGermIndices (k : ℕ) (θ : V) (a : HomogeneousWallIndex d C) :
    a ∈ D.homogeneousGermIndices k θ ↔
      CompletedGroup.projection k (D.homogeneousWall a).label ≠ 1 ∧
        θ ∈ (D.homogeneousWall a).support := by
  classical
  simp only [homogeneousGermIndices, Finset.mem_filter, Set.Finite.mem_toFinset,
    Function.mem_mulSupport, homogeneousPresentation_wall]

/-- At a regular point, distinct incident homogeneous walls have distinct degrees. -/
theorem homogeneousGermIndices_degree_injOn (k : ℕ) (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) :
    Set.InjOn (fun a : HomogeneousWallIndex d C => a.1.val)
      (D.homogeneousGermIndices k θ : Set (HomogeneousWallIndex d C)) := by
  rintro ⟨n, P⟩ hP ⟨m, Q⟩ hQ he
  have hnm : n = m := Subtype.ext he
  subst m
  apply congrArg (Sigma.mk n)
  exact (C (d.degree n.val).toNat).eq_of_mem_wall_of_notMem_singularSupport
    (by simpa only [homogeneousWall_support] using
      ((D.mem_homogeneousGermIndices k θ _).mp hP).2)
    (by simpa only [homogeneousWall_support] using
      ((D.mem_homogeneousGermIndices k θ _).mp hQ).2) (hθ _)

/-- The degrees of the active incident walls are exactly the retained nonzero
logarithmic coefficients of the completed germ. -/
@[simp↓]
theorem mem_image_homogeneousGermIndices (k : ℕ) (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) (n : N) :
    n ∈ (D.homogeneousGermIndices k θ).image (fun a => a.1.val) ↔
      d.degree n ≤ k ∧ d.logComponent ℒ (D.germLabel θ hθ) n ≠ 0 := by
  classical
  constructor
  · rintro hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ha, hmem⟩ := (D.mem_homogeneousGermIndices k θ a).mp ha
    rw [D.homogeneousWall_label_eq_germLabel a θ hθ hmem,
      PositiveDegrees.homogeneousFactor_def] at ha
    have hz := not_congr (d.projection_expToCompletion_eq_one_iff ℒ
      (d.logComponent ℒ (D.germLabel θ hθ) a.1.val).property k)
    rw [not_or, not_lt] at hz
    obtain ⟨hn, hk⟩ := hz.mp ha
    exact ⟨hk, fun he => hn (congrArg Subtype.val he)⟩
  · rintro ⟨hk, hn⟩
    have hp : n ∈ d.monoid ∧ n ≠ 0 := by
      by_contra hp
      have hb : ℒ n = ⊥ := IsPositiveGrading.eq_bot (d := d) n (by tauto)
      exact hn (Subtype.ext ((Submodule.eq_bot_iff _).mp hb _
        (d.logComponent ℒ (D.germLabel θ hθ) n).property))
    have hf : d.homogeneousFactor ℒ (D.germLabel θ hθ) n ≠ 1 := by
      intro he
      have he' := congrArg (fun g => d.logComponent ℒ g n) he
      exact hn (by simpa using he')
    obtain ⟨a, ⟨ha, hmem, _⟩, _⟩ :=
      (D.existsUnique_homogeneousWall_iff ⟨n, hp⟩ θ hθ).mpr hf
    have hdeg : a.1.val = n := congrArg Subtype.val ha
    refine Finset.mem_image.mpr ⟨a, (D.mem_homogeneousGermIndices k θ a).mpr ⟨?_, hmem⟩, hdeg⟩
    rw [D.homogeneousWall_label_eq_germLabel a θ hθ hmem,
      PositiveDegrees.homogeneousFactor_def]
    intro he
    have hz := (d.projection_expToCompletion_eq_one_iff ℒ
      (d.logComponent ℒ (D.germLabel θ hθ) a.1.val).property k).mp he
    rw [hdeg] at hz
    rcases hz with hz | hz
    · exact hn (Subtype.ext hz)
    · omega

variable [IsAbelianRays d ℒ]

private theorem lie_logComponent_germLabel (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) (n m : N) :
    ⁅(d.logComponent ℒ (D.germLabel θ hθ) n : L),
      (d.logComponent ℒ (D.germLabel θ hθ) m : L)⁆ = 0 := by
  by_cases hg : D.germLabel θ hθ = 1
  · simp [hg]
  · obtain ⟨w, hw, _⟩ := D.existsUnique_germLabel_mem_completedRaySubgroup θ hθ hg
    exact lie_eq_zero_of_mem_rayLieSubalgebra ℒ
      (d.logComponent_mem_rayLieSubalgebra ℒ hw n)
      (d.logComponent_mem_rayLieSubalgebra ℒ hw m)

/-- All incident homogeneous labels at an all-order regular point commute,
including labels taken from different finite complexes. -/
theorem homogeneousGermIndices_pairwise_commute (k : ℕ) (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) :
    (D.homogeneousGermIndices k θ : Set (HomogeneousWallIndex d C)).Pairwise
      (fun a b => Commute (D.homogeneousWall a).label (D.homogeneousWall b).label) := by
  intro a ha b hb _
  rw [D.homogeneousWall_label_eq_germLabel a θ hθ
      ((D.mem_homogeneousGermIndices k θ a).mp ha).2,
    D.homogeneousWall_label_eq_germLabel b θ hθ
      ((D.mem_homogeneousGermIndices k θ b).mp hb).2]
  exact d.commute_homogeneousFactor ℒ (D.lie_logComponent_germLabel θ hθ _ _)

/-- Multiplying the active homogeneous walls through a regular point recovers
its original germ at every cutoff. No consistency or stabilization is assumed. -/
theorem projection_germLabel_eq_noncommProd_homogeneousWall (k : ℕ) (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) :
    CompletedGroup.projection k (D.germLabel θ hθ) =
      (D.homogeneousGermIndices k θ).noncommProd
        (fun a => CompletedGroup.projection k (D.homogeneousWall a).label)
        (fun _ ha _ hb hab =>
          (D.homogeneousGermIndices_pairwise_commute k θ hθ ha hb hab).map _) := by
  classical
  let S := D.homogeneousGermIndices k θ
  have hc := D.lie_logComponent_germLabel θ hθ
  refine (d.projection_eq_noncommProd_homogeneousFactor hc k
    (S.image (fun a => a.1.val))
    (fun n hk hn => (D.mem_image_homogeneousGermIndices k θ hθ n).mpr ⟨hk, hn⟩)).trans ?_
  symm
  apply Finset.noncommProd_bij (i := fun a _ => a.1.val)
  · intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · exact D.homogeneousGermIndices_degree_injOn k θ hθ
  · intro n hn
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hn
    exact ⟨a, ha, he⟩
  · intro a ha
    rw [D.homogeneousWall_label_eq_germLabel a θ hθ
      ((D.mem_homogeneousGermIndices k θ a).mp ha).2]

end Mei.CompletedDiagram
