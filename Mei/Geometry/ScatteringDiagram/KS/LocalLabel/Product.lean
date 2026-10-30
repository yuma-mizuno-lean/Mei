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

/-- At a regular point, distinct incident homogeneous walls have distinct degrees. -/
theorem homogeneousPresentation_wallIndices_degree_injOn (k : ℕ) (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) :
    Set.InjOn (fun a : D.homogeneousPresentation.active k => a.1.1.val)
      (D.homogeneousPresentation.wallIndices k {θ} : Set (D.homogeneousPresentation.active k)) := by
  rintro ⟨⟨n, P⟩, hPa⟩ hP ⟨⟨m, Q⟩, hQa⟩ hQ he
  have hnm : n = m := Subtype.ext he
  subst m
  apply Subtype.ext
  apply congrArg (Sigma.mk n)
  exact (C (d.degree n.val).toNat).eq_of_mem_wall_of_notMem_singularSupport
    (by simpa only [Finset.mem_coe, IndexedWallPresentation.mem_wallIndices,
      Set.singleton_subset_iff, homogeneousPresentation_wall, homogeneousWall_support] using hP)
    (by simpa only [Finset.mem_coe, IndexedWallPresentation.mem_wallIndices,
      Set.singleton_subset_iff, homogeneousPresentation_wall, homogeneousWall_support] using hQ)
    (hθ _)

/-- The degrees of the active incident walls are exactly the retained nonzero
logarithmic coefficients of the completed germ. -/
@[simp↓]
theorem mem_image_homogeneousPresentation_wallIndices (k : ℕ) (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) (n : N) :
    n ∈ (D.homogeneousPresentation.wallIndices k {θ}).image (fun a => a.1.1.val) ↔
      d.degree n ≤ k ∧ d.logComponent ℒ (D.germLabel θ hθ) n ≠ 0 := by
  classical
  constructor
  · intro hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    have hmem : θ ∈ (D.homogeneousWall a).support := by
      simpa only [IndexedWallPresentation.mem_wallIndices, Set.singleton_subset_iff,
        homogeneousPresentation_wall] using ha
    have hactive := (D.homogeneousPresentation.mem_active k a).mp a.property
    rw [homogeneousPresentation_wall,
      D.homogeneousWall_label_eq_germLabel a θ hθ hmem] at hactive
    exact (d.projection_homogeneousFactor_ne_one_iff ℒ _ _ k).mp hactive
  · rintro ⟨hk, hn⟩
    have hp := d.mem_monoid_and_ne_zero_of_logComponent_ne_zero ℒ hn
    have hf : d.homogeneousFactor ℒ (D.germLabel θ hθ) n ≠ 1 := by
      intro he
      have he' := congrArg (fun g => d.logComponent ℒ g n) he
      exact hn (by simpa using he')
    obtain ⟨a, ⟨ha, hmem, _⟩, _⟩ :=
      (D.existsUnique_homogeneousWall_iff ⟨n, hp⟩ θ hθ).mpr hf
    have hdeg : a.1.val = n := congrArg Subtype.val ha
    have hactive : a ∈ D.homogeneousPresentation.active k := by
      rw [IndexedWallPresentation.mem_active, homogeneousPresentation_wall,
        D.homogeneousWall_label_eq_germLabel a θ hθ hmem,
        d.projection_homogeneousFactor_ne_one_iff, hdeg]
      exact ⟨hk, hn⟩
    refine Finset.mem_image.mpr ⟨⟨a, hactive⟩, ?_, hdeg⟩
    simpa only [IndexedWallPresentation.mem_wallIndices, Set.singleton_subset_iff,
      homogeneousPresentation_wall] using hmem

variable [IsAbelianRays d ℒ]

/-- All incident homogeneous labels at an all-order regular point commute,
including labels taken from different finite complexes. -/
theorem homogeneousPresentation_wallIndices_pairwise_commute (k : ℕ) (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) :
    (D.homogeneousPresentation.wallIndices k {θ} :
      Set (D.homogeneousPresentation.active k)).Pairwise
      (fun a b => Commute (D.homogeneousWall a).label (D.homogeneousWall b).label) := by
  intro a ha b hb _
  rw [D.homogeneousWall_label_eq_germLabel a θ hθ
      (by simpa only [Finset.mem_coe, IndexedWallPresentation.mem_wallIndices,
        Set.singleton_subset_iff, homogeneousPresentation_wall] using ha),
    D.homogeneousWall_label_eq_germLabel b θ hθ
      (by simpa only [Finset.mem_coe, IndexedWallPresentation.mem_wallIndices,
        Set.singleton_subset_iff, homogeneousPresentation_wall] using hb)]
  exact d.commute_homogeneousFactor ℒ (D.lie_logComponent_germLabel θ hθ _ _)

/-- Multiplying the active homogeneous walls through a regular point recovers
its original germ at every cutoff. No consistency or stabilization is assumed. -/
theorem projection_germLabel_eq_noncommProd_homogeneousWall (k : ℕ) (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) :
    CompletedGroup.projection k (D.germLabel θ hθ) =
      (D.homogeneousPresentation.wallIndices k {θ}).noncommProd
        (fun a => CompletedGroup.projection k (D.homogeneousWall a).label)
        (fun _ ha _ hb hab =>
          (D.homogeneousPresentation_wallIndices_pairwise_commute k θ hθ ha hb hab).map _) := by
  classical
  let S := D.homogeneousPresentation.wallIndices k {θ}
  have hc := D.lie_logComponent_germLabel θ hθ
  refine (d.projection_eq_noncommProd_homogeneousFactor hc k
    (S.image (fun a => a.1.1.val))
    (fun n hk hn =>
      (D.mem_image_homogeneousPresentation_wallIndices k θ hθ n).mpr ⟨hk, hn⟩)).trans ?_
  symm
  apply Finset.noncommProd_bij (i := fun a _ => a.1.1.val)
  · intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · exact D.homogeneousPresentation_wallIndices_degree_injOn k θ hθ
  · intro n hn
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hn
    exact ⟨a, ha, he⟩
  · intro a ha
    rw [D.homogeneousWall_label_eq_germLabel a θ hθ
      (by simpa only [Finset.mem_coe, IndexedWallPresentation.mem_wallIndices,
        Set.singleton_subset_iff, homogeneousPresentation_wall] using ha)]

end Mei.CompletedDiagram
