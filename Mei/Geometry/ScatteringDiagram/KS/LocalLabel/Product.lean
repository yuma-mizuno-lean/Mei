/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel.Homogeneous

/-!
# Recovering completed germs from homogeneous walls

At a point regular for every cutoff of a completed KS diagram with abelian rays,
the active homogeneous walls through the point multiply to the projection of its
completed local label. The product uses the actual indexed walls, including their
degree-dependent supports, rather than an independently chosen list of coefficients.
There is at most one incident wall of each degree. Every nonzero coefficient retained
at the cutoff occurs, and inactive walls contribute no factors. In particular,
the projection is the identity exactly when no active homogeneous wall contains
the point: distinct homogeneous degrees cannot cancel.

This recovers local labels from the homogeneous indexed presentation even when the
underlying complexes never stabilize. Consistency is unnecessary. The construction
uses `CompletedDiagram.homogeneousWall_label_eq_germLabel`, uniqueness of a wall
through a regular point, `PositiveDegrees.projection_eq_noncommProd_homogeneousFactor`
and `Finset.noncommProd_bij`.

The local description follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 (arXiv:1411.1394v2), and Bridgeland, *Scattering diagrams,
Hall algebras and stability conditions*, Definition 2.3 and §§2–3
(arXiv:1603.00416v4).
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
  (θ : V) (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V)))

include hθ

/-- All homogeneous walls through a common regular point have commuting completed
labels, even when their supports come from different cutoffs. -/
theorem homogeneousWall_label_commute_of_mem (a b : HomogeneousWallIndex d C)
    (ha : θ ∈ (D.homogeneousWall a).support)
    (hb : θ ∈ (D.homogeneousWall b).support) :
    Commute (D.homogeneousWall a).label (D.homogeneousWall b).label := by
  rw [D.homogeneousWall_label_eq_germLabel a θ hθ ha,
    D.homogeneousWall_label_eq_germLabel b θ hθ hb]
  exact d.commute_homogeneousFactor ℒ (D.lie_logComponent_germLabel θ hθ _ _)

omit [IsAbelianRays d ℒ] in
private theorem exists_active_homogeneousWall {k : ℕ} {n : N} (hn : d.degree n ≤ k)
    (h0 : d.logComponent ℒ (D.germLabel θ hθ) n ≠ 0) :
    ∃ a : D.homogeneousPresentation.active k,
      a.val.1.val = n ∧ θ ∈ (D.homogeneousWall a).support := by
  have hg : D.germLabel θ hθ ≠ 1 := by
    intro he
    exact h0 (by simp [he])
  obtain ⟨w, hw, _⟩ := D.existsUnique_germLabel_mem_completedRaySubgroup θ hθ hg
  have hr : n ∈ w.rayDegrees := by
    by_contra hr
    exact h0 (d.logComponent_eq_zero_of_notMem_rayDegrees ℒ hw hr)
  have hfactor : CompletedGroup.projection k
      (d.homogeneousFactor ℒ (D.germLabel θ hθ) n) ≠ 1 := by
    intro he
    have hz := d.logComponent_eq_zero_of_projection_eq_one ℒ hn he
    exact h0 (by simpa only [PositiveDegrees.logComponent_homogeneousFactor_same] using hz)
  obtain ⟨a, ⟨ha, hθa, _⟩, _⟩ :=
    (D.existsUnique_homogeneousWall_iff
      ⟨n, w.rayDegrees_subset hr, SupportedRay.ne_zero_of_mem_rayDegrees hr⟩ θ hθ).mpr
        (fun he => hfactor (by rw [he, map_one]))
  have hlabel := D.homogeneousWall_label_eq_germLabel a θ hθ hθa
  have hactive : a ∈ D.homogeneousPresentation.active k := by
    rw [IndexedWallPresentation.mem_active, homogeneousPresentation_wall, hlabel, ha]
    exact hfactor
  exact ⟨⟨a, hactive⟩, congrArg Subtype.val ha, hθa⟩

/-- The active homogeneous indexed walls through a regular point recover the
finite projection of its completed germ. The index inventory is precisely the
presentation's `wallIndices` for the singleton point. -/
theorem projection_germLabel_eq_noncommProd_homogeneousWall (k : ℕ) :
    CompletedGroup.projection k (D.germLabel θ hθ) =
      (D.homogeneousPresentation.wallIndices k {θ}).noncommProd
        (fun a => CompletedGroup.projection k (D.homogeneousPresentation.wall a).label)
        (fun a ha b hb _ => by
          simpa only [homogeneousPresentation_wall] using
            (D.homogeneousWall_label_commute_of_mem θ hθ a b
            (by simpa only [homogeneousPresentation_wall] using
              Set.singleton_subset_iff.mp (D.homogeneousPresentation.mem_wallIndices.mp ha))
            (by simpa only [homogeneousPresentation_wall] using
              Set.singleton_subset_iff.mp (D.homogeneousPresentation.mem_wallIndices.mp hb))).map
              (CompletedGroup.projection k)) := by
  classical
  let S := D.homogeneousPresentation.wallIndices k {θ}
  let degree (a : D.homogeneousPresentation.active k) : N := a.val.1.val
  have hmem (a : D.homogeneousPresentation.active k) (ha : a ∈ S) :
      θ ∈ (D.homogeneousWall a).support := by
    simpa only [homogeneousPresentation_wall] using
      Set.singleton_subset_iff.mp (D.homogeneousPresentation.mem_wallIndices.mp ha)
  have hinj : Set.InjOn degree (S : Set (D.homogeneousPresentation.active k)) :=
    D.homogeneousPresentation_wallIndices_degree_injOn k θ hθ
  have hcover (n : N) (hn : d.degree n ≤ k)
      (h0 : d.logComponent ℒ (D.germLabel θ hθ) n ≠ 0) : n ∈ S.image degree :=
    (D.mem_image_homogeneousPresentation_wallIndices k θ hθ n).mpr ⟨hn, h0⟩
  -- Reindex the algebraic homogeneous-factor product by the actual incident walls.
  have hprod := d.projection_eq_noncommProd_homogeneousFactor
    (D.lie_logComponent_germLabel θ hθ) k (S.image degree) hcover
  refine hprod.trans ?_
  symm
  apply Finset.noncommProd_bij _ _ _ _ (fun a _ => degree a)
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    (fun _ ha _ hb he => hinj ha hb he)
    (fun n hn => by
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hn
      exact ⟨a, ha, he⟩)
  intro a ha
  simpa only [homogeneousPresentation_wall] using congrArg (CompletedGroup.projection k)
    (D.homogeneousWall_label_eq_germLabel a θ hθ (hmem a ha))

omit [IsAbelianRays d ℒ] in
/-- At a regular point, a germ is invisible at order `k` exactly when there are
no active homogeneous walls through the point. Different homogeneous degrees
cannot cancel in their combined local label. This does not require abelian rays. -/
theorem projection_germLabel_eq_one_iff_wallIndices_eq_empty (k : ℕ) :
    CompletedGroup.projection k (D.germLabel θ hθ) = 1 ↔
      D.homogeneousPresentation.wallIndices k {θ} = ∅ := by
  classical
  constructor
  · intro hg
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hmem : θ ∈ (D.homogeneousWall a).support := by
      simpa only [homogeneousPresentation_wall] using
        Set.singleton_subset_iff.mp (D.homogeneousPresentation.mem_wallIndices.mp ha)
    apply (D.homogeneousPresentation.mem_active k a).mp a.property
    rw [homogeneousPresentation_wall, D.homogeneousWall_label_eq_germLabel a θ hθ hmem]
    exact d.projection_homogeneousFactor_eq_one ℒ _
      (fun hn => d.logComponent_eq_zero_of_projection_eq_one ℒ hn hg)
  · intro he
    have hz (n : N) (hn : d.degree n ≤ k) : d.logComponent ℒ (D.germLabel θ hθ) n = 0 := by
      by_contra h0
      obtain ⟨a, _, hθa⟩ := D.exists_active_homogeneousWall θ hθ hn h0
      have ha : a ∈ D.homogeneousPresentation.wallIndices k {θ} := by
        apply D.homogeneousPresentation.mem_wallIndices.mpr
        simpa only [homogeneousPresentation_wall] using Set.singleton_subset_iff.mpr hθa
      simp only [he, Finset.notMem_empty] at ha
    simpa only [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker] using
      (d.mem_degreeFiltration_succ_iff (ℒ := ℒ)).mpr hz

end Mei.CompletedDiagram
