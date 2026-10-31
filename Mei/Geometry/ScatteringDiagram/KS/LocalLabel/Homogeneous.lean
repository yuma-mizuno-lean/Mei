/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel
public import Mei.Geometry.ScatteringDiagram.KS.Realization
public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall.Splitting

/-!
# Homogeneous walls of a completed KS diagram

For each actual positive degree `n`, use the walls of a completed diagram at
order `degree(n)` and retain only the degree-`n` logarithmic coefficient of
each label. The resulting indexed wall family is finite at every cutoff.
The homogeneous labels are independent of the completed lifts used in the
finite-wall realization: a projection retaining a degree determines its
logarithmic coefficient.

At every point regular at all orders, the wall through that point at the
degree's own cutoff carries exactly the corresponding homogeneous factor of
the completed germ. If no wall passes through the point, that factor is the
identity. The complexes need neither stabilize nor refine each other. These
are degreewise local recovery statements; comparison of products of the
resulting walls is a further step.

The construction reuses `KSComplex.indexedWall`, `IndexedWall.homogeneousFactor`,
`PositiveDegrees.logComponent` and `CompletedDiagram.germLabel`. It follows the
homogeneous indexed-wall description in Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), and the
finite-order cone complexes of Bridgeland, *Scattering diagrams, Hall algebras
and stability conditions*, Definition 2.3 and §§2–3 (arXiv:1603.00416v4).
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

/-- An actual positive degree and a wall at the cutoff retaining that degree.
The primitive generator of its supported ray need not belong to the monoid. -/
abbrev HomogeneousWallIndex (d : PositiveDegrees N) (C : ℕ → FinitePolyhedralComplex h) :=
  Σ n : {n : N // n ∈ d.monoid ∧ n ≠ 0}, (C (d.degree n.val).toNat).walls

/-- A wall at the degree's own cutoff, with its pure homogeneous label. -/
def homogeneousWall (a : HomogeneousWallIndex d C) : IndexedWall s d ℒ :=
  ((D.diagram (d.degree a.1.val).toNat).indexedWall a.2).homogeneousFactor a.1.val

@[simp]
theorem homogeneousWall_support (a : HomogeneousWallIndex d C) :
    (D.homogeneousWall a).support = (a.2 : Set V) := by
  simp [homogeneousWall]

@[simp]
theorem homogeneousWall_ray (a : HomogeneousWallIndex d C) :
    (D.homogeneousWall a).ray = (D.diagram (d.degree a.1.val).toNat).wallRay a.2 := by
  simp [homogeneousWall]

/-- The label is the homogeneous factor of the finite wall's chosen completed lift. -/
@[simp]
theorem homogeneousWall_label (a : HomogeneousWallIndex d C) :
    (D.homogeneousWall a).label = d.homogeneousFactor ℒ
      ((D.diagram (d.degree a.1.val).toNat).indexedWall a.2).label a.1.val := by
  simp [homogeneousWall]

/-- Any completed lift of the finite wall label gives the same homogeneous label.
Thus the finite realization's choice of lift leaves no choice in this coefficient. -/
theorem homogeneousWall_label_eq (a : HomogeneousWallIndex d C)
    (g : d.completedBCHGroup ℒ)
    (hg : CompletedGroup.projection (d.degree a.1.val).toNat g =
      (D.diagram (d.degree a.1.val).toNat).label a.2) :
    (D.homogeneousWall a).label = d.homogeneousFactor ℒ g a.1.val := by
  rw [homogeneousWall_label, PositiveDegrees.homogeneousFactor_def,
    PositiveDegrees.homogeneousFactor_def]
  exact congrArg (fun x : ℒ a.1.val => d.expToCompletion ℒ x)
    (d.logComponent_eq_of_projection_eq ℒ (Int.self_le_toNat _)
      (((D.diagram (d.degree a.1.val).toNat).projection_indexedWall_label a.2).trans hg.symm))

/-- A pure wall is active exactly when its degree is retained and its coefficient
is nonzero. No abelian-ray assumption is needed. -/
@[simp↓]
theorem homogeneousWall_projection_ne_one_iff (a : HomogeneousWallIndex d C) (k : ℕ) :
    CompletedGroup.projection k (D.homogeneousWall a).label ≠ 1 ↔
      d.degree a.1.val ≤ k ∧ d.logComponent ℒ
        ((D.diagram (d.degree a.1.val).toNat).indexedWall a.2).label a.1.val ≠ 0 := by
  rw [homogeneousWall_label, PositiveDegrees.homogeneousFactor_def, ne_eq,
    d.projection_expToCompletion_eq_one_iff ℒ (d.logComponent ℒ _ _).property]
  simp only [not_or, not_lt, Submodule.coe_eq_zero, and_comm]

private theorem finite_homogeneousWall_active (k : ℕ) :
    {a : HomogeneousWallIndex d C |
      CompletedGroup.projection k (D.homogeneousWall a).label ≠ 1}.Finite := by
  apply Set.Finite.of_finite_fibers (fun a : HomogeneousWallIndex d C => a.1)
  · apply ((d.finite_cutoff k).preimage Subtype.val_injective.injOn).subset
    rintro n ⟨a, ha, rfl⟩
    exact d.mem_cutoff.mpr ⟨a.1.property.1,
      ((D.homogeneousWall_projection_ne_one_iff a k).mp ha).1⟩
  · intro n _
    apply (Set.finite_range (fun P : (C (d.degree n.val).toNat).walls =>
      (⟨n, P⟩ : HomogeneousWallIndex d C))).subset
    rintro ⟨m, P⟩ ⟨_, hm⟩
    have he : m = n := hm
    subst m
    exact ⟨P, rfl⟩

/-- The degreewise homogeneous indexed wall family of a completed KS diagram.
It has finitely many active walls at every cutoff, even if the complexes never stabilize. -/
def homogeneousPresentation : IndexedWallPresentation s d ℒ (HomogeneousWallIndex d C) where
  wall := D.homogeneousWall
  finite_active := D.finite_homogeneousWall_active

@[simp]
theorem homogeneousPresentation_wall (a : HomogeneousWallIndex d C) :
    D.homogeneousPresentation.wall a = D.homogeneousWall a := (rfl)

/-- The completed germ computes each homogeneous wall label at every regular point
on its support. This compares entire completed homogeneous factors. -/
theorem homogeneousWall_label_eq_germLabel (a : HomogeneousWallIndex d C)
    (θ : V) (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V)))
    (ha : θ ∈ (D.homogeneousWall a).support) :
    (D.homogeneousWall a).label = d.homogeneousFactor ℒ (D.germLabel θ hθ) a.1.val := by
  apply D.homogeneousWall_label_eq a (D.germLabel θ hθ)
  apply D.projection_germLabel_of_mem θ hθ
  simpa only [homogeneousWall_support] using ha

omit [Module.Free ℤ N] in
/-- If no wall passes through a regular point at the degree's own cutoff, the
corresponding homogeneous factor of its completed germ is the identity. -/
theorem homogeneousFactor_germLabel_eq_one_of_notMem (n : N)
    (θ : V) (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V)))
    (hP : ∀ P : (C (d.degree n).toNat).walls, θ ∉ (P : Set V)) :
    d.homogeneousFactor ℒ (D.germLabel θ hθ) n = 1 := by
  have hg : CompletedGroup.projection (d.degree n).toNat (D.germLabel θ hθ) = 1 := by
    rw [projection_germLabel, KSComplex.localLabel_of_notMem _ θ (hθ _) hP,
      d.groupTower_obj_one ℒ]
  rw [PositiveDegrees.homogeneousFactor_def,
    d.logComponent_eq_zero_of_projection_eq_one ℒ (Int.self_le_toNat _) hg,
    ZeroMemClass.coe_zero, PositiveDegrees.expToCompletion_zero]

/-- Each nonidentity homogeneous factor of a completed germ is represented by
exactly one nonidentity wall of that degree through the regular point. -/
theorem existsUnique_homogeneousWall_iff
    (n : {n : N // n ∈ d.monoid ∧ n ≠ 0})
    (θ : V) (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V))) :
    (∃! a : HomogeneousWallIndex d C,
      a.1 = n ∧ θ ∈ (D.homogeneousWall a).support ∧ (D.homogeneousWall a).label ≠ 1) ↔
      d.homogeneousFactor ℒ (D.germLabel θ hθ) n.val ≠ 1 := by
  constructor
  · rintro ⟨a, ⟨hn, ha, hlabel⟩, _⟩
    rw [D.homogeneousWall_label_eq_germLabel a θ hθ ha, hn] at hlabel
    exact hlabel
  · intro hg
    obtain ⟨P, hP⟩ : ∃ P : (C (d.degree n.val).toNat).walls, θ ∈ (P : Set V) := by
      by_contra! hP
      exact hg (D.homogeneousFactor_germLabel_eq_one_of_notMem n θ hθ hP)
    have hmem : θ ∈ (D.homogeneousWall ⟨n, P⟩).support := by
      simpa only [homogeneousWall_support] using hP
    refine ⟨⟨n, P⟩, ⟨rfl, hmem, ?_⟩, ?_⟩
    · rw [D.homogeneousWall_label_eq_germLabel _ θ hθ hmem]
      exact hg
    · rintro ⟨m, Q⟩ ⟨hm, hQ, _⟩
      dsimp only at hm
      subst m
      apply congrArg (Sigma.mk n)
      exact (C (d.degree n.val).toNat).eq_of_mem_wall_of_notMem_singularSupport
        (by simpa only [homogeneousWall_support] using hQ) hP (hθ _)

end Mei.CompletedDiagram
