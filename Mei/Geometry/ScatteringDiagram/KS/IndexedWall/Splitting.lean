/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall.Map

/-!
# Splitting indexed walls into homogeneous labels

An indexed wall presentation splits into a presentation indexed by an original
wall and an actual degree on its supported ray. Each new wall retains the original
support and primitive coorientation, and its label is the exponential of the
corresponding logarithmic coefficient. Only finitely many split walls survive any
cutoff. At that cutoff the active split supports cover exactly the active original
supports. With abelian rays, multiplying the active factors over each original
index recovers its label, so splitting retains the local wall data. Splitting
commutes with degree-preserving coefficient maps under the canonical
identification of indices, without injectivity or abelian-ray assumptions.

The construction uses `PositiveDegrees.homogeneousFactor`, its support bounds and
`PositiveDegrees.projection_eq_noncommProd_homogeneousFactor`. Coefficient
naturality uses `GradedLieHom.completedMap_homogeneousFactor`. It implements the
homogeneous splitting of abelian-ray labels in Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

universe u

variable {N V R : Type*} {L : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

namespace IndexedWall

/-- Retain one homogeneous logarithmic coefficient of a wall label, with its
original support and primitive coorientation. -/
def homogeneousFactor (W : IndexedWall s d ℒ) (n : N) : IndexedWall s d ℒ where
  ray := W.ray
  support := W.support
  isCone := W.isCone
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := d.homogeneousFactor ℒ W.label n
  label_mem := d.homogeneousFactor_mem_completedRaySubgroup ℒ W.label_mem n

@[simp]
theorem homogeneousFactor_ray (W : IndexedWall s d ℒ) (n : N) :
    (W.homogeneousFactor n).ray = W.ray := (rfl)

@[simp]
theorem homogeneousFactor_support (W : IndexedWall s d ℒ) (n : N) :
    (W.homogeneousFactor n).support = W.support := (rfl)

@[simp]
theorem homogeneousFactor_label (W : IndexedWall s d ℒ) (n : N) :
    (W.homogeneousFactor n).label = d.homogeneousFactor ℒ W.label n := (rfl)

end IndexedWall

namespace IndexedWallPresentation

variable {ι : Type*} (D : IndexedWallPresentation s d ℒ ι)

/-- Indices for homogeneous splitting: an original wall and an actual positive
monoid degree on its ray. Primitive generators outside the monoid are not indices. -/
abbrev HomogeneousIndex := Σ j : ι, (D.wall j).ray.rayDegrees

private theorem homogeneousFactor_active_parent {j : ι} {n : N} {k : ℕ}
    (hn : CompletedGroup.projection k (d.homogeneousFactor ℒ (D.wall j).label n) ≠ 1) :
    j ∈ D.active k := by
  rw [D.mem_active]
  intro hj
  by_cases hk : d.degree n ≤ k
  · exact hn (d.projection_homogeneousFactor_eq_one ℒ _
      (fun _ => d.logComponent_eq_zero_of_projection_eq_one ℒ hk hj))
  · exact hn (d.projection_homogeneousFactor_of_lt ℒ _ (lt_of_not_ge hk))

private theorem finite_homogeneous_active (k : ℕ) :
    {a : D.HomogeneousIndex |
      CompletedGroup.projection k
        (d.homogeneousFactor ℒ (D.wall a.1).label a.2.val) ≠ 1}.Finite := by
  let f : D.HomogeneousIndex → ι × N := fun a => (a.1, a.2.val)
  apply Set.Finite.of_injOn (f := f) ?_ ?_
    ((D.finite_active k).prod (d.finite_cutoff k))
  · rintro ⟨j, n⟩ hn
    refine ⟨(D.mem_active k j).mp (D.homogeneousFactor_active_parent hn), d.mem_cutoff.mpr ⟨?_, ?_⟩⟩
    · exact (D.wall j).ray.rayDegrees_subset n.property
    · by_contra hk
      exact hn (d.projection_homogeneousFactor_of_lt ℒ _ (lt_of_not_ge hk))
  · rintro ⟨j, n⟩ _ ⟨j', n'⟩ _ he
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    exact congrArg (Sigma.mk j) (Subtype.ext he)

/-- Split every indexed wall into its actual homogeneous degrees. This retains
repeated original indices and is finite at every order, without abelian rays. -/
def homogeneousPresentation : IndexedWallPresentation s d ℒ D.HomogeneousIndex where
  wall a := (D.wall a.1).homogeneousFactor a.2.val
  finite_active := D.finite_homogeneous_active

@[simp]
theorem homogeneousPresentation_wall (a : D.HomogeneousIndex) :
    D.homogeneousPresentation.wall a = (D.wall a.1).homogeneousFactor a.2.val := (rfl)

/-- A split wall is active precisely when its degree is retained and its
logarithmic coefficient is nonzero. -/
@[simp↓]
theorem mem_active_homogeneousPresentation (k : ℕ) (a : D.HomogeneousIndex) :
    a ∈ D.homogeneousPresentation.active k ↔
      d.degree a.2.val ≤ k ∧ d.logComponent ℒ (D.wall a.1).label a.2.val ≠ 0 := by
  rw [mem_active, homogeneousPresentation_wall, IndexedWall.homogeneousFactor_label,
    PositiveDegrees.homogeneousFactor_def, ne_eq,
    d.projection_expToCompletion_eq_one_iff ℒ (d.logComponent ℒ _ _).property]
  simp only [not_or, not_lt, Submodule.coe_eq_zero, and_comm]

/-- Every active split wall comes from an active original wall. -/
theorem active_homogeneousPresentation_parent {k : ℕ} {a : D.HomogeneousIndex}
    (ha : a ∈ D.homogeneousPresentation.active k) : a.1 ∈ D.active k := by
  apply D.homogeneousFactor_active_parent
  simpa only [mem_active, homogeneousPresentation_wall, IndexedWall.homogeneousFactor_label]
    using ha

/-- The active homogeneous factors belonging to one original wall. -/
def homogeneousIndices (k : ℕ) (j : ι) : Finset (D.wall j).ray.rayDegrees :=
  ((Set.toFinite (D.homogeneousPresentation.active k)).preimage
    (f := fun n => (⟨j, n⟩ : D.HomogeneousIndex)) (by
      intro n _ n' _ he
      exact eq_of_heq (Sigma.mk.inj_iff.mp he).2)).toFinset

@[simp]
theorem mem_homogeneousIndices (k : ℕ) (j : ι) (n : (D.wall j).ray.rayDegrees) :
    n ∈ D.homogeneousIndices k j ↔
      (⟨j, n⟩ : D.HomogeneousIndex) ∈ D.homogeneousPresentation.active k := by
  rw [homogeneousIndices, Set.Finite.mem_toFinset]
  rfl

/-- An original wall survives a cutoff exactly when at least one of its
homogeneous split walls survives. This does not require abelian rays. -/
theorem mem_active_iff_exists_homogeneous (k : ℕ) (j : ι) :
    j ∈ D.active k ↔ ∃ n : (D.wall j).ray.rayDegrees,
      (⟨j, n⟩ : D.HomogeneousIndex) ∈ D.homogeneousPresentation.active k := by
  constructor
  · intro hj
    by_contra hn
    have hz (n : N) (hk : d.degree n ≤ k) : d.logComponent ℒ (D.wall j).label n = 0 := by
      by_cases hr : n ∈ (D.wall j).ray.rayDegrees
      · by_contra h0
        exact hn ⟨⟨n, hr⟩, (D.mem_active_homogeneousPresentation k _).mpr ⟨hk, h0⟩⟩
      · exact d.logComponent_eq_zero_of_notMem_rayDegrees ℒ (D.wall j).label_mem hr
    have hlog : BCHGroup.log (L := d.truncatedLie ℒ k)
        (CompletedGroup.projection k (D.wall j).label) = 0 := by
      rw [d.log_projection_eq_mkQ_sum ℒ]
      have hsum : (∑ n ∈ (d.finite_cutoff k).toFinset,
          (d.logComponent ℒ (D.wall j).label n : L)) = 0 :=
        Finset.sum_eq_zero fun n hn => congrArg Subtype.val
          (hz n (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp hn)).2)
      rw [hsum, map_zero]
    exact ((D.mem_active k j).mp hj)
      (BCHGroup.log_injective (hlog.trans (BCHGroup.log_one (L := d.truncatedLie ℒ k)).symm))
  · rintro ⟨n, hn⟩
    exact D.active_homogeneousPresentation_parent hn

variable [IsAbelianRays d ℒ]

/-- Multiplying exactly the active homogeneous factors over an original index
recovers its projected label. No zero coefficient or invisible degree contributes. -/
theorem projection_eq_noncommProd_homogeneousPresentation (k : ℕ) (j : ι) :
    CompletedGroup.projection k (D.wall j).label =
      (D.homogeneousIndices k j).noncommProd
        (fun n => CompletedGroup.projection k
          (D.homogeneousPresentation.wall ⟨j, n⟩).label)
        (fun n _ m _ _ => by
          simpa only [homogeneousPresentation_wall, IndexedWall.homogeneousFactor_label] using
            (d.commute_of_mem_completedRaySubgroup ℒ
              (d.homogeneousFactor_mem_completedRaySubgroup ℒ (D.wall j).label_mem n.val)
              (d.homogeneousFactor_mem_completedRaySubgroup ℒ (D.wall j).label_mem m.val)).map
                (CompletedGroup.projection k)) := by
  classical
  let e : (D.wall j).ray.rayDegrees ↪ N := ⟨Subtype.val, Subtype.val_injective⟩
  have hc (n m : N) :
      ⁅(d.logComponent ℒ (D.wall j).label n : L),
        (d.logComponent ℒ (D.wall j).label m : L)⁆ = 0 :=
    lie_eq_zero_of_mem_rayLieSubalgebra ℒ
      (d.logComponent_mem_rayLieSubalgebra ℒ (D.wall j).label_mem n)
      (d.logComponent_mem_rayLieSubalgebra ℒ (D.wall j).label_mem m)
  have he := d.projection_eq_noncommProd_homogeneousFactor hc k
    ((D.homogeneousIndices k j).map e) (fun n hk hn => by
      have hr : n ∈ (D.wall j).ray.rayDegrees := by
        by_contra hr
        exact hn (d.logComponent_eq_zero_of_notMem_rayDegrees ℒ (D.wall j).label_mem hr)
      exact Finset.mem_map.mpr ⟨⟨n, hr⟩, (D.mem_homogeneousIndices k j _).mpr
        ((D.mem_active_homogeneousPresentation k _).mpr ⟨hk, hn⟩), rfl⟩)
  simp only [homogeneousPresentation_wall, IndexedWall.homogeneousFactor_label]
  exact he.trans (Finset.noncommProd_map _ e _ _)

omit [IsAbelianRays d ℒ] in
/-- Homogeneous splitting preserves the union of active supports at every order. -/
theorem iUnion_active_support_homogeneousPresentation (k : ℕ) :
    (⋃ a : D.homogeneousPresentation.active k,
      (D.homogeneousPresentation.wall a).support) =
        ⋃ j : D.active k, (D.wall j).support := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, hx⟩
    refine ⟨⟨a.val.1, D.active_homogeneousPresentation_parent a.property⟩, ?_⟩
    simpa only [homogeneousPresentation_wall, IndexedWall.homogeneousFactor_support] using hx
  · rintro ⟨j, hx⟩
    obtain ⟨n, hn⟩ := (D.mem_active_iff_exists_homogeneous k j).mp j.property
    refine ⟨⟨⟨j, n⟩, hn⟩, ?_⟩
    simpa only [homogeneousPresentation_wall, IndexedWall.homogeneousFactor_support] using hx

end IndexedWallPresentation

section Map

variable {L' : Type u} [LieRing L'] [LieAlgebra R L']
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  {ℳ : N → Submodule R L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]

/-- Changing coefficients commutes with splitting an indexed wall into its
homogeneous logarithmic factors, including factors killed by the map. -/
@[simp]
theorem IndexedWall.map_homogeneousFactor (W : IndexedWall s d ℒ)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (n : N) :
    (W.homogeneousFactor n).map f = (W.map f).homogeneousFactor n := by
  apply IndexedWall.ext <;> simp

namespace IndexedWallPresentation

variable {ι : Type*} (D : IndexedWallPresentation s d ℒ ι)
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)

/-- Coefficient change preserves the original wall index and its actual ray
degree. This identifies the two index types used when mapping and splitting. -/
def homogeneousIndexEquiv : D.HomogeneousIndex ≃ (D.map f).HomogeneousIndex :=
  Equiv.sigmaCongrRight fun j => Set.equivOfEq (by simp)

@[simp]
theorem homogeneousIndexEquiv_fst (a : D.HomogeneousIndex) :
    (D.homogeneousIndexEquiv f a).1 = a.1 := (rfl)

@[simp]
theorem homogeneousIndexEquiv_degree (a : D.HomogeneousIndex) :
    (D.homogeneousIndexEquiv f a).2.val = a.2.val := (rfl)

@[simp]
theorem homogeneousIndexEquiv_symm_fst (a : (D.map f).HomogeneousIndex) :
    ((D.homogeneousIndexEquiv f).symm a).1 = a.1 := (rfl)

@[simp]
theorem homogeneousIndexEquiv_symm_degree (a : (D.map f).HomogeneousIndex) :
    ((D.homogeneousIndexEquiv f).symm a).2.val = a.2.val := (rfl)

/-- Splitting and changing coefficients give exactly the same indexed walls
under the canonical identification of their indices. No abelian-ray or
injectivity hypothesis is needed. -/
@[simp↓]
theorem homogeneousPresentation_map_wall (a : D.HomogeneousIndex) :
    (D.map f).homogeneousPresentation.wall (D.homogeneousIndexEquiv f a) =
      (D.homogeneousPresentation.wall a).map f := by
  simp

end IndexedWallPresentation

end Map
end Mei
