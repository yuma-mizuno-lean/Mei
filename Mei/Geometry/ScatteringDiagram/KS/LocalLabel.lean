/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Germ
public import Mei.Geometry.ScatteringDiagram.KS.Ray
public import Mei.Algebra.Lie.BCH.Ray.Basic

/-!
# Completed labels at regular wall points

At a point outside the singular support of every finite complex, the local wall labels
assemble to a completed BCH label. A cutoff with no wall through the point contributes
the identity. The complexes need neither stabilize nor refine each other, and no
consistency hypothesis is needed. Equivalent diagrams give the same completed label.
Every nonidentity local label belongs to a unique supported-ray subgroup.

These pointwise labels supply the coefficients of local wall germs when comparing
indexed ray presentations with completed cone diagrams. No common neighborhood on which
all finite complexes are constant is asserted.

The construction uses `KSComplex.label_eq_of_equivalent`,
`CompletedDiagram.equivalent_truncate`, and the compatible-family carrier
`Mei.completedGroup`. The conventions follow Bridgeland, *Scattering diagrams, Hall
algebras and stability conditions*, Definition 2.3 and §§2.9–2.11
(arXiv:1603.00416v4), and Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, §1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

namespace KSComplex

variable {C C' : FinitePolyhedralComplex h} {k : ℕ}
  (D : KSComplex s d ℒ C k) (E : KSComplex s d ℒ C' k)
  (θ : V) (hθ : θ ∉ singularSupport (fun P : C.walls => (P : Set V)))

open Classical in
/-- The finite local wall label at a regular point, or the identity when no wall
contains the point. All coorientations are positive on the degree point. -/
def localLabel (_hθ : θ ∉ singularSupport (fun P : C.walls => (P : Set V))) :
    d.truncatedGroup ℒ k :=
  if hp : ∃ P : C.walls, θ ∈ (P : Set V) then D.label hp.choose else 1

/-- Every wall through a regular point computes its local label. -/
theorem localLabel_of_mem (P : C.walls) (hP : θ ∈ (P : Set V)) :
    D.localLabel θ hθ = D.label P := by
  classical
  have hp : ∃ Q : C.walls, θ ∈ (Q : Set V) := ⟨P, hP⟩
  rw [localLabel, dite_eq_left hp]
  exact congrArg D.label (C.eq_of_mem_wall_of_notMem_singularSupport hp.choose_spec hP hθ)

/-- Off all walls the local label is the identity. -/
@[simp]
theorem localLabel_of_notMem (hP : ∀ P : C.walls, θ ∉ (P : Set V)) :
    D.localLabel θ hθ = 1 := by
  classical
  rw [localLabel, dite_eq_right (by simpa using hP)]

/-- Local labels depend only on the path-product equivalence class, at common
regular points of the two complexes. -/
theorem localLabel_eq_of_equivalent
    (hDE : D.toFiniteWallDiagram.Equivalent E.toFiniteWallDiagram)
    (hθE : θ ∉ singularSupport (fun P : C'.walls => (P : Set V))) :
    D.localLabel θ hθ = E.localLabel θ hθE := by
  classical
  by_cases hP : ∃ P : C.walls, θ ∈ (P : Set V)
  · obtain ⟨P, hP⟩ := hP
    rw [D.localLabel_of_mem θ hθ P hP]
    by_cases hQ : ∃ Q : C'.walls, θ ∈ (Q : Set V)
    · obtain ⟨Q, hQ⟩ := hQ
      rw [E.localLabel_of_mem θ hθE Q hQ]
      exact D.label_eq_of_equivalent E hDE P Q hP hQ hθ hθE
    · have hQ : ∀ Q : C'.walls, θ ∉ (Q : Set V) := by simpa using hQ
      rw [E.localLabel_of_notMem θ hθE hQ]
      exact D.label_eq_one_of_equivalent E hDE P hP hθ hQ
  · have hP : ∀ P : C.walls, θ ∉ (P : Set V) := by simpa using hP
    rw [D.localLabel_of_notMem θ hθ hP]
    by_cases hQ : ∃ Q : C'.walls, θ ∈ (Q : Set V)
    · obtain ⟨Q, hQ⟩ := hQ
      rw [E.localLabel_of_mem θ hθE Q hQ]
      exact (E.label_eq_one_of_equivalent D hDE.symm Q hQ hθE hP).symm
    · exact (E.localLabel_of_notMem θ hθE (by simpa using hQ)).symm

/-- Truncation sends a local label to the local label of the truncated diagram. -/
@[simp]
theorem localLabel_truncate {l : ℕ} (hkl : l ≤ k) :
    (D.truncate hkl).localLabel θ hθ =
      (d.truncationMap ℒ hkl).bchGroupMap (D.localLabel θ hθ) := by
  classical
  by_cases hP : ∃ P : C.walls, θ ∈ (P : Set V)
  · obtain ⟨P, hP⟩ := hP
    simp only [localLabel_of_mem _ θ hθ P hP, truncate_label]
  · have hP' : ∀ P : C.walls, θ ∉ (P : Set V) := by simpa using hP
    simp [localLabel_of_notMem, hP']

end KSComplex

namespace CompletedDiagram

variable {C E : ℕ → FinitePolyhedralComplex h}
  (D : CompletedDiagram s d ℒ C)
  (θ : V) (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V)))

/-- Local wall labels at different cutoffs are compatible, including cutoffs at
which the point lies on no wall. -/
theorem truncation_localLabel {k l : ℕ} (hkl : k ≤ l) :
    (d.truncationMap ℒ hkl).bchGroupMap ((D.diagram l).localLabel θ (hθ l)) =
      (D.diagram k).localLabel θ (hθ k) := by
  rw [← KSComplex.localLabel_truncate]
  exact ((D.diagram l).truncate hkl).localLabel_eq_of_equivalent (D.diagram k)
    θ (hθ l) (D.equivalent_truncate hkl) (hθ k)

/-- The completed local wall label at a point regular at every cutoff. Its
coorientation is the one positive on the degree point. -/
def germLabel : d.completedBCHGroup ℒ :=
  ⟨fun k => (D.diagram k).localLabel θ (hθ k),
    (mem_completedGroup_iff _ _).mpr (fun _ _ hkl => D.truncation_localLabel θ hθ hkl)⟩

/-- Each projection is the actual local label of the finite complex. -/
@[simp]
theorem projection_germLabel (k : ℕ) :
    CompletedGroup.projection k (D.germLabel θ hθ) =
      (D.diagram k).localLabel θ (hθ k) := by
  rw [CompletedGroup.projection_apply]
  rfl

/-- A wall through the point computes the corresponding projection. -/
theorem projection_germLabel_of_mem (k : ℕ) (P : (C k).walls)
    (hP : θ ∈ (P : Set V)) :
    CompletedGroup.projection k (D.germLabel θ hθ) = (D.diagram k).label P := by
  rw [projection_germLabel, KSComplex.localLabel_of_mem _ θ (hθ k) P hP]

/-- The completed germ is trivial exactly when all finite local labels are trivial. -/
@[simp]
theorem germLabel_eq_one_iff : D.germLabel θ hθ = 1 ↔
    ∀ k, (D.diagram k).localLabel θ (hθ k) = 1 := by
  constructor
  · intro hg k
    rw [← projection_germLabel, hg, map_one]
    -- The categorical tower and the concrete BCH quotient have the same identity.
    rfl
  · intro hg
    apply CompletedGroup.ext
    intro k
    rw [projection_germLabel, hg, map_one]
    rfl

/-- Points off all walls at all orders have identity germ. -/
@[simp]
theorem germLabel_of_notMem (hP : ∀ k (P : (C k).walls), θ ∉ (P : Set V)) :
    D.germLabel θ hθ = 1 := by
  rw [germLabel_eq_one_iff]
  exact fun k => (D.diagram k).localLabel_of_notMem θ (hθ k) (hP k)

/-- Equivalent completed diagrams have identical local completed labels at every
point regular for both sequences of complexes. -/
theorem germLabel_eq_of_equivalent (F : CompletedDiagram s d ℒ E)
    (hDF : D.Equivalent F)
    (hθF : ∀ k, θ ∉ singularSupport (fun P : (E k).walls => (P : Set V))) :
    D.germLabel θ hθ = F.germLabel θ hθF := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_germLabel]
  exact (D.diagram k).localLabel_eq_of_equivalent (F.diagram k) θ (hθ k)
    ((FiniteWallDiagram.equivalent_def _ _).mpr (by
      intro x y x' y' p q hpq
      exact (equivalent_iff D F).mp hDF k p q hpq)) (hθF k)

/-- A nonidentity local completed label lies on a unique supported ray. This
requires neither abelian ray algebras nor consistency of the diagram. -/
theorem existsUnique_germLabel_mem_completedRaySubgroup [Module.Free ℤ N]
    (hg : D.germLabel θ hθ ≠ 1) :
    ∃! w : SupportedRay d, D.germLabel θ hθ ∈ d.completedRaySubgroup ℒ w := by
  classical
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  apply d.existsUnique_mem_completedRaySubgroup ℒ hg
  intro k hk
  obtain ⟨P, hP⟩ : ∃ P : (C k).walls, θ ∈ (P : Set V) := by
    by_contra! he
    apply hk
    rw [projection_germLabel, KSComplex.localLabel_of_notMem _ θ (hθ k) he]
    rfl
  refine ⟨(D.diagram k).wallRay P, ?_⟩
  rw [projection_germLabel_of_mem _ θ hθ k P hP]
  exact (D.diagram k).label_mem_bchSubgroup_rayLieSubalgebra P
    ((D.diagram k).degree_mem_wallRay P)

/-- Any nonidentity finite wall label determines the ray of the entire completed
germ, regardless of the walls used at other cutoffs. -/
theorem germLabel_mem_completedRaySubgroup [Module.Free ℤ N]
    (k : ℕ) (P : (C k).walls) (hP : θ ∈ (P : Set V))
    (hlabel : (D.diagram k).label P ≠ 1) :
    D.germLabel θ hθ ∈ d.completedRaySubgroup ℒ ((D.diagram k).wallRay P) := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  have hg : D.germLabel θ hθ ≠ 1 := by
    intro he
    apply hlabel
    rw [← D.projection_germLabel_of_mem θ hθ k P hP, he, map_one]
    rfl
  obtain ⟨w, hw, -⟩ := D.existsUnique_germLabel_mem_completedRaySubgroup θ hθ hg
  have hwk := (d.mem_completedRaySubgroup ℒ w _).mp hw k
  rw [D.projection_germLabel_of_mem θ hθ k P hP] at hwk
  have heq : w = (D.diagram k).wallRay P :=
    d.eq_of_mem_bchSubgroup_rayLieSubalgebra (d.truncatedGrading ℒ k) hlabel
      ((LieSubalgebra.mem_bchSubgroup _ _).mpr hwk)
      ((D.diagram k).label_mem_bchSubgroup_rayLieSubalgebra P
        ((D.diagram k).degree_mem_wallRay P))
  exact heq ▸ hw

end CompletedDiagram

end Mei
