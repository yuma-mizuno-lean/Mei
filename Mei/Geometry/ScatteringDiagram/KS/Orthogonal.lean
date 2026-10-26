/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Supported
public import Mei.Algebra.Lie.Graded.Truncation.Transition
public import Mei.Algebra.Lie.BCH.Subgroup
public import Mathlib.Basic.Real.Basic

/-!
# Lie algebras orthogonal to dual supports

For a subset `σ` of the real dual of the grading monoid, `orthogonalLieSubalgebra`
is the sum of the homogeneous pieces whose degrees vanish on all of `σ`.
For a positive grading, the degree-zero piece already vanishes, so this is precisely
`g(σ) = ⨁_{n ∈ N⁺, σ ⊆ n⊥} g_n`. In any other model of the real dual, apply the
construction to the evaluation image of the support.

Componentwise membership shows that unions of supports give intersections of
Lie subalgebras. Taking the finite degree quotient commutes with the construction,
and its BCH subgroup maps onto the corresponding subgroup at every lower order.
These are the finite-order label groups for conical scattering walls.

This uses Mathlib's kernels, intersections and `LieSubalgebra.map`, together with
`Mei.supportedLieSubalgebra` and the existing `LieSubalgebra.bchSubgroup`.
-/

public section

namespace Mei

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L]

section General

variable (ℒ : N → Submodule R L) [SetLike.GradedBracket ℒ ℒ]

/-- The Lie subalgebra supported on degrees annihilating every point of `σ`.
No convexity or rationality assumption on the dual support is required. -/
def orthogonalLieSubalgebra (σ : Set (N →+ ℝ)) : LieSubalgebra R L :=
  supportedLieSubalgebra ℒ (⨅ θ ∈ σ, (AddMonoidHom.mker θ).toAddSubsemigroup)

/-- Orthogonality selects the intersection of the evaluation kernels. -/
theorem orthogonalLieSubalgebra_def (σ : Set (N →+ ℝ)) :
    orthogonalLieSubalgebra ℒ σ =
      supportedLieSubalgebra ℒ (⨅ θ ∈ σ, (AddMonoidHom.mker θ).toAddSubsemigroup) := (rfl)

/-- Every piece annihilating the support is contained in its orthogonal Lie algebra. -/
theorem le_orthogonalLieSubalgebra {σ : Set (N →+ ℝ)} {n : N}
    (hn : ∀ θ ∈ σ, θ n = 0) : ℒ n ≤ (orthogonalLieSubalgebra ℒ σ).toSubmodule := by
  apply le_supportedLieSubalgebra
  simpa only [AddSubsemigroup.mem_iInf, AddSubmonoid.mem_toSubsemigroup,
    AddMonoidHom.mem_mker] using hn

/-- A larger dual support imposes more vanishing conditions on degrees. -/
theorem orthogonalLieSubalgebra_antitone : Antitone (orthogonalLieSubalgebra ℒ) := by
  intro σ τ hστ
  apply supportedLieSubalgebra_mono
  intro n hn
  simp only [AddSubsemigroup.mem_iInf, AddSubmonoid.mem_toSubsemigroup,
    AddMonoidHom.mem_mker] at hn ⊢
  exact fun θ hθ => hn θ (hστ hθ)

/-- A degree-preserving additive homomorphism preserves the algebra orthogonal to any
dual support. Neither grading needs an internal decomposition. -/
theorem map_mem_orthogonalLieSubalgebra {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (ℳ : N → Submodule R L') [SetLike.GradedBracket ℳ ℳ]
    (f : L →+ L') (hf : ∀ n, ∀ x ∈ ℒ n, f x ∈ ℳ n)
    {σ : Set (N →+ ℝ)} {x : L} (hx : x ∈ orthogonalLieSubalgebra ℒ σ) :
    f x ∈ orthogonalLieSubalgebra ℳ σ := by
  rw [← LieSubalgebra.mem_toSubmodule, orthogonalLieSubalgebra_def,
    supportedLieSubalgebra_toSubmodule] at hx
  refine Submodule.iSup_induction _ (motive := fun x =>
    f x ∈ orthogonalLieSubalgebra ℳ σ) hx (fun n x hx => ?_)
    (by simp) (fun x y hx hy => by simpa only [map_add] using
      (orthogonalLieSubalgebra ℳ σ).add_mem hx hy)
  apply le_orthogonalLieSubalgebra ℳ _ (hf n x hx)
  simpa only [AddSubsemigroup.mem_iInf, AddSubmonoid.mem_toSubsemigroup,
    AddMonoidHom.mem_mker] using n.property

variable [DecidableEq N] [DirectSum.Decomposition ℒ]

/-- A component must vanish whenever one point of the support detects its degree. -/
@[simp]
theorem mem_orthogonalLieSubalgebra_iff (σ : Set (N →+ ℝ)) (x : L) :
    x ∈ orthogonalLieSubalgebra ℒ σ ↔
      ∀ θ ∈ σ, ∀ n, θ n ≠ 0 → (DirectSum.decompose ℒ x n : L) = 0 := by
  simp only [orthogonalLieSubalgebra_def, mem_supportedLieSubalgebra_iff,
    AddSubsemigroup.mem_iInf, AddSubmonoid.mem_toSubsemigroup,
    AddMonoidHom.mem_mker]
  grind

/-- The orthogonal Lie algebra is stable under homogeneous projections. -/
theorem orthogonalLieSubalgebra_isHomogeneous (σ : Set (N →+ ℝ)) :
    DirectSum.SetLike.IsHomogeneous ℒ (orthogonalLieSubalgebra ℒ σ) :=
  supportedLieSubalgebra_isHomogeneous ℒ _

/-- The empty support imposes no condition on the Lie algebra. -/
@[simp]
theorem orthogonalLieSubalgebra_empty : orthogonalLieSubalgebra ℒ ∅ = ⊤ := by
  ext x
  simp [mem_orthogonalLieSubalgebra_iff]

/-- The zero point imposes no condition on degrees. -/
@[simp]
theorem orthogonalLieSubalgebra_singleton_zero : orthogonalLieSubalgebra ℒ {0} = ⊤ := by
  ext x
  simp [mem_orthogonalLieSubalgebra_iff]

/-- A union of dual supports gives the intersection of their Lie algebras. -/
@[simp]
theorem orthogonalLieSubalgebra_union (σ τ : Set (N →+ ℝ)) :
    orthogonalLieSubalgebra ℒ (σ ∪ τ) =
      orthogonalLieSubalgebra ℒ σ ⊓ orthogonalLieSubalgebra ℒ τ := by
  ext x
  simp only [LieSubalgebra.mem_inf, mem_orthogonalLieSubalgebra_iff, Set.mem_union]
  grind

end General

variable (ℒ : N → Submodule R L) [DecidableEq N] [GradedLieAlgebra ℒ]
  (d : PositiveDegrees N) [IsPositiveGrading d ℒ]

/-- Every finite orthogonal element has a representative in the original orthogonal algebra. -/
theorem map_orthogonalLieSubalgebra_mkQ (σ : Set (N →+ ℝ)) (k : ℕ) :
    (orthogonalLieSubalgebra ℒ σ).map (d.degreeIdeal ℒ k).mkQ =
      orthogonalLieSubalgebra (d.truncatedGrading ℒ k) σ := by
  simp only [orthogonalLieSubalgebra_def]
  apply LieSubalgebra.toSubmodule_injective
  refine (congrArg LieSubalgebra.toSubmodule
    (map_supportedLieSubalgebra ℒ (⨅ θ ∈ σ, (AddMonoidHom.mker θ).toAddSubsemigroup)
      (d.degreeIdeal ℒ k).mkQ)).trans ?_
  simp only [supportedLieSubalgebra_toSubmodule]
  exact iSup_congr fun n => (d.truncatedGrading_eq ℒ k n).symm

/-- Lowering the cutoff maps the finer orthogonal Lie algebra onto the coarser one. -/
theorem map_orthogonalLieSubalgebra_truncationMap (σ : Set (N →+ ℝ))
    {k l : ℕ} (h : k ≤ l) :
    (orthogonalLieSubalgebra (d.truncatedGrading ℒ l) σ).map (d.truncationMap ℒ h) =
      orthogonalLieSubalgebra (d.truncatedGrading ℒ k) σ := by
  simp only [orthogonalLieSubalgebra_def]
  simpa only [d.map_truncatedGrading_truncationMap ℒ h] using
    map_supportedLieSubalgebra (d.truncatedGrading ℒ l)
      (⨅ θ ∈ σ, (AddMonoidHom.mker θ).toAddSubsemigroup) (d.truncationMap ℒ h)

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- The finite orthogonal BCH subgroups map onto one another under truncation. -/
theorem map_bchSubgroup_orthogonalLieSubalgebra (σ : Set (N →+ ℝ))
    {k l : ℕ} (h : k ≤ l) :
    ((orthogonalLieSubalgebra (d.truncatedGrading ℒ l) σ).bchSubgroup).map
        (d.truncationMap ℒ h).bchGroupMap =
      (orthogonalLieSubalgebra (d.truncatedGrading ℒ k) σ).bchSubgroup := by
  rw [← LieSubalgebra.bchSubgroup_map, map_orthogonalLieSubalgebra_truncationMap]

end Mei
