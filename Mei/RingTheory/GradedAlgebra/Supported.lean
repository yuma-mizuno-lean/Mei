/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.Basic
public import TauCeti.RingTheory.GradedAlgebra.Subalgebra

/-!
# Subalgebras supported on additive submonoids of degrees

The sum of the homogeneous pieces indexed by an additive submonoid is a
subalgebra. It inherits the ambient grading, with all excluded pieces zero.
This restricts a Laurent grading to a positive coefficient algebra before
taking its degree completion.

The underlying module is `Mei.shiftedSubmodule` at shift zero; multiplication
reuses its existing API. Homogeneity follows from the support characterization,
and excluded pieces vanish by independence of the ambient decomposition.
The induced algebra grading is
`Subalgebra.gradedAlgebra`, rather than a second decomposition construction.
-/

public section

noncomputable section

namespace Mei

variable {R A Γ : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid Γ] (𝒜 : Γ → Submodule R A) [SetLike.GradedMonoid 𝒜]
  (P : AddSubmonoid Γ)

/-- The subalgebra supported on the chosen additive submonoid of degrees. -/
def supportedSubalgebra : Subalgebra R A :=
  (shiftedSubmodule 𝒜 P 0).toSubalgebra
    (le_shiftedSubmodule 𝒜 P 0 P.zero_mem (by simpa using SetLike.one_mem_graded 𝒜))
    (fun _ _ hx hy => by
      simpa only [zero_add] using
        shiftedSubmodule_mul_le 𝒜 P 0 0 (Submodule.mul_mem_mul hx hy))

/-- The underlying module is the module supported in the zero translate of `P`. -/
@[simp]
theorem supportedSubalgebra_toSubmodule :
    (supportedSubalgebra 𝒜 P).toSubmodule = shiftedSubmodule 𝒜 P 0 := by
  simp [supportedSubalgebra]

/-- Every allowed homogeneous piece belongs to the supported subalgebra. -/
theorem le_supportedSubalgebra {n : Γ} (hn : n ∈ P) :
    𝒜 n ≤ (supportedSubalgebra 𝒜 P).toSubmodule := by
  rw [supportedSubalgebra_toSubmodule]
  simpa only [zero_add] using le_shiftedSubmodule 𝒜 P 0 hn

/-- A subalgebra contains the supported subalgebra exactly when it contains its pieces. -/
theorem supportedSubalgebra_le_iff (B : Subalgebra R A) :
    supportedSubalgebra 𝒜 P ≤ B ↔ ∀ n ∈ P, 𝒜 n ≤ B.toSubmodule := by
  constructor
  · intro h n hn x hx
    exact h (le_supportedSubalgebra 𝒜 P hn hx)
  · intro h
    have hs : shiftedSubmodule 𝒜 P 0 ≤ B.toSubmodule := by
      simpa only [shiftedSubmodule_def, zero_add, iSup_le_iff] using
        (fun n : P => h n n.property)
    rw [← supportedSubalgebra_toSubmodule] at hs
    exact hs

end Mei

namespace Mei

variable {R A Γ : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid Γ] [DecidableEq Γ] (𝒜 : Γ → Submodule R A) [GradedAlgebra 𝒜]
  (P : AddSubmonoid Γ)

/-- Membership means that every excluded ambient homogeneous component vanishes. -/
@[simp]
theorem mem_supportedSubalgebra_iff (x : A) :
    x ∈ supportedSubalgebra 𝒜 P ↔
      ∀ n, n ∉ P → (DirectSum.decompose 𝒜 x n : A) = 0 := by
  classical
  rw [← Subalgebra.mem_toSubmodule, supportedSubalgebra_toSubmodule]
  simpa only [shiftedSubmodule_def, zero_add, iSup_subtype, SetLike.mem_coe] using
    Mei.DirectSum.mem_iSup_iff_decompose_eq_zero 𝒜 (P : Set Γ)

/-- The supported subalgebra is closed under ambient homogeneous projections. -/
theorem supportedSubalgebra_isHomogeneous :
    DirectSum.SetLike.IsHomogeneous 𝒜 (supportedSubalgebra 𝒜 P) := by
  simpa only [DirectSum.SetLike.IsHomogeneous, ← Subalgebra.mem_toSubmodule,
    supportedSubalgebra_toSubmodule, shiftedSubmodule_def, zero_add, iSup_subtype,
    SetLike.mem_coe] using
    Mei.DirectSum.iSup_isHomogeneous 𝒜 (P : Set Γ)

/-- Restrict the ambient grading to the supported subalgebra. -/
instance instGradedAlgebraSupportedSubalgebra :
    GradedAlgebra ((supportedSubalgebra 𝒜 P).grading 𝒜) :=
  Subalgebra.gradedAlgebra (supportedSubalgebra_isHomogeneous 𝒜 P)

/-- No excluded degree survives in the supported algebra's grading. -/
@[simp]
theorem supportedSubalgebra_grading_eq_bot {n : Γ} (hn : n ∉ P) :
    (supportedSubalgebra 𝒜 P).grading 𝒜 n = ⊥ := by
  have hd : Disjoint (supportedSubalgebra 𝒜 P).toSubmodule (𝒜 n) := by
    rw [supportedSubalgebra_toSubmodule]
    simpa only [shiftedSubmodule_def, zero_add, iSup_subtype, SetLike.mem_coe] using
      ((DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep.disjoint_biSup hn).symm
  ext x
  simpa only [Subalgebra.mem_grading_iff, Submodule.mem_bot] using
    (Submodule.mem_right_iff_eq_zero_of_disjoint hd (x := x))

end Mei
