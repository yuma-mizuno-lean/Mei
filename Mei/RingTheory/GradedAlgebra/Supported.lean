/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted
public import TauCeti.RingTheory.GradedAlgebra.Subalgebra

/-!
# Subalgebras supported on additive submonoids of degrees

The sum of the homogeneous pieces indexed by an additive submonoid is a
subalgebra. It inherits the ambient grading, with all excluded pieces zero.
This restricts a Laurent grading to a positive coefficient algebra before
taking its degree completion.

The underlying module is `Mei.shiftedSubmodule` at shift zero; multiplication
and homogeneity reuse its existing API. The induced algebra grading is
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
  [AddCommGroup Γ] [DecidableEq Γ] (𝒜 : Γ → Submodule R A) [GradedAlgebra 𝒜]
  (P : AddSubmonoid Γ)

/-- Membership means that every excluded ambient homogeneous component vanishes. -/
@[simp]
theorem mem_supportedSubalgebra_iff (x : A) :
    x ∈ supportedSubalgebra 𝒜 P ↔
      ∀ n, n ∉ P → (DirectSum.decompose 𝒜 x n : A) = 0 := by
  rw [← Subalgebra.mem_toSubmodule, supportedSubalgebra_toSubmodule]
  simpa only [sub_zero] using (mem_shiftedSubmodule_iff 𝒜 P 0 (x := x))

/-- The supported subalgebra is closed under ambient homogeneous projections. -/
theorem supportedSubalgebra_isHomogeneous :
    DirectSum.SetLike.IsHomogeneous 𝒜 (supportedSubalgebra 𝒜 P) :=
  shiftedSubmodule_isHomogeneous 𝒜 P 0

/-- Restrict the ambient grading to the supported subalgebra. -/
instance instGradedAlgebraSupportedSubalgebra :
    GradedAlgebra ((supportedSubalgebra 𝒜 P).grading 𝒜) :=
  Subalgebra.gradedAlgebra (supportedSubalgebra_isHomogeneous 𝒜 P)

/-- No excluded degree survives in the supported algebra's grading. -/
@[simp]
theorem supportedSubalgebra_grading_eq_bot {n : Γ} (hn : n ∉ P) :
    (supportedSubalgebra 𝒜 P).grading 𝒜 n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply (Submodule.mem_bot R).mpr
  apply Subtype.ext
  have hz := (mem_supportedSubalgebra_iff 𝒜 P x).mp x.property n hn
  simpa only [DirectSum.decompose_of_mem_same 𝒜
    ((Subalgebra.mem_grading_iff _ _).mp hx), ZeroMemClass.coe_zero] using hz

end Mei
