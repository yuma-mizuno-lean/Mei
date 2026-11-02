/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/
module

public import Mei.RingTheory.GradedAlgebra.FunctionWall.Basic
public import Mei.LinearAlgebra.GradedCorrespondence.Basic

/-!
# Ordinary walls as graph correspondences

A function wall's signed action is an algebra automorphism, so the coefficient
algebra, graded by the exponent monoid, forms a graded correspondence: its
graph. Every exponent is admissible, the left leg is the identity and the right
leg is the action. The homogeneous transfers are exactly the exponent
components of the signed image, so crossing the wall replaces a homogeneous
decoration by its components under the action. The two legs are jointly
injective, and the backward transfers use the inverse action. Slabs use the
admissible-lift correspondences instead.
-/

public noncomputable section

namespace Mei.GradedAlgebra

variable {R A Γ : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddMonoid Γ] [DecidableEq Γ]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
  (𝒢 : Γ → Submodule R A) [GradedAlgebra 𝒢]

/-- The graph correspondence of a function wall's signed action over the
exponent-graded coefficient algebra. The left leg is the identity, the right
leg is the action, so every exponent is admissible and the left lift is the
identity total lift. -/
noncomputable def functionWallGraph (f : (𝒜 0)ˣ) :
    Mei.GradedCorrespondence (B := A) 𝒢 𝒢 Set.univ Set.univ :=
  Mei.GradedCorrespondence.graph 𝒢 𝒢 (functionWallAction 𝒜 f).toLinearEquiv

omit [AddMonoid Γ] [DecidableEq Γ] [GradedAlgebra 𝒢] in
/-- The left leg of the wall's graph correspondence is the identity. -/
@[simp]
theorem functionWallGraph_left (f : (𝒜 0)ˣ) :
    (functionWallGraph 𝒜 𝒢 f).left = LinearMap.id :=
  Mei.GradedCorrespondence.graph_left _

omit [AddMonoid Γ] [DecidableEq Γ] [GradedAlgebra 𝒢] in
/-- The right leg of the wall's graph correspondence is the signed action. -/
@[simp]
theorem functionWallGraph_right (f : (𝒜 0)ˣ) :
    (functionWallGraph 𝒜 𝒢 f).right = (functionWallAction 𝒜 f).toLinearMap :=
  Mei.GradedCorrespondence.graph_right _

/-- Crossing the wall transports a homogeneous exponent decoration to the
exponent components of its signed image. -/
theorem functionWallGraph_transfer (f : (𝒜 0)ˣ) {i : Γ} {a : A} (ha : a ∈ 𝒢 i)
    {w : ℤ} (hw : a ∈ 𝒜 w) (j : Γ) :
    (functionWallGraph 𝒜 𝒢 f).transfer ⟨i, Set.mem_univ i⟩ j ⟨a, ha⟩ =
      DirectSum.decompose 𝒢 (a * algebraMap (𝒜 0) A (f ^ w : (𝒜 0)ˣ)) j := by
  have h1 := Mei.GradedCorrespondence.graph_transfer_apply
    (𝒰 := 𝒢) (𝒱 := 𝒢) (e := (functionWallAction 𝒜 f).toLinearEquiv)
    ⟨i, Set.mem_univ i⟩ j ⟨a, ha⟩
  have h2 : (functionWallAction 𝒜 f).toLinearEquiv ((⟨a, ha⟩ : 𝒢 i) : A) =
      functionWallAction 𝒜 f a := rfl
  rw [h2] at h1
  rw [← functionWallAction_apply_of_mem 𝒜 f hw]
  exact h1

/-- The backward transfer unscales by the inverse action. -/
theorem functionWallGraph_symm_transfer (f : (𝒜 0)ˣ) {i : Γ} {a : A} (ha : a ∈ 𝒢 i)
    {w : ℤ} (hw : a ∈ 𝒜 w) (j : Γ) :
    (functionWallGraph 𝒜 𝒢 f).symm.transfer ⟨i, Set.mem_univ i⟩ j ⟨a, ha⟩ =
      DirectSum.decompose 𝒢 (a * algebraMap (𝒜 0) A ((f⁻¹ ^ w : (𝒜 0)ˣ))) j := by
  have h1 := Mei.GradedCorrespondence.graph_symm_transfer_apply
    (𝒰 := 𝒢) (𝒱 := 𝒢) (e := (functionWallAction 𝒜 f).toLinearEquiv)
    ⟨i, Set.mem_univ i⟩ j ⟨a, ha⟩
  have h2 : (functionWallAction 𝒜 f).toLinearEquiv.symm ((⟨a, ha⟩ : 𝒢 i) : A) =
      functionWallAction 𝒜 f⁻¹ a := by
    rw [functionWallAction_inv]
    rfl
  rw [h2] at h1
  rw [← functionWallAction_apply_of_mem 𝒜 f⁻¹ hw]
  exact h1

omit [AddMonoid Γ] [DecidableEq Γ] [GradedAlgebra 𝒢] in
/-- The two legs are jointly injective: a middle element is determined by its
identity image and its signed image at once. -/
theorem functionWallGraph_jointInjective (f : (𝒜 0)ˣ) :
    Function.Injective
      ((functionWallGraph 𝒜 𝒢 f).left.prod (functionWallGraph 𝒜 𝒢 f).right) :=
  Mei.GradedCorrespondence.graph_injective _

/-- The left total lift of the wall's graph correspondence is the identity. -/
@[simp]
theorem functionWallGraph_liftLeftTotal (f : (𝒜 0)ˣ) :
    (functionWallGraph 𝒜 𝒢 f).liftLeftTotal = LinearMap.id :=
  Mei.GradedCorrespondence.graph_liftLeftTotal _


end Mei.GradedAlgebra
