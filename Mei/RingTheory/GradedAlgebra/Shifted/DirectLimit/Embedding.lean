/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Embedding finite graded coefficients in the global algebra

If every lattice degree is a difference of positive degrees, the original graded
algebra embeds in the global coefficient algebra. All ambient components are
preserved, and the algebra map agrees
with every supported ordinary coefficient embedding. No completion or support
finiteness assumption is imposed on global coefficients.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A) [GradedAlgebra 𝒜]
  (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)

private def homogeneousGlobalMap (p : Γ) : 𝒜 p →ₗ[R] d.ShiftedDirectLimit 𝒜 :=
  let s := Classical.choose (d.exists_coefficientOrigin_of_spanning hspan p)
  let hs := Classical.choose_spec (d.exists_coefficientOrigin_of_spanning hspan p)
  (d.toShiftedDirectLimitOfChart 𝒜 p s hs).comp
    ((d.shiftedFiltration 𝒜 p).of.comp
      (Submodule.inclusion (by
        simpa only [add_zero] using le_shiftedSubmodule 𝒜 d.monoid p d.monoid.zero_mem)))

private theorem homogeneousGlobalMap_component (p u : Γ) (a : 𝒜 p) :
    d.shiftedDirectLimitComponents 𝒜 (d.homogeneousGlobalMap 𝒜 hspan p a) u =
      DirectSum.decompose 𝒜 (a : A) u := by
  simp only [homogeneousGlobalMap, LinearMap.comp_apply,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart, shiftedHomogeneousComponent_of,
    Submodule.coe_inclusion]

private theorem components_mul_of (p q : Γ) (s t : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hq : q - d.coefficientOrigin t ∈ d.monoid)
    (a : shiftedSubmodule 𝒜 d.monoid p) (b : shiftedSubmodule 𝒜 d.monoid q) (u : Γ) :
    d.shiftedDirectLimitComponents 𝒜
        (d.toShiftedDirectLimitOfChart 𝒜 p s hp ((d.shiftedFiltration 𝒜 p).of a) *
          d.toShiftedDirectLimitOfChart 𝒜 q t hq ((d.shiftedFiltration 𝒜 q).of b)) u =
      DirectSum.decompose 𝒜 ((a : A) * b) u := by
  rw [toShiftedDirectLimitOfChart_mul, shiftedCompletionMul_of,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart, shiftedHomogeneousComponent_of,
    coe_shiftedMul]

private theorem homogeneousGlobalMap_one :
    d.homogeneousGlobalMap 𝒜 hspan 0 (GradedMonoid.GOne.one (A := fun p => 𝒜 p)) = 1 := by
  apply d.shiftedDirectLimitComponents_injective 𝒜
  funext u
  rw [homogeneousGlobalMap_component, shiftedDirectLimitComponents_one, SetLike.coe_gOne]

private theorem homogeneousGlobalMap_mul {p q : Γ} (a : 𝒜 p) (b : 𝒜 q) :
    d.homogeneousGlobalMap 𝒜 hspan (p + q) (GradedMonoid.GMul.mul (A := fun p => 𝒜 p) a b) =
      d.homogeneousGlobalMap 𝒜 hspan p a * d.homogeneousGlobalMap 𝒜 hspan q b := by
  apply d.shiftedDirectLimitComponents_injective 𝒜
  funext u
  rw [homogeneousGlobalMap_component]
  simp only [homogeneousGlobalMap, LinearMap.comp_apply, components_mul_of,
    Submodule.coe_inclusion, SetLike.coe_gMul]

/-- Include the original graded algebra in global coefficients when positive differences span. -/
def toShiftedDirectLimitAlgHom : A →ₐ[R] d.ShiftedDirectLimit 𝒜 :=
  (DirectSum.toAlgebra R (fun p => 𝒜 p) (d.homogeneousGlobalMap 𝒜 hspan)
    (d.homogeneousGlobalMap_one 𝒜 hspan)
    (fun {p q} a b => d.homogeneousGlobalMap_mul 𝒜 hspan (p := p) (q := q) a b)).comp
      (DirectSum.decomposeAlgEquiv 𝒜).toAlgHom

private theorem toShiftedDirectLimitAlgHom_homogeneous (p : Γ) (a : 𝒜 p) :
    d.toShiftedDirectLimitAlgHom 𝒜 hspan (a : A) =
      d.homogeneousGlobalMap 𝒜 hspan p a := by
  simp only [toShiftedDirectLimitAlgHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    DirectSum.decomposeAlgEquiv_apply, DirectSum.decompose_coe,
    DirectSum.toAlgebra_apply]
  exact DirectSum.toSemiring_of (fun i => (d.homogeneousGlobalMap 𝒜 hspan i).toAddMonoidHom)
    (d.homogeneousGlobalMap_one 𝒜 hspan)
    (fun {p q} a b => d.homogeneousGlobalMap_mul 𝒜 hspan (p := p) (q := q) a b) p a

/-- Every ambient component of an original coefficient is preserved. -/
@[simp]
theorem shiftedDirectLimitComponents_toShiftedDirectLimitAlgHom (a : A) (u : Γ) :
    d.shiftedDirectLimitComponents 𝒜 (d.toShiftedDirectLimitAlgHom 𝒜 hspan a) u =
      DirectSum.decompose 𝒜 a u := by
  let E : A →ₗ[R] ∀ u, 𝒜 u :=
    LinearMap.pi (fun u => (DFinsupp.lapply u).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap)
  have he : (d.shiftedDirectLimitComponents 𝒜).comp
      (d.toShiftedDirectLimitAlgHom 𝒜 hspan).toLinearMap = E := by
    apply DirectSum.decompose_lhom_ext 𝒜
    intro p
    apply LinearMap.ext
    intro b
    funext v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
      toShiftedDirectLimitAlgHom_homogeneous, homogeneousGlobalMap_component, E,
      LinearMap.pi_apply, LinearEquiv.coe_coe, DFinsupp.lapply_apply,
      DirectSum.decomposeLinearEquiv_apply]
  have h := congrFun (congrArg (fun f : A →ₗ[R] ∀ u, 𝒜 u => f a) he) u
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, E, LinearMap.pi_apply,
    LinearEquiv.coe_coe, DFinsupp.lapply_apply, DirectSum.decomposeLinearEquiv_apply] using h

/-- No original graded coefficient is lost in the global completion. -/
theorem toShiftedDirectLimitAlgHom_injective :
    Function.Injective (d.toShiftedDirectLimitAlgHom 𝒜 hspan) := by
  intro a b h
  apply (DirectSum.decompose 𝒜).injective
  apply DFinsupp.ext
  intro u
  simpa only [shiftedDirectLimitComponents_toShiftedDirectLimitAlgHom] using
    congrArg (fun x => d.shiftedDirectLimitComponents 𝒜 x u) h

/-- Ordinary coefficients in any translated support have their original global image. -/
theorem toShiftedDirectLimitAlgHom_of_supported (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) (a : shiftedSubmodule 𝒜 d.monoid p) :
    d.toShiftedDirectLimitAlgHom 𝒜 hspan (a : A) =
      d.toShiftedDirectLimitOfChart 𝒜 p s hp ((d.shiftedFiltration 𝒜 p).of a) := by
  apply d.shiftedDirectLimitComponents_injective 𝒜
  funext u
  rw [shiftedDirectLimitComponents_toShiftedDirectLimitAlgHom,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart, shiftedHomogeneousComponent_of]

end Mei.PositiveDegrees
