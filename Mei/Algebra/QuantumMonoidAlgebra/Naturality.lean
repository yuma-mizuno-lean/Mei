/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Action
public import Mei.Algebra.QuantumMonoidAlgebra.Completion
public import Mei.Algebra.Lie.BCH.RestrictScalars
public import Mei.RingTheory.FilteredAlgebra.Exp.Map
public import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Naturality of completed quantum inner actions

Simultaneous coefficient and exponent maps intertwine the completed quantum BCH
representations. The coefficient map can have a kernel and the degree map can
change cutoffs. In particular, specialization can kill labels or make their
commutators vanish. No genericity of the quantum parameter is required.

The label comparison restricts to rational scalars, applies
`QuantumMonoidAlgebra.positiveGradedLieHom`, and returns to the original scalar
rings through `PositiveDegrees.completedBCHRestrictScalarsEquiv`. The coefficient
comparison is the existing `QuantumMonoidAlgebra.mapPositiveCompletion`.
Finite coefficient inclusions commute with these maps, so coefficient logarithms
and their exponentials commute with completion maps. The conjugation formula
`CoefficientAction.completedBCHAction_apply` then gives action equivariance.

We use Mathlib's `RingHom.toRatAlgHom` and Mei's scalar-restriction,
finite-quotient and completed-exponential naturality APIs. The quantum inner-action
convention follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Example 2.1(iii), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section Coefficients

variable {R S K Γ Γ' : Type*} [CommRing R] [CommRing S] [CommRing K]
  [Algebra K R] [Algebra K S] [AddCommGroup Γ] [AddCommGroup Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ}
  {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →ₐ[K] S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

/-- The ordinary coefficient inclusion commutes with simultaneous quantum maps,
over any common commutative scalar ring. -/
@[simp↓]
theorem positiveMap_positiveLieToCoefficients (x : positiveLieAlgebra q β d) :
    positiveMap φ.toRingHom T.toAddMonoidHom h d.monoid e.monoid
        (fun _ hn => T.map_mem hn) (positiveLieToCoefficients q β d x) =
      positiveLieToCoefficients q' β' e (positiveGradedLieHom φ T h x) := by
  apply Subtype.ext
  rw [coe_positiveMap, coe_positiveLieToCoefficients, coe_positiveLieToCoefficients]
  exact (coe_positiveGradedLieHom_apply φ T h x).symm

variable [DecidableEq Γ] [DecidableEq Γ']

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ hn => d.degree_nonneg hn)
local notation "G" => positiveFiltration q' β' e.monoid e.degree (fun _ hn => e.degree_nonneg hn)
local notation "ℒ" => positiveLieGrading q β d
local notation "ℳ" => positiveLieGrading q' β' e
local notation "ψ" => positiveMap φ.toRingHom T.toAddMonoidHom h d.monoid e.monoid
  (fun _ hn => T.map_mem hn)

/-- At each target cutoff, finite coefficient inclusions commute with the quantum
map from the source cutoff prescribed by the positive degree modulus. -/
@[simp↓]
theorem quotientMap_truncatedCoefficientInclusion (k : ℕ)
    (x : d.truncatedLie ℒ (T.modulus k)) :
    Ideal.quotientMap ((G).ideal (k + 1)) ψ (positiveMap_ideal_le d e T φ.toRingHom h k)
        (truncatedCoefficientInclusion q β d (T.modulus k) x) =
      truncatedCoefficientInclusion q' β' e k
        (e.truncatedRestrictScalarsEquiv (R := K) ℳ k
          ((positiveGradedLieHom φ T h).truncatedMap k le_rfl
            ((d.truncatedRestrictScalarsEquiv (R := K) ℒ (T.modulus k)).symm x))) := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  simp only [truncatedCoefficientInclusion_mk,
    Ideal.quotientMap_mk, PositiveDegrees.truncatedRestrictScalarsEquiv_symm_mk,
    GradedLieHom.truncatedMap_mk, PositiveDegrees.truncatedRestrictScalarsEquiv_mk]
  exact congrArg (Ideal.Quotient.mk _)
    (positiveMap_positiveLieToCoefficients d e T φ h x)

end Coefficients

universe u v

variable {R S : Type u} {Γ Γ' : Type v} [CommRing R] [CommRing S]
  [Algebra ℚ R] [Algebra ℚ S] [AddCommGroup Γ] [AddCommGroup Γ']
  [DecidableEq Γ] [DecidableEq Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ}
  {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ hn => d.degree_nonneg hn)
local notation "G" => positiveFiltration q' β' e.monoid e.degree (fun _ hn => e.degree_nonneg hn)
local notation "ℒ" => positiveLieGrading q β d
local notation "ℳ" => positiveLieGrading q' β' e
local notation "f" => positiveGradedLieHom φ.toRatAlgHom T h
local notation "E" => d.completedBCHRestrictScalarsEquiv (R := ℚ) ℒ
local notation "E'" => e.completedBCHRestrictScalarsEquiv (R := ℚ) ℳ
local notation "Φ" => mapPositiveCompletion d e T φ h
local notation "Ψ" => MonoidHom.comp (MulEquiv.toMonoidHom E')
  (MonoidHom.comp (GradedLieHom.completedMap (R := ℚ) f) (MulEquiv.toMonoidHom (MulEquiv.symm E)))
local notation "ψ" => positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
  (fun _ hn => T.map_mem hn)

namespace CoefficientAction

open scoped CoefficientAction

/-- The coefficient logarithm of a completed label commutes with quantum transport.
The displayed label map uses rational scalar restriction on both sides. -/
@[simp]
theorem mapPositiveCompletion_completedCoefficientLog (g : d.completedBCHGroup ℒ) :
    Φ (completedCoefficientLog q β d g) =
      (completedCoefficientLog q' β' e (Ψ g) : (G).completion) := by
  apply (G).completion_ext
  intro k
  simp only [projection_mapPositiveCompletion, projection_completedCoefficientLog,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv,
    GradedLieHom.projection_completedMap,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv_symm,
    LieHom.log_bchGroupMap, BCHGroup.log_exp]
  exact quotientMap_truncatedCoefficientInclusion d e T φ.toRatAlgHom h k _

/-- Quantum transport preserves the exponential that implements the completed
inner action, even when specialization kills the label. -/
@[simp]
theorem mapPositiveCompletion_completedExp_coefficientLog (g : d.completedBCHGroup ℒ) :
    Φ ((F).completedExp (completedCoefficientLog q β d g)) =
      (G).completedExp (completedCoefficientLog q' β' e (Ψ g)) := by
  have h₁ : (F).ideal 1 ≤ ((G).ideal 1).comap ψ := by
    apply positiveMap_ideal_le_of_degree φ T.toAddMonoidHom h d.monoid e.monoid
      (fun _ hn => T.map_mem hn) d.degree e.degree
      (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn)
    intro n hn hd
    have hn0 : n ≠ 0 := by
      intro hz
      simp only [hz, map_zero] at hd
      omega
    exact e.degree_pos (T.map_mem hn) (T.map_ne_zero hn hn0)
  have hΦ (x : (F).completion) :
      Φ x = (F).mapCompletion (G) ψ T.modulus T.monotone_modulus
        (positiveMap_ideal_le d e T φ h) x := by
    apply (G).completion_ext
    intro k
    exact (projection_mapPositiveCompletion d e T φ h k x).trans
      ((F).projection_mapCompletion (G) ψ T.modulus T.monotone_modulus
        (positiveMap_ideal_le d e T φ h) k x).symm
  exact (hΦ _).trans
    (((F).mapCompletion_completedExp (G) ψ T.modulus T.monotone_modulus
      (positiveMap_ideal_le d e T φ h) h₁ (completedCoefficientLog q β d g)).trans
        (congrArg (G).completedExp (Subtype.ext ((hΦ _).symm.trans
          (mapPositiveCompletion_completedCoefficientLog d e T φ h g)))))

/-- Simultaneous coefficient and exponent transport intertwines the completed
quantum inner actions. Both the label and coefficient may be arbitrary completed
elements; no injectivity, alternatingness or nondegeneracy hypothesis is needed. -/
theorem mapPositiveCompletion_completedBCHAction (g : d.completedBCHGroup ℒ)
    (a : (F).completion) :
    Φ ((F).completedBCHAction d ℒ g a) =
      (G).completedBCHAction e ℳ (Ψ g) (Φ a) := by
  let u := (F).completedExp (completedCoefficientLog q β d g)
  let v := (F).completedExp (completedCoefficientLog q β d g⁻¹)
  calc
    _ = Φ (u * a * v) := congrArg Φ (completedBCHAction_apply q β d g a)
    _ = Φ u * Φ a * Φ v :=
      ((Φ).map_mul (u * a) v).trans
        (congrArg (fun t => t * Φ v) ((Φ).map_mul u a))
    _ = (G).completedExp (completedCoefficientLog q' β' e (Ψ g)) * Φ a *
        (G).completedExp (completedCoefficientLog q' β' e ((Ψ g)⁻¹)) := by
      have hu := mapPositiveCompletion_completedExp_coefficientLog d e T φ h g
      have hv := (mapPositiveCompletion_completedExp_coefficientLog d e T φ h g⁻¹).trans
        (congrArg (fun t => (G).completedExp (completedCoefficientLog q' β' e t))
          ((Ψ).map_inv g))
      exact congrArg₂ (fun x y => x * Φ a * y) hu hv
    _ = _ := (completedBCHAction_apply q' β' e (Ψ g) (Φ a)).symm

end CoefficientAction
end Mei.QuantumMonoidAlgebra
