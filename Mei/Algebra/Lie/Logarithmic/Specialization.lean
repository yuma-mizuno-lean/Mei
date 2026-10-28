/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Grading
public import Mei.Algebra.Lie.Graded.RestrictScalars

/-!
# Twisted coefficient specialization of logarithmic fields

A coefficient homomorphism `φ : R →ₐ[K] S` and a multiplicative weight `χ` on
the degree monoid send `z^n ∂_m` to `χ(n) z^n ∂_(φ ∘ m)`. This preserves the
logarithmic bracket, tangency and positive support, including when coefficients
or weights vanish. Specializations compose by multiplying the second weight by
the image of the first weight.

The positive restriction is a `GradedLieHom` after restricting scalars to `K`.
Its finite truncations and, for rational scalars, completed BCH map are therefore
provided by the existing graded-map constructions. The coefficient-action
comparison applies to any monomial algebra map with the same generator formula.

The construction uses `Finsupp.lsum` and the existing formal logarithmic bracket.
Twisted coefficient changes follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.LogarithmicVectorField

variable {K R S Γ Λ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (ρ : Γ →+ Λ) (φ : R →ₐ[K] S) (χ : Multiplicative Γ →* S)

private def coefficientLinearMap :
    LogarithmicVectorField R Γ Λ ρ →ₗ[K] LogarithmicVectorField S Γ Λ ρ := by
  let f : (Λ →+ R) →ₗ[K] (Λ →+ S) :=
    { toFun m := (φ : R →+ S).comp m
      map_add' m m' := by ext l; simp
      map_smul' r m := by ext l; simp }
  exact (Finsupp.lsum K fun n =>
    χ (.ofAdd n) • ((single ρ n).restrictScalars K).comp f).comp
      ((toFinsupp ρ).toLinearMap.restrictScalars K)

private theorem coefficientLinearMap_single (n : Γ) (m : Λ →+ R) :
    coefficientLinearMap ρ φ χ (single ρ n m) =
      single ρ n (χ (.ofAdd n) • (φ : R →+ S).comp m) := by
  simp [coefficientLinearMap]

/-- Change coefficients and multiply each degree by its multiplicative weight.
The common scalar ring is retained in the Lie homomorphism. -/
def coefficientMap :
    LogarithmicVectorField R Γ Λ ρ →ₗ⁅K⁆ LogarithmicVectorField S Γ Λ ρ :=
  { coefficientLinearMap ρ φ χ with
    map_lie' := by
      intro x y
      simp only [LinearMap.toFun_eq_coe]
      induction x using induction_on ρ with
      | h0 => simp
      | hs n m =>
        induction y using induction_on ρ with
        | h0 => simp
        | hs n' m' =>
          simp only [single_bracket_single, coefficientLinearMap_single]
          congr 1
          ext l
          simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply,
            AddMonoidHom.sub_apply, smul_eq_mul, AlgHom.coe_toAddMonoidHom,
            map_sub, ofAdd_add, map_mul]
          ring
        | ha y z hy hz => simp_all
      | ha x z hx hz => simp_all }

/-- The generator formula for twisted coefficient specialization. -/
@[simp]
theorem coefficientMap_single (n : Γ) (m : Λ →+ R) :
    coefficientMap ρ φ χ (single ρ n m) =
      single ρ n (χ (.ofAdd n) • (φ : R →+ S).comp m) :=
  coefficientLinearMap_single ρ φ χ n m

/-- Specialization acts separately on every formal character coefficient. -/
@[simp]
theorem toFinsupp_coefficientMap (x : LogarithmicVectorField R Γ Λ ρ) (n : Γ) :
    toFinsupp ρ (coefficientMap ρ φ χ x) n =
      χ (.ofAdd n) • (φ : R →+ S).comp (toFinsupp ρ x n) := by
  classical
  induction x using induction_on ρ with
  | h0 => ext l; simp
  | hs j m =>
    by_cases h : j = n
    · subst j; simp
    · ext l; simp [h]
  | ha x y hx hy => ext l; simp [hx, hy, mul_add]

/-- Identity coefficients and the constant weight one give the identity Lie map. -/
@[simp]
theorem coefficientMap_id :
    coefficientMap ρ (AlgHom.id K R) (1 : Multiplicative Γ →* R) = LieHom.id := by
  ext x n l
  simp

variable {T : Type*} [CommRing T] [Algebra K T]

/-- Twisted specializations compose with the transported product of their weights. -/
@[simp]
theorem coefficientMap_comp (ψ : S →ₐ[K] T) (ω : Multiplicative Γ →* T) :
    (coefficientMap ρ ψ ω).comp (coefficientMap ρ φ χ) =
      coefficientMap ρ (ψ.comp φ) (ω * ψ.toMonoidHom.comp χ) := by
  ext x n l
  simp [mul_assoc]

/-- Twisted coefficient specialization preserves positive support and tangency. -/
theorem coefficientMap_mem_tropicalVertexLieAlgebra (d : PositiveDegrees Γ)
    {x : LogarithmicVectorField R Γ Λ ρ} (hx : x ∈ tropicalVertexLieAlgebra d ρ) :
    coefficientMap ρ φ χ x ∈ tropicalVertexLieAlgebra d ρ := by
  obtain ⟨ht, hs⟩ := (mem_tropicalVertexLieAlgebra_iff d ρ x).mp hx
  apply (mem_tropicalVertexLieAlgebra_iff d ρ _).mpr
  constructor
  · intro n
    simp [ht n]
  · intro n hn
    simp [hs n hn]

/-- Twisted coefficient change on positive tropical vertex algebras, with identity
degree map and modulus. Restricting scalars permits arbitrary coefficient algebra
homomorphisms, including quotient maps. -/
def coefficientGradedLieHom (d : PositiveDegrees Γ) :
    GradedLieHom (R := K) (L := tropicalVertexLieAlgebra (R := R) d ρ)
      (L' := tropicalVertexLieAlgebra (R := S) d ρ) (PositiveDegreeMap.id d)
      (fun n => (tropicalVertexGrading (R := R) d ρ n).restrictScalars K)
      (fun n => (tropicalVertexGrading (R := S) d ρ n).restrictScalars K) where
  toLieHom :=
    { toLinearMap :=
        ((coefficientMap ρ φ χ).toLinearMap.comp
          ((tropicalVertexLieAlgebra d ρ).incl.toLinearMap.restrictScalars K)).codRestrict
          ((tropicalVertexLieAlgebra d ρ).toSubmodule.restrictScalars K)
          (fun x => coefficientMap_mem_tropicalVertexLieAlgebra ρ φ χ d x.property)
      map_lie' := by
        intro x y
        apply Subtype.ext
        exact (coefficientMap ρ φ χ).map_lie x.val y.val }
  map_mem {n x} hx := by
    simp only [PositiveDegreeMap.id_apply, Submodule.restrictScalars_mem]
    obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n x).mp hx
    refine (mem_tropicalVertexGrading_iff (R := S) d ρ n _).mpr
      ⟨χ (.ofAdd n) • (φ : R →+ S).comp m, ?_⟩
    exact (coefficientMap_single ρ φ χ n m).symm.trans
      (congrArg (coefficientMap ρ φ χ) hm)

/-- The positive graded restriction agrees with the ambient coefficient map. -/
@[simp]
theorem coe_coefficientGradedLieHom (d : PositiveDegrees Γ)
    (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    (coefficientGradedLieHom ρ φ χ d x).val = coefficientMap ρ φ χ x.val := (rfl)

/-- Identity coefficient specialization gives the identity positive graded map. -/
@[simp]
theorem coefficientGradedLieHom_id (d : PositiveDegrees Γ) :
    coefficientGradedLieHom ρ (AlgHom.id K R) (1 : Multiplicative Γ →* R) d =
      GradedLieHom.id (fun n => (tropicalVertexGrading d ρ n).restrictScalars K) := by
  apply GradedLieHom.ext
  intro x
  apply Subtype.ext
  simp

/-- Composition of positive coefficient specializations agrees with the composite
ambient specialization. This Lie-map equality also compares their induced finite
and completed maps through the generic graded-map API. -/
@[simp]
theorem coefficientGradedLieHom_comp (d : PositiveDegrees Γ)
    (ψ : S →ₐ[K] T) (ω : Multiplicative Γ →* T) :
    (coefficientGradedLieHom ρ ψ ω d).toLieHom.comp
        (coefficientGradedLieHom ρ φ χ d).toLieHom =
      (coefficientGradedLieHom ρ (ψ.comp φ) (ω * ψ.toMonoidHom.comp χ) d).toLieHom := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  simpa only [LieHom.comp_apply, GradedLieHom.coe_toLieHom,
    coe_coefficientGradedLieHom] using
      DFunLike.congr_fun (coefficientMap_comp ρ φ χ ψ ω) x.val

/-- A monomial coefficient map with the same twist intertwines the ordinary
logarithmic actions. No faithfulness or cancellation assumption is needed. -/
theorem map_action (f : _root_.AddMonoidAlgebra R Γ →ₐ[K] _root_.AddMonoidAlgebra S Γ)
    (hf : ∀ n r, f (_root_.AddMonoidAlgebra.single n r) =
      _root_.AddMonoidAlgebra.single n (φ r * χ (.ofAdd n)))
    (x : LogarithmicVectorField R Γ Λ ρ) (a : _root_.AddMonoidAlgebra R Γ) :
    f (action ρ x a) = action ρ (coefficientMap ρ φ χ x) (f a) := by
  induction x using induction_on ρ with
  | h0 => simp
  | hs n m =>
    induction a using _root_.AddMonoidAlgebra.induction_linear with
    | zero => simp
    | single p r =>
      simp only [coefficientMap_single, action_single_apply, hf, ofAdd_add, map_mul,
        AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, smul_eq_mul,
        AlgHom.coe_toAddMonoidHom]
      congr 1
      ring
    | add a b ha hb => simp_all
  | ha x y hx hy => simp_all

end Mei.LogarithmicVectorField
