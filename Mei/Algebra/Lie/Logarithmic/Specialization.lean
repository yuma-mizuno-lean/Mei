/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Coefficient
public import Mei.Algebra.Lie.Graded.RestrictScalars

/-!
# Twisted coefficient specialization of logarithmic fields

A coefficient homomorphism `φ : R →ₐ[K] S` and a multiplicative weight `χ` on
the degree monoid send `z^n ∂_m` to `χ(n) z^n ∂_(φ ∘ m)`. This preserves the
logarithmic bracket, tangency and exponent support, including when coefficients
or weights vanish. Specializations compose by multiplying the second weight by
the image of the first weight.

The positive restriction is a `GradedLieHom` after restricting scalars to `K`.
Its finite truncations and, for rational scalars, completed BCH map are therefore
provided by the existing graded-map constructions. Weights specified only on a
coefficient monoid are handled by `coefficientMonoidGradedLieHom`. These weights
may vanish even over a nontrivial ring. The construction has identity and
composition laws and agrees with ambient specialization when the weight extends.
The coefficient-action comparison applies to any monomial algebra map with the
same generator formula.

The construction uses `Finsupp.lsum` and the existing formal logarithmic bracket.
Twisted coefficient changes follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.LogarithmicVectorField

variable {K R S Γ Λ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (ρ : Γ →+ Λ) (φ : R →ₐ[K] S)

private def coefficientLinearMap (χ : Γ → S) :
    LogarithmicVectorField R Γ Λ ρ →ₗ[K] LogarithmicVectorField S Γ Λ ρ := by
  let f : (Λ →+ R) →ₗ[K] (Λ →+ S) :=
    { toFun m := (φ : R →+ S).comp m
      map_add' m m' := by ext l; simp
      map_smul' r m := by ext l; simp }
  exact (Finsupp.lsum K fun n =>
    χ n • ((single ρ n).restrictScalars K).comp f).comp
      ((toFinsupp ρ).toLinearMap.restrictScalars K)

private theorem coefficientLinearMap_single (χ : Γ → S) (n : Γ) (m : Λ →+ R) :
    coefficientLinearMap ρ φ χ (single ρ n m) =
      single ρ n (χ n • (φ : R →+ S).comp m) := by
  simp [coefficientLinearMap]

private theorem coefficientLinearMap_coeff (χ : Γ → S)
    (x : LogarithmicVectorField R Γ Λ ρ) (n : Γ) :
    toFinsupp ρ (coefficientLinearMap ρ φ χ x) n =
      χ n • (φ : R →+ S).comp (toFinsupp ρ x n) := by
  classical
  induction x using induction_on ρ with
  | h0 => ext l; simp
  | hs j m =>
    rw [coefficientLinearMap_single]
    by_cases h : j = n
    · subst j; simp
    · ext l; simp [h]
  | ha x y hx hy => ext l; simp [hx, hy, mul_add]

variable (χ : Multiplicative Γ →* S)

/-- Change coefficients and multiply each degree by its multiplicative weight.
The common scalar ring is retained in the Lie homomorphism. -/
def coefficientMap :
    LogarithmicVectorField R Γ Λ ρ →ₗ⁅K⁆ LogarithmicVectorField S Γ Λ ρ :=
  { coefficientLinearMap ρ φ (fun n => χ (.ofAdd n)) with
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
  coefficientLinearMap_single ρ φ (fun n => χ (.ofAdd n)) n m

/-- Specialization acts separately on every formal character coefficient. -/
@[simp]
theorem toFinsupp_coefficientMap (x : LogarithmicVectorField R Γ Λ ρ) (n : Γ) :
    toFinsupp ρ (coefficientMap ρ φ χ x) n =
      χ (.ofAdd n) • (φ : R →+ S).comp (toFinsupp ρ x n) := by
  exact coefficientLinearMap_coeff ρ φ (fun n => χ (.ofAdd n)) x n

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

/-- Twisted coefficient specialization preserves tangency and support in any
additive subsemigroup of exponents. -/
theorem coefficientMap_mem_tangentSubalgebra (A : AddSubsemigroup Γ)
    {x : LogarithmicVectorField R Γ Λ ρ} (hx : x ∈ tangentSubalgebra ρ A) :
    coefficientMap ρ φ χ x ∈ tangentSubalgebra ρ A := by
  obtain ⟨ht, hs⟩ := (mem_tangentSubalgebra_iff ρ A x).mp hx
  apply (mem_tangentSubalgebra_iff ρ A _).mpr
  constructor
  · intro n
    simp [ht n]
  · intro n hn
    simp [hs n hn]

/-- Twisted coefficient specialization preserves positive support and tangency. -/
theorem coefficientMap_mem_tropicalVertexLieAlgebra (d : PositiveDegrees Γ)
    {x : LogarithmicVectorField R Γ Λ ρ} (hx : x ∈ tropicalVertexLieAlgebra d ρ) :
    coefficientMap ρ φ χ x ∈ tropicalVertexLieAlgebra d ρ := by
  rw [mem_tropicalVertexLieAlgebra_iff] at hx ⊢
  have hA : x ∈ tangentSubalgebra ρ d.monoid.toAddSubsemigroup :=
    (mem_tangentSubalgebra_iff ρ _ x).mpr
      ⟨hx.1, fun n hn => hx.2 n (Or.inl hn)⟩
  have h := (mem_tangentSubalgebra_iff ρ _ _).mp
    (coefficientMap_mem_tangentSubalgebra ρ φ χ _ hA)
  refine ⟨h.1, ?_⟩
  intro n hn
  rcases hn with hn | rfl
  · exact h.2 n hn
  · simp [hx.2 0 (Or.inr rfl)]

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

namespace Mei.LogarithmicVectorField

variable {K R S Γ Λ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (ρ : Γ →+ Λ) (φ : R →ₐ[K] S) (Q : AddSubmonoid Γ)
  (χ : Multiplicative Q →* S)

private def monoidWeight (n : Γ) : S := by
  classical
  exact if hn : n ∈ Q then χ (.ofAdd ⟨n, hn⟩) else 0

private theorem monoidWeight_mem {n : Γ} (hn : n ∈ Q) :
    monoidWeight Q χ n = χ (.ofAdd ⟨n, hn⟩) := by
  simp [monoidWeight, hn]

private theorem monoidWeight_add {n n' : Γ} (hn : n ∈ Q) (hn' : n' ∈ Q) :
    monoidWeight Q χ (n + n') = monoidWeight Q χ n * monoidWeight Q χ n' := by
  rw [monoidWeight_mem Q χ hn, monoidWeight_mem Q χ hn',
    monoidWeight_mem Q χ (Q.add_mem hn hn'), ← map_mul]
  congr 1

private theorem monoidLinearMap_mem (d : PositiveDegrees Γ)
    (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    coefficientLinearMap ρ φ (monoidWeight Q χ) x.val ∈
      tropicalVertexLieAlgebra d ρ := by
  obtain ⟨ht, hs⟩ := (mem_tropicalVertexLieAlgebra_iff d ρ x.val).mp x.property
  apply (mem_tropicalVertexLieAlgebra_iff d ρ _).mpr
  constructor
  · intro n
    simp [coefficientLinearMap_coeff, ht n]
  · intro n hn
    simp [coefficientLinearMap_coeff, hs n hn]

private theorem monoidLinearMap_lie_single {n n' : Γ}
    (hn : n ∈ Q) (hn' : n' ∈ Q) (m m' : Λ →+ R) :
    coefficientLinearMap ρ φ (monoidWeight Q χ) ⁅single ρ n m, single ρ n' m'⁆ =
      ⁅coefficientLinearMap ρ φ (monoidWeight Q χ) (single ρ n m),
        coefficientLinearMap ρ φ (monoidWeight Q χ) (single ρ n' m')⁆ := by
  simp only [single_bracket_single, coefficientLinearMap_single]
  congr 1
  ext l
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply,
    AddMonoidHom.sub_apply, smul_eq_mul, AlgHom.coe_toAddMonoidHom,
    map_sub, map_mul, monoidWeight_add Q χ hn hn']
  ring

private theorem monoidLinearMap_lie (d : PositiveDegrees Γ) (hQ : d.monoid ≤ Q)
    (x y : tropicalVertexLieAlgebra (R := R) d ρ) :
    coefficientLinearMap ρ φ (monoidWeight Q χ) (⁅x, y⁆ :
        tropicalVertexLieAlgebra d ρ).val =
      ⁅coefficientLinearMap ρ φ (monoidWeight Q χ) x.val,
        coefficientLinearMap ρ φ (monoidWeight Q χ) y.val⁆ := by
  classical
  induction x using DirectSum.Decomposition.inductionOn (tropicalVertexGrading (R := R) d ρ) with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ d.monoid
    · obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n x.val).mp x.property
      induction y using DirectSum.Decomposition.inductionOn
        (tropicalVertexGrading (R := R) d ρ) with
      | zero => simp
      | @homogeneous n' y =>
        by_cases hn' : n' ∈ d.monoid
        · obtain ⟨m', hm'⟩ := (mem_tropicalVertexGrading_iff d ρ n' y.val).mp y.property
          simp only [LieSubalgebra.coe_bracket, ← hm, ← hm']
          exact monoidLinearMap_lie_single ρ φ Q χ (hQ hn) (hQ hn') m m'
        · have hy : (y : tropicalVertexLieAlgebra (R := R) d ρ) = 0 := by
            simpa only [IsPositiveGrading.eq_bot (d := d)
              (ℒ := tropicalVertexGrading d ρ) n' (Or.inl hn'), Submodule.mem_bot]
              using y.property
          simp [hy]
      | add y z hy hz => simp_all
    · have hx : (x : tropicalVertexLieAlgebra (R := R) d ρ) = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d)
          (ℒ := tropicalVertexGrading d ρ) n (Or.inl hn), Submodule.mem_bot]
          using x.property
      simp [hx]
  | add x z hx hz => simp_all

/-- Twisted coefficient change with weights defined only on the coefficient monoid.
Weights may vanish and need not extend to the ambient degree group. The induced
finite and completed BCH maps retain the identity cutoff modulus. -/
def coefficientMonoidGradedLieHom (d : PositiveDegrees Γ) (hQ : d.monoid ≤ Q) :
    GradedLieHom (R := K) (L := tropicalVertexLieAlgebra (R := R) d ρ)
      (L' := tropicalVertexLieAlgebra (R := S) d ρ) (PositiveDegreeMap.id d)
      (fun n => (tropicalVertexGrading (R := R) d ρ n).restrictScalars K)
      (fun n => (tropicalVertexGrading (R := S) d ρ n).restrictScalars K) where
  toLieHom :=
    { toLinearMap :=
        ((coefficientLinearMap ρ φ (monoidWeight Q χ)).comp
          ((tropicalVertexLieAlgebra d ρ).incl.toLinearMap.restrictScalars K)).codRestrict
          ((tropicalVertexLieAlgebra d ρ).toSubmodule.restrictScalars K)
          (monoidLinearMap_mem ρ φ Q χ d)
      map_lie' := by
        intro x y
        exact Subtype.ext (monoidLinearMap_lie ρ φ Q χ d hQ x y) }
  map_mem {n x} hx := by
    simp only [PositiveDegreeMap.id_apply, Submodule.restrictScalars_mem]
    obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n x).mp hx
    exact (mem_tropicalVertexGrading_iff d ρ n _).mpr
      ⟨monoidWeight Q χ n • (φ : R →+ S).comp m,
        (coefficientLinearMap_single ρ φ _ n m).symm.trans
          (congrArg (coefficientLinearMap ρ φ _) hm)⟩

/-- On allowed monoid degrees the specialization multiplies the character by the
specified weight. This also characterizes specialization when a weight vanishes. -/
@[simp]
theorem toFinsupp_coefficientMonoidGradedLieHom (d : PositiveDegrees Γ)
    (hQ : d.monoid ≤ Q) (x : tropicalVertexLieAlgebra (R := R) d ρ)
    {n : Γ} (hn : n ∈ Q) :
    toFinsupp ρ (coefficientMonoidGradedLieHom ρ φ Q χ d hQ x).val n =
      χ (.ofAdd ⟨n, hn⟩) • (φ : R →+ S).comp (toFinsupp ρ x.val n) := by
  exact (coefficientLinearMap_coeff ρ φ (monoidWeight Q χ) x.val n).trans
    (congrArg (fun a => a • (φ : R →+ S).comp (toFinsupp ρ x.val n))
      (monoidWeight_mem Q χ hn))

/-- The specialization is zero outside the coefficient monoid. -/
@[simp]
theorem toFinsupp_coefficientMonoidGradedLieHom_of_not_mem (d : PositiveDegrees Γ)
    (hQ : d.monoid ≤ Q) (x : tropicalVertexLieAlgebra (R := R) d ρ)
    {n : Γ} (hn : n ∉ Q) :
    toFinsupp ρ (coefficientMonoidGradedLieHom ρ φ Q χ d hQ x).val n = 0 := by
  have h := (mem_tropicalVertexLieAlgebra_iff d ρ
    (coefficientMonoidGradedLieHom ρ φ Q χ d hQ x).val).mp
      (coefficientMonoidGradedLieHom ρ φ Q χ d hQ x).property
  exact h.2 n (Or.inl (fun hm => hn (hQ hm)))

/-- A homogeneous field in an allowed degree has the expected twisted character. -/
theorem coe_coefficientMonoidGradedLieHom_of_homogeneous (d : PositiveDegrees Γ)
    (hQ : d.monoid ≤ Q) {n : Γ} (hn : n ∈ d.monoid)
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (m : Λ →+ R)
    (hm : single ρ n m = x.val) :
    (coefficientMonoidGradedLieHom ρ φ Q χ d hQ x).val =
      single ρ n (χ (.ofAdd ⟨n, hQ hn⟩) • (φ : R →+ S).comp m) := by
  exact (congrArg (coefficientLinearMap ρ φ (monoidWeight Q χ)) hm).symm.trans
    ((coefficientLinearMap_single ρ φ _ n m).trans
      (congrArg (fun a => single ρ n (a • (φ : R →+ S).comp m))
        (monoidWeight_mem Q χ (hQ hn))))

/-- Monoid weights that extend to the ambient degrees recover the ambient
specialization. No choice of extension is part of the monoid-local construction. -/
theorem coefficientMonoidGradedLieHom_eq (d : PositiveDegrees Γ) (hQ : d.monoid ≤ Q)
    (ω : Multiplicative Γ →* S)
    (hω : ∀ n : Q, χ (.ofAdd n) = ω (.ofAdd n.val)) :
    coefficientMonoidGradedLieHom ρ φ Q χ d hQ = coefficientGradedLieHom ρ φ ω d := by
  apply GradedLieHom.ext
  intro x
  apply Subtype.ext
  apply LogarithmicVectorField.ext ρ
  intro n
  by_cases hn : n ∈ Q
  · simp [toFinsupp_coefficientMonoidGradedLieHom, hn, hω]
  · have hz := (mem_tropicalVertexLieAlgebra_iff d ρ x.val).mp x.property |>.2 n
      (Or.inl (fun hm => hn (hQ hm)))
    simp [toFinsupp_coefficientMonoidGradedLieHom_of_not_mem, hn, hz]

/-- Constant weight one and the identity coefficients give the identity graded map. -/
@[simp]
theorem coefficientMonoidGradedLieHom_id (d : PositiveDegrees Γ) (hQ : d.monoid ≤ Q) :
    coefficientMonoidGradedLieHom ρ (AlgHom.id K R) Q (1 : Multiplicative Q →* R) d hQ =
      GradedLieHom.id (fun n => (tropicalVertexGrading d ρ n).restrictScalars K) := by
  rw [coefficientMonoidGradedLieHom_eq ρ (AlgHom.id K R) Q 1 d hQ 1 (by simp)]
  exact coefficientGradedLieHom_id ρ d

variable {T : Type*} [CommRing T] [Algebra K T]

/-- Monoid-local specializations compose by multiplying the second weight by the
image of the first. In particular, no unit hypotheses are introduced by composition. -/
@[simp]
theorem coefficientMonoidGradedLieHom_comp (d : PositiveDegrees Γ) (hQ : d.monoid ≤ Q)
    (ψ : S →ₐ[K] T) (ω : Multiplicative Q →* T) :
    (coefficientMonoidGradedLieHom ρ ψ Q ω d hQ).toLieHom.comp
        (coefficientMonoidGradedLieHom ρ φ Q χ d hQ).toLieHom =
      (coefficientMonoidGradedLieHom ρ (ψ.comp φ) Q
        (ω * ψ.toMonoidHom.comp χ) d hQ).toLieHom := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  apply LogarithmicVectorField.ext ρ
  intro n
  by_cases hn : n ∈ Q
  · ext l
    simp [hn, mul_assoc]
  · simp [hn]

/-- A monomial map with the same coefficient-monoid weights intertwines the
coefficient actions. This holds for arbitrary formal fields and coefficient sums,
including coefficients and weights killed by specialization. -/
theorem map_coefficientAction (d : PositiveDegrees Γ) (hQ : d.monoid ≤ Q)
    (f : _root_.AddMonoidAlgebra R Q →ₐ[K] _root_.AddMonoidAlgebra S Q)
    (hf : ∀ (p : Q) r, f (_root_.AddMonoidAlgebra.single p r) =
      _root_.AddMonoidAlgebra.single p (φ r * χ (.ofAdd p)))
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (a : _root_.AddMonoidAlgebra R Q) :
    f (tropicalVertexCoefficientAction d ρ Q hQ x a) =
      tropicalVertexCoefficientAction d ρ Q hQ
        (coefficientMonoidGradedLieHom ρ φ Q χ d hQ x) (f a) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn (tropicalVertexGrading (R := R) d ρ) with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ d.monoid
    · obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n x.val).mp x.property
      rw [tropicalVertexCoefficientAction_of_homogeneous d ρ Q hQ hn x.val m hm,
        tropicalVertexCoefficientAction_of_homogeneous d ρ Q hQ hn
          (coefficientMonoidGradedLieHom ρ φ Q χ d hQ x.val) _
          (coe_coefficientMonoidGradedLieHom_of_homogeneous ρ φ Q χ d hQ hn x.val m hm).symm]
      induction a using _root_.AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp_all
      | single p r =>
        simp only [AddMonoidAlgebra.monomialDerivation_single, hf,
          AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, smul_eq_mul,
          AlgHom.coe_toAddMonoidHom, map_mul]
        have hχ : χ (.ofAdd ((⟨n, hQ hn⟩ : Q) + p)) =
            χ (.ofAdd ⟨n, hQ hn⟩) * χ (.ofAdd p) := by
          rw [ofAdd_add, map_mul]
        rw [hχ]
        congr 1
        ring
    · have hx : (x : tropicalVertexLieAlgebra (R := R) d ρ) = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d)
          (ℒ := tropicalVertexGrading d ρ) n (Or.inl hn), Submodule.mem_bot]
          using x.property
      simp [hx]
  | add x y hx hy => simp_all

end Mei.LogarithmicVectorField

namespace Mei.LogarithmicVectorField

variable {K R S Γ Λ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ] [AddCommMonoid Λ]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {Q : AddSubmonoid Γ}
  {U : Submodule R (Λ →+ R)} {V : Submodule S (Λ →+ S)}
  (φ : R →ₐ[K] S) (χ : Multiplicative Q →* S) (hQ : d.monoid ≤ Q)
  (hφ : ∀ m : U, (φ : R →+ S).comp m.val ∈ V)

include hφ in
/-- Specialization preserves selected character subspaces when coefficient
change sends their characters into the target subspace. Vanishing weights need
no separate treatment. -/
theorem coefficientMonoidGradedLieHom_mem_tropicalSubalgebra
    (x : tropicalSubalgebra ρ U d) :
    coefficientMonoidGradedLieHom ρ φ Q χ d hQ x.val ∈ tropicalSubalgebra ρ V d := by
  rw [mem_tropicalSubalgebra_iff]
  intro n
  by_cases hn : n ∈ Q
  · rw [toFinsupp_coefficientMonoidGradedLieHom ρ φ Q χ d hQ x.val hn]
    exact V.smul_mem _ (hφ ⟨toFinsupp ρ x.val.val n,
      (mem_tropicalSubalgebra_iff ρ U d x.val).mp x.property n⟩)
  · rw [toFinsupp_coefficientMonoidGradedLieHom_of_not_mem ρ φ Q χ d hQ x.val hn]
    exact V.zero_mem

/-- Restrict monoid-local coefficient specialization to its actual source and
target character domains, retaining the common scalar ring. -/
def restrictCoefficientMonoidGradedLieHom :
    GradedLieHom (R := K) (L := tropicalSubalgebra ρ U d)
      (L' := tropicalSubalgebra ρ V d) (PositiveDegreeMap.id d)
      (fun n => (tropicalSubalgebraGrading ρ U d n).restrictScalars K)
      (fun n => (tropicalSubalgebraGrading ρ V d n).restrictScalars K) where
  toLieHom :=
    { toFun x := ⟨coefficientMonoidGradedLieHom ρ φ Q χ d hQ x.val,
        coefficientMonoidGradedLieHom_mem_tropicalSubalgebra φ χ hQ hφ x⟩
      map_add' x y := by apply Subtype.ext; simp
      map_smul' r x := by apply Subtype.ext; simp
      map_lie' := by
        intro x y
        apply Subtype.ext
        simp only [LieSubalgebra.coe_bracket, GradedLieHom.map_lie] }
  map_mem hx := by
    rw [Submodule.restrictScalars_mem, tropicalSubalgebraGrading_def,
      Submodule.mem_comap, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl] at hx ⊢
    exact (coefficientMonoidGradedLieHom ρ φ Q χ d hQ).map_mem hx

/-- Forgetting the target character restriction recovers monoid-local specialization. -/
@[simp]
theorem coe_restrictCoefficientMonoidGradedLieHom (x : tropicalSubalgebra ρ U d) :
    (restrictCoefficientMonoidGradedLieHom φ χ hQ hφ x).val =
      coefficientMonoidGradedLieHom ρ φ Q χ d hQ x.val := (rfl)

end Mei.LogarithmicVectorField
