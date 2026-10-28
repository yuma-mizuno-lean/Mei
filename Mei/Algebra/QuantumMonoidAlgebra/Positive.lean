/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Hom
public import Mei.RingTheory.GradedAlgebra.Supported
public import Mei.RingTheory.GradedAlgebra.DegreeFiltration

/-!
# Positive quantum coefficient algebras

Inside the full quantum algebra, retain precisely the exponents in a chosen
additive submonoid. The inherited exponent grading has zero pieces outside
that monoid. A degree nonnegative on the monoid gives a separated multiplicative
two-sided ideal filtration, whose order-`k` quotient retains degrees at most
`k`. Strict positivity and finite degree cutoffs are not required. Membership is
characterized by the quantum basis coefficients, so this filtration can be used
without unfolding submodule suprema. Simultaneous coefficient and exponent maps
restrict to these supported subalgebras and preserve their inherited grading,
identities, and composition.

This is the coefficient algebra to complete before integrating quantum inner
derivations. We reuse `Mei.supportedSubalgebra`, the inherited grading from
`Subalgebra.gradedAlgebra`, and `Mei.GradedAlgebra.degreeFiltration`.
The supported maps restrict `QuantumMonoidAlgebra.map` using Mathlib's
`RingHom.restrict`.
The quantum convention follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(iii).
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

section

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- The subalgebra of quantum coefficients supported in the chosen exponent monoid. -/
abbrev positiveSubalgebra (P : AddSubmonoid Γ) : Subalgebra R (QuantumMonoidAlgebra q β) :=
  supportedSubalgebra (grade q β) P

/-- Positive support is detected by vanishing of the excluded basis coefficients. -/
@[simp]
theorem mem_positiveSubalgebra_iff (P : AddSubmonoid Γ) (x : QuantumMonoidAlgebra q β) :
    x ∈ positiveSubalgebra q β P ↔ ∀ p, p ∉ P → (basis q β).repr x p = 0 := by
  classical
  simp only [positiveSubalgebra, mem_supportedSubalgebra_iff,
    ZeroMemClass.coe_eq_zero, decompose_eq_zero_iff]

/-- A quantum monomial viewed in the positive coefficient algebra. -/
def positiveMonomial (P : AddSubmonoid Γ) (p : P) : positiveSubalgebra q β P :=
  ⟨monomial q β p, le_supportedSubalgebra (grade q β) P p.property
    ((mem_grade_iff q β p _).mpr ⟨1, one_smul _ _⟩)⟩

/-- Inclusion into the full quantum algebra preserves positive monomials. -/
@[simp]
theorem coe_positiveMonomial (P : AddSubmonoid Γ) (p : P) :
    (positiveMonomial q β P p : QuantumMonoidAlgebra q β) = monomial q β p := (rfl)

/-- The zero exponent gives the unit of the positive algebra. -/
@[simp]
theorem positiveMonomial_zero (P : AddSubmonoid Γ) :
    positiveMonomial q β P 0 = 1 := by
  apply Subtype.ext
  simp

/-- Positive monomials retain the quantum multiplication rule. -/
@[simp]
theorem positiveMonomial_mul (P : AddSubmonoid Γ) (p r : P) :
    positiveMonomial q β P p * positiveMonomial q β P r =
      ((q ^ β p r : Rˣ) : R) • positiveMonomial q β P (p + r) := by
  apply Subtype.ext
  simp

variable (P : AddSubmonoid Γ) (δ : Γ →+ ℤ) (hδ : ∀ p ∈ P, 0 ≤ δ p)

/-- The degree filtration of a quantum coefficient algebra whose allowed exponents
have nonnegative degree. -/
def positiveFiltration : AlgFiltration (positiveSubalgebra q β P) := by
  classical
  exact GradedAlgebra.degreeFiltration
    ((positiveSubalgebra q β P).grading (grade q β)) δ
    (fun p hp => supportedSubalgebra_grading_eq_bot (grade q β) P
      (fun h => (not_lt_of_ge (hδ p h)) hp))

open scoped Classical in
/-- Each positive filtration term is the degree ideal of the inherited grading. -/
theorem positiveFiltration_ideal (k : ℕ) :
    (positiveFiltration q β P δ hδ).ideal k =
      GradedAlgebra.degreeIdeal ((positiveSubalgebra q β P).grading (grade q β)) δ
        (fun p hp => supportedSubalgebra_grading_eq_bot (grade q β) P
          (fun h => (not_lt_of_ge (hδ p h)) hp)) k := by
  classical
  rw [positiveFiltration, GradedAlgebra.degreeFiltration_ideal]

/-- Forgetting ideal multiplication gives the degree tail of the inherited grading. -/
@[simp]
theorem positiveFiltration_ideal_restrictScalars (k : ℕ) :
    ((positiveFiltration q β P δ hδ).ideal k).restrictScalars R =
      Mei.DirectSum.degreeTail ((positiveSubalgebra q β P).grading (grade q β)) δ k := by
  classical
  rw [positiveFiltration, GradedAlgebra.degreeFiltration_ideal,
    GradedAlgebra.degreeIdeal_restrictScalars]

/-- A filtration term consists exactly of coefficients supported above its lower bound. -/
theorem mem_positiveFiltration_iff (k : ℕ) (x : positiveSubalgebra q β P) :
    x ∈ (positiveFiltration q β P δ hδ).ideal k ↔
      ∀ p, δ p < k → (basis q β).repr (x : QuantumMonoidAlgebra q β) p = 0 := by
  classical
  rw [positiveFiltration, GradedAlgebra.degreeFiltration_ideal,
    GradedAlgebra.mem_degreeIdeal_iff, Mei.DirectSum.mem_degreeTail_iff]
  constructor
  · intro hx p hp
    have h := congrArg (fun y : positiveSubalgebra q β P =>
      (y : QuantumMonoidAlgebra q β)) (hx p hp)
    rw [Subalgebra.coe_decompose_grading] at h
    exact (decompose_eq_zero_iff q β _ p).mp (ZeroMemClass.coe_eq_zero.mp h)
  · intro hx p hp
    apply Subtype.ext
    rw [Subalgebra.coe_decompose_grading]
    exact ZeroMemClass.coe_eq_zero.mpr ((decompose_eq_zero_iff q β _ p).mpr (hx p hp))

/-- A homogeneous positive monomial has exactly its prescribed filtration order,
unless its scalar coefficient is zero. -/
@[simp]
theorem smul_positiveMonomial_mem_positiveFiltration_iff (k : ℕ) (p : P) (r : R) :
    r • positiveMonomial q β P p ∈ (positiveFiltration q β P δ hδ).ideal k ↔
      r = 0 ∨ (k : ℤ) ≤ δ p := by
  classical
  rw [mem_positiveFiltration_iff]
  simp only [Subalgebra.coe_smul, coe_positiveMonomial, ← basis_apply, _root_.map_smul,
    Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_apply]
  constructor
  · intro h
    by_cases hp : (k : ℤ) ≤ δ p
    · exact Or.inr hp
    · exact Or.inl (by simpa using h p (lt_of_not_ge hp))
  · rintro (rfl | hp)
    · simp
    · intro n hn
      have hnp : (p : Γ) ≠ n := by intro he; subst n; omega
      simp [hnp]

/-- The positive quantum degree filtration is separated. -/
theorem iInf_positiveFiltration_eq_bot :
    (⨅ k, (positiveFiltration q β P δ hδ).ideal k) = ⊥ := by
  classical
  simp only [positiveFiltration, GradedAlgebra.degreeFiltration_ideal]
  exact GradedAlgebra.iInf_degreeIdeal_eq_bot _ _ _

end

variable {R S U Γ Γ' Γ'' : Type*}
  [CommRing R] [CommRing S] [CommRing U]
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  {q : Rˣ} {q' : Sˣ} {q'' : Uˣ}
  {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  {β'' : LinearMap.BilinForm ℤ Γ''}

section Support

variable (φ : R →+* S) (f : Γ →+ Γ')
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
  (P : AddSubmonoid Γ) (P' : AddSubmonoid Γ') (hf : ∀ n ∈ P, f n ∈ P')

include hf in
/-- A quantum map carries coefficients supported on `P` to coefficients supported
on `P'` when the exponent map sends `P` into `P'`. -/
theorem map_mem_positiveSubalgebra {x : QuantumMonoidAlgebra q β}
    (hx : x ∈ positiveSubalgebra q β P) :
    map φ f h x ∈ positiveSubalgebra q' β' P' := by
  have hx' : x ∈ shiftedSubmodule (grade q β) P 0 := by
    rwa [← supportedSubalgebra_toSubmodule (grade q β) P]
  rw [shiftedSubmodule_def] at hx'
  refine Submodule.iSup_induction _
    (motive := fun x => map φ f h x ∈ positiveSubalgebra q' β' P') hx'
    (fun n x hx => ?_) (by simp) (fun x y hx hy => by
      simpa using (positiveSubalgebra q' β' P').add_mem hx hy)
  simp only [zero_add] at hx
  exact le_supportedSubalgebra (grade q' β') P' (hf n n.property)
    (map_mem_grade φ f h hx)

/-- Restrict a simultaneous quantum coefficient and exponent map to positive support. -/
def positiveMap : positiveSubalgebra q β P →+* positiveSubalgebra q' β' P' :=
  (map φ f h).restrict _ _ (fun _ hx => map_mem_positiveSubalgebra φ f h P P' hf hx)

/-- The restricted map agrees with the ambient quantum map. -/
@[simp]
theorem coe_positiveMap (x : positiveSubalgebra q β P) :
    (positiveMap φ f h P P' hf x : QuantumMonoidAlgebra q' β') = map φ f h x := (rfl)

/-- Positive quantum monomials map to the corresponding image monomials. -/
@[simp]
theorem positiveMap_positiveMonomial (p : P) :
    positiveMap φ f h P P' hf (positiveMonomial q β P p) =
      positiveMonomial q' β' P' ⟨f p, hf p p.property⟩ := by
  apply Subtype.ext
  simp

/-- The restricted map applies the coefficient homomorphism to scalars. -/
@[simp]
theorem positiveMap_algebraMap (r : R) :
    positiveMap φ f h P P' hf (algebraMap R _ r) = algebraMap S _ (φ r) := by
  apply Subtype.ext
  simp

/-- The restricted quantum map preserves the inherited homogeneous pieces. -/
theorem positiveMap_mem_grading {n : Γ} {x : positiveSubalgebra q β P}
    (hx : x ∈ (positiveSubalgebra q β P).grading (grade q β) n) :
    positiveMap φ f h P P' hf x ∈
      (positiveSubalgebra q' β' P').grading (grade q' β') (f n) := by
  rw [Subalgebra.mem_grading_iff] at hx ⊢
  simpa only [coe_positiveMap] using map_mem_grade φ f h hx

end Support

/-- Identity coefficient and exponent maps restrict to the identity on positive support. -/
@[simp]
theorem positiveMap_id (P : AddSubmonoid Γ) :
    positiveMap (q := q) (β := β) (RingHom.id R) (AddMonoidHom.id Γ)
      (fun _ _ => by simp) P P (fun _ hn => hn) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  simp only [coe_positiveMap, map_id, RingHom.id_apply]

/-- Positive quantum maps compose in both coefficients and exponents. -/
theorem positiveMap_comp (φ : R →+* S) (ψ : S →+* U) (f : Γ →+ Γ') (g : Γ' →+ Γ'')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (h' : ∀ p r, Units.map ψ.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (g p) (g r))
    (P : AddSubmonoid Γ) (P' : AddSubmonoid Γ') (P'' : AddSubmonoid Γ'')
    (hf : ∀ n ∈ P, f n ∈ P') (hg : ∀ n ∈ P', g n ∈ P'') :
    (positiveMap ψ g h' P' P'' hg).comp (positiveMap φ f h P P' hf) =
      positiveMap (ψ.comp φ) (g.comp f) (fun p r => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← h', ← h]; rfl)
        P P'' (fun n hn => hg _ (hf n hn)) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  simp

end Mei.QuantumMonoidAlgebra
