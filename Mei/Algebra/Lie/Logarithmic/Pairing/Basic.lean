/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Grading
public import Mei.Algebra.Lie.Graded.PositiveDegreeHom

/-!
# Pairings of tropical vertex Lie algebras

A linear map on a subspace of characters, together with a positive degree map,
induces a Lie homomorphism when it preserves the character evaluations on positive
spatial degrees. Characters outside the chosen subspace are not needed. Distinct
source degrees may merge in the target.

We use the character restriction from the grading layer, `Finsupp.lsum` for
transporting finite sums, and `GradedLieHom` for finite-order Lie maps. Import
`Mei.Algebra.Lie.BCH.Completion` to obtain the induced completed group maps
when `R` is a ℚ-algebra.
The pairing condition and logarithmic bracket follow Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei

variable {R Γ Λ Γ' Λ' : Type*} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} (U : Submodule R (Λ →+ R))

/-- A positive degree map and a linear map on a chosen character subspace,
preserving evaluation on the positive spatial degrees. -/
structure TropicalPairing where
  /-- The degree map, including its cutoff modulus. -/
  degreeMap : PositiveDegreeMap d e
  /-- The map on the selected characters. -/
  characterMap : U →ₗ[R] (Λ' →+ R)
  /-- Character evaluation is preserved on every allowed positive degree. -/
  eval_eq : ∀ (m : U) {n : Γ}, n ∈ d.monoid →
    characterMap m (ρ' (degreeMap n)) = m.val (ρ n)

namespace LogarithmicVectorField

variable (d ρ)

private def characterCoefficients : tropicalSubalgebra ρ U d →ₗ[R] Γ →₀ U where
  toFun x := Finsupp.ofSupportFinite
    (fun n => ⟨toFinsupp ρ x.val.val n,
      (mem_tropicalSubalgebra_iff ρ U d x.val).mp x.property n⟩)
    (by
      apply (toFinsupp ρ x.val.val).support.finite_toSet.subset
      intro n hn
      simp only [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hz
      exact hn (Subtype.ext hz))
  map_add' x y := by apply Finsupp.ext; intro n; apply Subtype.ext; simp
  map_smul' r x := by apply Finsupp.ext; intro n; apply Subtype.ext; simp

private theorem characterCoefficients_apply (x : tropicalSubalgebra ρ U d) (n : Γ) :
    (characterCoefficients (d := d) (ρ := ρ) (U := U) x n).val = toFinsupp ρ x.val.val n := rfl

end LogarithmicVectorField

namespace TropicalPairing

/-- A tropical pairing is determined by its degree and character maps. -/
@[ext]
theorem ext {U : Submodule R (Λ →+ R)}
    {p q : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U}
    (hT : p.degreeMap = q.degreeMap) (hS : p.characterMap = q.characterMap) : p = q := by
  cases p
  cases q
  cases hT
  cases hS
  rfl

section OfDegreeMap

variable {ρ' : Γ' →+ Λ}

/-- A positive degree map compatible on allowed degrees with projections into a common
tangent lattice is a pairing acting as the identity on any character subspace. -/
def ofDegreeMap (T : PositiveDegreeMap d e) (hT : ∀ n ∈ d.monoid, ρ' (T n) = ρ n)
    (U : Submodule R (Λ →+ R)) : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U where
  degreeMap := T
  characterMap := U.subtype
  eval_eq m n hn := by simp [hT n hn]

variable {U} (T : PositiveDegreeMap d e) (hT : ∀ n ∈ d.monoid, ρ' (T n) = ρ n)

@[simp]
theorem ofDegreeMap_degreeMap : (ofDegreeMap T hT U).degreeMap = T := (rfl)

@[simp]
theorem ofDegreeMap_characterMap (m : U) : (ofDegreeMap T hT U).characterMap m = m.val := (rfl)

/-- A pairing from a compatible degree map keeps characters in its selected subspace. -/
theorem ofDegreeMap_characterMap_mem (m : U) : (ofDegreeMap T hT U).characterMap m ∈ U :=
  m.property

end OfDegreeMap

open LogarithmicVectorField

variable {U} (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U)

private def mapLinear : tropicalSubalgebra ρ U d →ₗ[R] LogarithmicVectorField R Γ' Λ' ρ' :=
  (Finsupp.lsum R fun n => (single ρ' (p.degreeMap n)).comp p.characterMap).comp
    (characterCoefficients (d := d) (ρ := ρ) (U := U))

private theorem mapLinear_of_homogeneous {n : Γ} (x : tropicalSubalgebra ρ U d)
    (m : U) (hm : single ρ n m.val = x.val.val) :
    p.mapLinear x = single ρ' (p.degreeMap n) (p.characterMap m) := by
  have hc : characterCoefficients (d := d) (ρ := ρ) (U := U) x = Finsupp.single n m := by
    apply Finsupp.ext
    intro j
    apply Subtype.ext
    simp only [characterCoefficients_apply, ← hm, toFinsupp_single]
    by_cases h : n = j
    · subst j; simp
    · simp [h]
  simp only [mapLinear, LinearMap.comp_apply, hc, Finsupp.lsum_single]

private theorem mapLinear_mem (x : tropicalSubalgebra ρ U d) :
    p.mapLinear x ∈ tropicalVertexLieAlgebra e ρ' := by
  classical
  induction x using DirectSum.Decomposition.inductionOn (tropicalSubalgebraGrading ρ U d) with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ d.monoid ∧ n ≠ 0
    · obtain ⟨m, hm⟩ :=
        (mem_tropicalSubalgebraGrading_iff (d := d) (ρ := ρ) (U := U) n x).mp x.property
      rw [p.mapLinear_of_homogeneous x m hm]
      refine single_mem_tropicalVertexLieAlgebra e ρ'
        (p.degreeMap.map_mem hn.1) (p.degreeMap.map_ne_zero hn.1 hn.2) _ ?_
      rw [p.eval_eq m hn.1]
      have ht := ((mem_tropicalVertexLieAlgebra_iff d ρ x.val.val.val).mp
        x.val.val.property).1 n
      simpa only [← hm, toFinsupp_single, Finsupp.single_eq_same] using ht
    · have hx : (x : tropicalSubalgebra ρ U d) = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d)
          (ℒ := tropicalSubalgebraGrading ρ U d) n (by tauto), Submodule.mem_bot]
          using x.property
      simp [hx]
  | add x y hx hy => simpa only [map_add] using
      (tropicalVertexLieAlgebra e ρ').add_mem hx hy

private theorem mapLinear_bracket_of_homogeneous {n n' : Γ}
    (hn : n ∈ d.monoid) (hn' : n' ∈ d.monoid)
    (x y : tropicalSubalgebra ρ U d) (m m' : U)
    (hm : single ρ n m.val = x.val.val) (hm' : single ρ n' m'.val = y.val.val) :
    p.mapLinear ⁅x, y⁆ = ⁅p.mapLinear x, p.mapLinear y⁆ := by
  let mb : U := m.val (ρ n') • m' - m'.val (ρ n) • m
  have hb : single ρ (n + n') mb.val = (⁅x, y⁆ : tropicalSubalgebra ρ U d).val.val := by
    simp only [LieSubalgebra.coe_bracket, ← hm, ← hm', single_bracket_single,
      mb, Submodule.coe_sub, Submodule.coe_smul]
  rw [p.mapLinear_of_homogeneous _ mb hb,
    p.mapLinear_of_homogeneous _ m hm, p.mapLinear_of_homogeneous _ m' hm',
    single_bracket_single, map_add]
  congr 1
  simpa only [mb, p.eval_eq m hn', p.eval_eq m' hn] using
    p.characterMap.map_sub (m.val (ρ n') • m') (m'.val (ρ n) • m)
      |>.trans (congrArg₂ (· - ·)
        (p.characterMap.map_smul (m.val (ρ n')) m')
        (p.characterMap.map_smul (m'.val (ρ n)) m))

private def lieHom :
    tropicalSubalgebra ρ U d →ₗ⁅R⁆ tropicalVertexLieAlgebra (R := R) e ρ' := by
  classical
  exact
  { p.mapLinear.codRestrict (tropicalVertexLieAlgebra e ρ').toSubmodule p.mapLinear_mem with
    map_lie' := by
      intro x y
      apply Subtype.ext
      simp only [LinearMap.toFun_eq_coe, LinearMap.codRestrict_apply,
        LieSubalgebra.coe_bracket]
      induction x using DirectSum.Decomposition.inductionOn
        (tropicalSubalgebraGrading ρ U d) with
      | zero => simp
      | @homogeneous n x =>
        by_cases hn : n ∈ d.monoid
        · induction y using DirectSum.Decomposition.inductionOn
            (tropicalSubalgebraGrading ρ U d) with
          | zero => simp
          | @homogeneous n' y =>
            by_cases hn' : n' ∈ d.monoid
            · obtain ⟨m, hm⟩ :=
                (mem_tropicalSubalgebraGrading_iff (d := d) (ρ := ρ) (U := U) n x).mp x.property
              obtain ⟨m', hm'⟩ :=
                (mem_tropicalSubalgebraGrading_iff (d := d) (ρ := ρ) (U := U) n' y).mp y.property
              exact p.mapLinear_bracket_of_homogeneous hn hn' x y m m' hm hm'
            · have hy : (y : tropicalSubalgebra ρ U d) = 0 := by
                simpa only [IsPositiveGrading.eq_bot (d := d)
                  (ℒ := tropicalSubalgebraGrading ρ U d) n' (Or.inl hn'), Submodule.mem_bot]
                  using y.property
              simp [hy]
          | add y z hy hz => simp_all
        · have hx : (x : tropicalSubalgebra ρ U d) = 0 := by
            simpa only [IsPositiveGrading.eq_bot (d := d)
              (ℒ := tropicalSubalgebraGrading ρ U d) n (Or.inl hn), Submodule.mem_bot]
              using x.property
          simp [hx]
      | add x z hx hz => simp_all }

/-- Transport positive tangent fields along a tropical pairing. The existing
`GradedLieHom.truncatedMap` provides its finite-order Lie map. When `R` is a
ℚ-algebra, applying `.bchGroupMap` to that Lie map gives the finite group map,
and `GradedLieHom.completedMap` gives the completed group map after importing
`Mei.Algebra.Lie.BCH.Completion`, both with the original cutoff modulus. -/
def gradedLieHom :
    GradedLieHom p.degreeMap (tropicalSubalgebraGrading ρ U d)
      (tropicalVertexGrading (R := R) e ρ') where
  toLieHom := p.lieHom
  map_mem {n x} hx := by
    obtain ⟨m, hm⟩ :=
      (mem_tropicalSubalgebraGrading_iff (d := d) (ρ := ρ) (U := U) n x).mp hx
    exact (mem_tropicalVertexGrading_iff e ρ' _ _).mpr
      ⟨p.characterMap m, (p.mapLinear_of_homogeneous x m hm).symm⟩

/-- On a homogeneous field, the pairing transports its degree and its selected
character. -/
theorem coe_gradedLieHom_of_homogeneous {n : Γ}
    (x : tropicalSubalgebra ρ U d) (m : U) (hm : single ρ n m.val = x.val.val) :
    (p.gradedLieHom x).val = single ρ' (p.degreeMap n) (p.characterMap m) :=
  p.mapLinear_of_homogeneous x m hm

/-- The pairing map on a positive tangent generator. -/
@[simp]
theorem coe_gradedLieHom_tropicalSingle {n : Γ}
    (hn : n ∈ d.monoid) (hne : n ≠ 0) (m : U) (hm : m.val (ρ n) = 0) :
    (p.gradedLieHom (tropicalSingle d ρ U hn hne m hm)).val =
      single ρ' (p.degreeMap n) (p.characterMap m) :=
  p.coe_gradedLieHom_of_homogeneous _ m (coe_tropicalSingle d ρ U hn hne m hm).symm

end TropicalPairing
end Mei
