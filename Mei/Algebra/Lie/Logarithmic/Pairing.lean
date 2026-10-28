/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Grading
public import Mei.Algebra.Lie.BCH.Completion

/-!
# Pairings of tropical vertex Lie algebras

A linear map on a subspace of characters, together with a positive degree map,
induces a Lie homomorphism when it preserves the character evaluations on positive
spatial degrees. Characters outside the chosen subspace are not needed. Distinct
source degrees may merge in the target.

We use `supportedLieSubalgebra` for the character restriction, `Finsupp.lsum` for
transporting finite sums, and `GradedLieHom` for finite and completed group maps.
The pairing condition and logarithmic bracket follow Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.LogarithmicVectorField

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (ρ : Γ →+ Λ) (U : Submodule R (Λ →+ R))

private def characterGrade (n : Γ) : Submodule R (LogarithmicVectorField R Γ Λ ρ) :=
  U.map (single ρ n)

private instance : SetLike.GradedBracket (characterGrade ρ U) (characterGrade ρ U) where
  bracket_mem := by
    rintro n n' x y ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨_, U.sub_mem (U.smul_mem _ hm') (U.smul_mem _ hm),
      (single_bracket_single ρ n n' m m').symm⟩

/-- Formal logarithmic fields all of whose characters belong to `U`. -/
def characterSubalgebra : LieSubalgebra R (LogarithmicVectorField R Γ Λ ρ) :=
  supportedLieSubalgebra (characterGrade ρ U) ⊤

/-- Character restriction is coefficientwise, with no condition outside the support. -/
@[simp]
theorem mem_characterSubalgebra_iff (x : LogarithmicVectorField R Γ Λ ρ) :
    x ∈ characterSubalgebra ρ U ↔ ∀ n, toFinsupp ρ x n ∈ U := by
  constructor
  · intro hx
    have hx' : x ∈ (characterSubalgebra ρ U).toSubmodule := hx
    rw [characterSubalgebra, supportedLieSubalgebra_toSubmodule] at hx'
    refine Submodule.iSup_induction _ (motive := fun x => ∀ n, toFinsupp ρ x n ∈ U)
      hx' ?_ (by simp) ?_
    · rintro n x ⟨m, hm, rfl⟩ j
      by_cases h : n.val = j
      · subst j; simpa using hm
      · simp [h]
    · intro x y hx hy n
      simpa only [map_add, Finsupp.add_apply] using U.add_mem (hx n) (hy n)
  · intro hx
    classical
    rw [← DirectSum.sum_support_decompose (grade ρ) x]
    apply Submodule.sum_mem
    intro n _
    rw [decompose_grade]
    exact le_supportedLieSubalgebra (characterGrade ρ U) (S := ⊤) (by trivial)
      ⟨_, hx n, rfl⟩

/-- A homogeneous field belongs to the character restriction exactly when its
character does. -/
theorem single_mem_characterSubalgebra_iff (n : Γ) (m : Λ →+ R) :
    single ρ n m ∈ characterSubalgebra ρ U ↔ m ∈ U := by
  classical
  rw [mem_characterSubalgebra_iff]
  constructor
  · intro h; simpa using h n
  · intro h j
    by_cases hn : n = j
    · subst j; simpa using h
    · simp [hn]

/-- Restrict the positive tangent Lie algebra to characters in `U`. -/
def tropicalSubalgebra (d : PositiveDegrees Γ) :
    LieSubalgebra R (tropicalVertexLieAlgebra (R := R) d ρ) :=
  (characterSubalgebra ρ U).comap (tropicalVertexLieAlgebra d ρ).incl

/-- Membership in the positive character restriction is coefficientwise. -/
@[simp]
theorem mem_tropicalSubalgebra_iff (d : PositiveDegrees Γ)
    (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    x ∈ tropicalSubalgebra ρ U d ↔ ∀ n, toFinsupp ρ x.val n ∈ U :=
  mem_characterSubalgebra_iff ρ U x.val

/-- The restricted algebra is stable under homogeneous projection. -/
theorem tropicalSubalgebra_isHomogeneous [DecidableEq Γ] (d : PositiveDegrees Γ) :
    DirectSum.SetLike.IsHomogeneous (tropicalVertexGrading (R := R) d ρ)
      (tropicalSubalgebra ρ U d) := by
  intro n x hx
  rw [mem_tropicalSubalgebra_iff] at hx ⊢
  have he := TauCeti.DirectSum.map_decompose_restrict (grade ρ)
    (tropicalVertexGrading (R := R) d ρ) (tropicalVertexLieAlgebra d ρ).incl.toLinearMap
    (by intros; simp only [tropicalVertexGrading_def, Submodule.mem_comap,
      LieHom.coe_toLinearMap]) n x
  simp only [LieHom.coe_toLinearMap, LieSubalgebra.coe_incl] at he
  rw [← mem_characterSubalgebra_iff, he, decompose_grade,
    single_mem_characterSubalgebra_iff]
  exact hx n

/-- The exponent pieces inherited by the positive character restriction. -/
def tropicalSubalgebraGrading (d : PositiveDegrees Γ) (n : Γ) :
    Submodule R (tropicalSubalgebra ρ U d) :=
  (tropicalVertexGrading d ρ n).comap (tropicalSubalgebra ρ U d).incl.toLinearMap

/-- The restricted exponent grading is the inverse image of the tropical vertex grading. -/
theorem tropicalSubalgebraGrading_def (d : PositiveDegrees Γ) :
    tropicalSubalgebraGrading ρ U d = fun n =>
      (tropicalVertexGrading d ρ n).comap (tropicalSubalgebra ρ U d).incl.toLinearMap := (rfl)

/-- The positive character restriction retains an internal Lie grading. -/
instance [DecidableEq Γ] (d : PositiveDegrees Γ) :
    GradedLieAlgebra (tropicalSubalgebraGrading ρ U d) := by
  rw [tropicalSubalgebraGrading_def]
  exact (tropicalSubalgebra ρ U d).gradedLieAlgebra (tropicalVertexGrading d ρ)
    (tropicalSubalgebra_isHomogeneous ρ U d)

instance (d : PositiveDegrees Γ) :
    IsPositiveGrading d (tropicalSubalgebraGrading ρ U d) := by
  rw [tropicalSubalgebraGrading_def]
  exact inferInstanceAs (IsPositiveGrading d (fun n =>
    (tropicalVertexGrading d ρ n).comap (tropicalSubalgebra ρ U d).incl.toLinearMap))

end Mei.LogarithmicVectorField

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

/-- A positive tangent homogeneous field with its character in `U`. -/
def tropicalSingle {n : Γ} (hn : n ∈ d.monoid) (hne : n ≠ 0)
    (m : U) (hm : m.val (ρ n) = 0) : tropicalSubalgebra ρ U d :=
  ⟨⟨single ρ n m.val, single_mem_tropicalVertexLieAlgebra d ρ hn hne m.val hm⟩,
    (single_mem_characterSubalgebra_iff ρ U n m.val).mpr m.property⟩

/-- The ambient formal field of the restricted homogeneous generator. -/
@[simp]
theorem coe_tropicalSingle {n : Γ} (hn : n ∈ d.monoid) (hne : n ≠ 0)
    (m : U) (hm : m.val (ρ n) = 0) :
    (tropicalSingle (d := d) (ρ := ρ) (U := U) hn hne m hm).val.val = single ρ n m.val := (rfl)

/-- A homogeneous restricted field is represented by a character in the selected subspace. -/
theorem mem_tropicalSubalgebraGrading_iff (n : Γ) (x : tropicalSubalgebra ρ U d) :
    x ∈ tropicalSubalgebraGrading ρ U d n ↔ ∃ m : U, single ρ n m.val = x.val.val := by
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n x.val).mp hx
    have hU := (mem_tropicalSubalgebra_iff ρ U d x.val).mp x.property
    refine ⟨⟨m, ?_⟩, hm⟩
    exact (single_mem_characterSubalgebra_iff ρ U n m).mp
      (hm ▸ (mem_characterSubalgebra_iff ρ U x.val.val).mpr hU)
  · rintro ⟨m, hm⟩
    exact (mem_tropicalVertexGrading_iff d ρ n x.val).mpr ⟨m.val, hm⟩

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
`GradedLieHom.truncatedMap` and `GradedLieHom.completedMap` provide its finite
and completed group maps with the original cutoff modulus. -/
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
  p.coe_gradedLieHom_of_homogeneous _ m rfl

end TropicalPairing
end Mei
