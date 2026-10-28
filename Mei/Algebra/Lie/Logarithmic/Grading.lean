/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Basic
public import Mei.Algebra.Lie.Graded.Supported
public import Mei.Algebra.Lie.Graded.Subalgebra
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Tangent logarithmic vector fields and their grading

Formal logarithmic vector fields decompose by their exponent. The homogeneous
fields whose characters annihilate their spatial degrees are closed under the
bracket. Selecting strictly positive degrees gives the tropical vertex Lie algebra,
with its internal positive grading and ordinary action on the coefficient algebra.
Restricting to a submodule of characters preserves this positive grading.
Here the coefficients are `R`-valued additive characters; comparison with tensor
products of integral tangent characters is a separate base-change identification.

The decomposition uses Mathlib's independence and spanning theorems for
`Finsupp.lsingle`. Restriction uses `LieSubalgebra.gradedLieAlgebra` and
`supportedLieSubalgebra`; character restriction uses `Finsupp.submodule`.
The tangent-character bracket is the logarithmic bracket of Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.LogarithmicVectorField

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (ρ : Γ →+ Λ)

/-- The degree-`n` homogeneous formal logarithmic vector fields. -/
def grade (n : Γ) : Submodule R (LogarithmicVectorField R Γ Λ ρ) :=
  LinearMap.range (single ρ n)

/-- The exponent piece is the range of the homogeneous inclusion. -/
theorem grade_def :
    grade (R := R) ρ = fun n => LinearMap.range (single ρ n) := (rfl)

/-- A homogeneous field has exactly one exponent and an arbitrary character. -/
theorem mem_grade_iff (n : Γ) (x : LogarithmicVectorField R Γ Λ ρ) :
    x ∈ grade ρ n ↔ ∃ m, single ρ n m = x := Iff.rfl

/-- The exponent pieces give an internal Lie grading. -/
noncomputable instance instGradedLieAlgebraGrade [DecidableEq Γ] :
    GradedLieAlgebra (grade (R := R) ρ) where
  toDecomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · simpa only [grade_def, single_def, LinearMap.range_comp] using
        ((toFinsupp (R := R) ρ).symm.toLinearMap.iSupIndep_map
          (toFinsupp ρ).symm.injective (iSupIndep_range_lsingle Γ R (Λ →+ R)))
    · simp only [grade_def, single_def, LinearMap.range_comp, ← Submodule.map_iSup,
        Finsupp.iSup_lsingle_range]
      simp [LinearMap.range_eq_top.mpr (toFinsupp ρ).symm.surjective]
  bracket_mem := by
    intro n n' x y hx hy
    obtain ⟨m, rfl⟩ := (mem_grade_iff ρ n x).mp hx
    obtain ⟨m', rfl⟩ := (mem_grade_iff ρ n' y).mp hy
    rw [single_bracket_single]
    exact ⟨_, rfl⟩

/-- Homogeneous projection selects precisely the character of that exponent. -/
@[simp]
theorem decompose_grade [DecidableEq Γ] (x : LogarithmicVectorField R Γ Λ ρ) (n : Γ) :
    (DirectSum.decompose (grade ρ) x n : LogarithmicVectorField R Γ Λ ρ) =
      single ρ n (toFinsupp ρ x n) := by
  induction x using induction_on ρ with
  | h0 => simp
  | hs n' m =>
    have hmem : single ρ n' m ∈ grade ρ n' := ⟨m, rfl⟩
    by_cases h : n' = n
    · subst n'
      simp [DirectSum.decompose_of_mem_same _ hmem]
    · simp [DirectSum.decompose_of_mem_ne _ hmem h,
        Finsupp.single_eq_of_ne (Ne.symm h)]
  | ha x y hx hy => simp [hx, hy]

/-- Tangent fields of degree `n` have characters annihilating `ρ(n)`. -/
def tangentGrade (n : Γ) : Submodule R (LogarithmicVectorField R Γ Λ ρ) :=
  (LinearMap.ker ((LinearMap.applyₗ' R (R := ℕ) (ρ n)).comp
    (addMonoidHomLequivNat R).toLinearMap)).map (single ρ n)

/-- A tangent homogeneous field is a single character annihilating its spatial degree. -/
theorem mem_tangentGrade_iff (n : Γ) (x : LogarithmicVectorField R Γ Λ ρ) :
    x ∈ tangentGrade ρ n ↔ ∃ m : Λ →+ R, m (ρ n) = 0 ∧ single ρ n m = x := Iff.rfl

/-- Tangency of a homogeneous field is equivalent to tangency of its character. -/
@[simp]
theorem single_mem_tangentGrade_iff (n : Γ) (m : Λ →+ R) :
    single ρ n m ∈ tangentGrade ρ n ↔ m (ρ n) = 0 := by
  rw [mem_tangentGrade_iff]
  constructor
  · rintro ⟨m', hm', he⟩
    exact (single_injective ρ n he) ▸ hm'
  · exact fun hm => ⟨m, hm, rfl⟩

/-- The logarithmic bracket preserves tangency to the total spatial degree. -/
instance : SetLike.GradedBracket (tangentGrade (R := R) ρ) (tangentGrade (R := R) ρ) where
  bracket_mem := by
    intro n n' x y hx hy
    obtain ⟨m, hm, rfl⟩ := (mem_tangentGrade_iff ρ n x).mp hx
    obtain ⟨m', hm', rfl⟩ := (mem_tangentGrade_iff ρ n' y).mp hy
    simp only [vadd_eq_add]
    rw [single_bracket_single, single_mem_tangentGrade_iff]
    simp [hm, hm', mul_comm]

/-- Restrict tangent fields to an additive set of exponents. -/
def tangentSubalgebra (S : AddSubsemigroup Γ) : LieSubalgebra R (LogarithmicVectorField R Γ Λ ρ) :=
  supportedLieSubalgebra (tangentGrade ρ) S

/-- Membership in the tangent subalgebra records tangency and vanishing outside the
chosen exponent set, including when the spatial map has zero directions. -/
theorem mem_tangentSubalgebra_iff (S : AddSubsemigroup Γ) (x : LogarithmicVectorField R Γ Λ ρ) :
    x ∈ tangentSubalgebra ρ S ↔
      (∀ n, toFinsupp ρ x n (ρ n) = 0) ∧ (∀ n ∉ S, toFinsupp ρ x n = 0) := by
  constructor
  · intro hx
    have hx' : x ∈ (supportedLieSubalgebra (tangentGrade ρ) S).toSubmodule := hx
    rw [supportedLieSubalgebra_toSubmodule] at hx'
    refine Submodule.iSup_induction (fun n : S => tangentGrade (R := R) ρ n) (motive := fun x =>
      (∀ n, toFinsupp ρ x n (ρ n) = 0) ∧ (∀ n ∉ S, toFinsupp ρ x n = 0)) hx' ?_
      (by simp) ?_
    · intro n x hx
      obtain ⟨m, hm, rfl⟩ := (mem_tangentGrade_iff ρ n x).mp hx
      constructor
      · intro j
        by_cases h : n.val = j
        · subst j; simpa using hm
        · simp [h]
      · intro j hj
        have h : n.val ≠ j := fun h => hj (h ▸ n.property)
        simp [h]
    · intro x y hx hy
      constructor
      · intro n; simp [hx.1 n, hy.1 n]
      · intro n hn; simp [hx.2 n hn, hy.2 n hn]
  · rintro ⟨ht, hS⟩
    classical
    rw [← DirectSum.sum_support_decompose (grade ρ) x]
    apply Submodule.sum_mem
    intro n _
    rw [decompose_grade]
    by_cases hn : n ∈ S
    · exact le_supportedLieSubalgebra (tangentGrade (R := R) ρ) hn
        ((single_mem_tangentGrade_iff ρ n _).mpr (ht n))
    · simp [hS n hn]

/-- Tangent subalgebras are stable under exponent projection. -/
theorem tangentSubalgebra_isHomogeneous [DecidableEq Γ] (S : AddSubsemigroup Γ) :
    DirectSum.SetLike.IsHomogeneous (grade (R := R) ρ) (tangentSubalgebra ρ S) := by
  intro n x hx
  obtain ⟨ht, hS⟩ := (mem_tangentSubalgebra_iff ρ S x).mp hx
  rw [decompose_grade]
  by_cases hn : n ∈ S
  · exact le_supportedLieSubalgebra (tangentGrade (R := R) ρ) hn
      ((single_mem_tangentGrade_iff ρ n _).mpr (ht n))
  · simp [hS n hn]

end Mei.LogarithmicVectorField

namespace Mei

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ)

/-- The tropical vertex Lie algebra in coefficient-valued characters: formal tangent fields
supported on the nonzero allowed degrees. It retains characters even when their
ordinary action is zero. -/
def tropicalVertexLieAlgebra : LieSubalgebra R (LogarithmicVectorField R Γ Λ ρ) :=
  LogarithmicVectorField.tangentSubalgebra ρ
    { carrier := {n | n ∈ d.monoid ∧ n ≠ 0}
      add_mem' := by
        rintro n n' ⟨hn, hne⟩ ⟨hn', hne'⟩
        refine ⟨d.monoid.add_mem hn hn', ?_⟩
        have hp : 0 < d.degree (n + n') := by
          simpa only [map_add] using add_pos (d.degree_pos hn hne) (d.degree_pos hn' hne')
        intro h
        simp [h] at hp }

/-- Membership is exactly coefficientwise tangency and support in the strictly
positive monoid; no quotient by the kernel of the coefficient action is taken. -/
theorem mem_tropicalVertexLieAlgebra_iff (x : LogarithmicVectorField R Γ Λ ρ) :
    x ∈ tropicalVertexLieAlgebra d ρ ↔
      (∀ n, LogarithmicVectorField.toFinsupp ρ x n (ρ n) = 0) ∧
      (∀ n, n ∉ d.monoid ∨ n = 0 → LogarithmicVectorField.toFinsupp ρ x n = 0) := by
  simp only [tropicalVertexLieAlgebra, LogarithmicVectorField.mem_tangentSubalgebra_iff,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, not_and_or, not_not]

/-- The exponent grading on the positive tangent Lie algebra. -/
def tropicalVertexGrading (n : Γ) : Submodule R (tropicalVertexLieAlgebra (R := R) d ρ) :=
  (LogarithmicVectorField.grade ρ n).comap (tropicalVertexLieAlgebra d ρ).incl.toLinearMap

/-- The positive grading is the inverse image of the ambient exponent grading. -/
theorem tropicalVertexGrading_def :
    tropicalVertexGrading (R := R) d ρ = fun n =>
      (LogarithmicVectorField.grade ρ n).comap
        (tropicalVertexLieAlgebra d ρ).incl.toLinearMap := (rfl)

/-- A homogeneous positive tangent field is represented by a single formal character. -/
theorem mem_tropicalVertexGrading_iff (n : Γ) (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    x ∈ tropicalVertexGrading d ρ n ↔
      ∃ m, LogarithmicVectorField.single ρ n m = (x : LogarithmicVectorField R Γ Λ ρ) := by
  rw [tropicalVertexGrading_def, Submodule.mem_comap]
  exact LogarithmicVectorField.mem_grade_iff ρ n (x : LogarithmicVectorField R Γ Λ ρ)

/-- The tropical vertex Lie algebra is homogeneous in the ambient exponent grading. -/
theorem tropicalVertexLieAlgebra_isHomogeneous [DecidableEq Γ] :
    DirectSum.SetLike.IsHomogeneous (LogarithmicVectorField.grade (R := R) ρ)
      (tropicalVertexLieAlgebra d ρ) :=
  LogarithmicVectorField.tangentSubalgebra_isHomogeneous ρ _

/-- Positive tangent fields inherit the internal exponent decomposition. -/
noncomputable instance instGradedLieAlgebraTropicalVertexGrading [DecidableEq Γ] :
    GradedLieAlgebra (tropicalVertexGrading (R := R) d ρ) := by
  rw [tropicalVertexGrading_def]
  exact (tropicalVertexLieAlgebra d ρ).gradedLieAlgebra (LogarithmicVectorField.grade ρ)
    (tropicalVertexLieAlgebra_isHomogeneous d ρ)

/-- The tropical vertex grading has no piece at zero or outside the positive monoid. -/
instance : IsPositiveGrading d (tropicalVertexGrading (R := R) d ρ) where
  eq_bot n hn := by
    apply eq_bot_iff.mpr
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n x).mp hx
    have hc := ((mem_tropicalVertexLieAlgebra_iff d ρ
      (x : LogarithmicVectorField R Γ Λ ρ)).mp x.property).2 n hn
    have hm0 : m = 0 := by simpa [← hm] using hc
    apply Subtype.ext
    simpa [hm0] using hm.symm

/-- Every tangent character in a nonzero allowed degree defines a positive field. -/
theorem single_mem_tropicalVertexLieAlgebra {n : Γ} (hn : n ∈ d.monoid) (hne : n ≠ 0)
    (m : Λ →+ R) (hm : m (ρ n) = 0) :
    LogarithmicVectorField.single ρ n m ∈ tropicalVertexLieAlgebra d ρ := by
  rw [mem_tropicalVertexLieAlgebra_iff]
  constructor
  · intro j
    by_cases h : n = j
    · subst j; simpa using hm
    · simp [h]
  · intro j hj
    have h : n ≠ j := by rintro rfl; tauto
    simp [h]

end Mei

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

/-- The character restriction is the image of the coefficient submodule. -/
@[simp]
theorem characterSubalgebra_toSubmodule :
    (characterSubalgebra ρ U).toSubmodule =
      (Finsupp.submodule (fun _ : Γ => U)).map (toFinsupp ρ).symm.toLinearMap := by
  simp only [characterSubalgebra, supportedLieSubalgebra_toSubmodule, characterGrade,
    iSup_subtype, AddSubsemigroup.mem_top, iSup_pos, Finsupp.submodule_eq_iSup,
    Submodule.map_iSup, Submodule.map_comp, single_def]

/-- Character restriction is coefficientwise, with no condition outside the support. -/
@[simp]
theorem mem_characterSubalgebra_iff (x : LogarithmicVectorField R Γ Λ ρ) :
    x ∈ characterSubalgebra ρ U ↔ ∀ n, toFinsupp ρ x n ∈ U := by
  rw [← LieSubalgebra.mem_toSubmodule, characterSubalgebra_toSubmodule,
    Submodule.mem_map_equiv, LinearEquiv.symm_symm, Finsupp.mem_submodule_iff]

/-- A homogeneous field belongs to the character restriction exactly when its
character does. -/
theorem single_mem_characterSubalgebra_iff (n : Γ) (m : Λ →+ R) :
    single ρ n m ∈ characterSubalgebra ρ U ↔ m ∈ U := by
  rw [mem_characterSubalgebra_iff, toFinsupp_single]
  simpa only [Submodule.mem_comap, Finsupp.lsingle_apply, Finsupp.mem_submodule_iff] using
    (SetLike.ext_iff.mp (Finsupp.comap_lsingle_submodule (fun _ : Γ => U) n) m)

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

namespace Mei.LogarithmicVectorField

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (U : Submodule R (Λ →+ R))

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

variable {d ρ U} in
/-- Induction on restricted fields: a predicate closed under zero and addition holds
everywhere once it holds on each homogeneous field `single ρ n m` with `m ∈ U`. -/
@[elab_as_elim]
theorem tropicalSubalgebra_induction {motive : tropicalSubalgebra ρ U d → Prop}
    (zero : motive 0)
    (homogeneous : ∀ (n : Γ) (m : U) (x : tropicalSubalgebra ρ U d),
      single ρ n m.val = x.val.val → motive x)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (x : tropicalSubalgebra ρ U d) : motive x := by
  classical
  induction x using DirectSum.Decomposition.inductionOn (tropicalSubalgebraGrading ρ U d) with
  | zero => exact zero
  | @homogeneous n x =>
    obtain ⟨m, hm⟩ := (mem_tropicalSubalgebraGrading_iff d ρ U n x).mp x.property
    exact homogeneous n m x hm
  | add x y hx hy => exact add x y hx hy

end Mei.LogarithmicVectorField
