/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Basic
public import Mei.Algebra.Lie.BCH.Completion

/-!
# Composition of tropical pairings

Tropical pairings compose when the first character map lands in the character
subspace on which the second is defined. Their Lie maps then compose on the
positive character-restricted algebras, and their completed BCH maps compose
with the original cutoff moduli. In particular, intermediate character spaces
need not be the whole dual space, and degree maps need not be injective.

The construction uses `TropicalPairing.gradedLieHom`, Mathlib's
`LinearMap.codRestrict` and homogeneous decomposition, and the composition law
for `GradedLieHom.completedMap`. The pairing condition follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.TropicalPairing

open Mei.LogarithmicVectorField

section

variable {R Γ Λ Γ' Λ' Γ'' Λ'' : Type*} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  [AddCommMonoid Γ''] [AddCommMonoid Λ'']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {f : PositiveDegrees Γ''}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {U : Submodule R (Λ →+ R)} {V : Submodule R (Λ' →+ R)}

/-- The identity pairing on a selected character subspace. -/
def id (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (U : Submodule R (Λ →+ R)) :
    TropicalPairing (d := d) (e := d) (ρ := ρ) (ρ' := ρ) U where
  degreeMap := PositiveDegreeMap.id d
  characterMap := U.subtype
  eval_eq m n _ := by simp

@[simp]
theorem id_degreeMap : (id d ρ U).degreeMap = PositiveDegreeMap.id d := (rfl)

@[simp]
theorem id_characterMap (m : U) : (id d ρ U).characterMap m = m.val := (rfl)

/-- The identity pairing keeps characters in its selected subspace. -/
theorem id_characterMap_mem (m : U) : (id d ρ U).characterMap m ∈ U := m.property

variable (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U)
  (q : TropicalPairing (d := e) (e := f) (ρ := ρ') (ρ' := ρ'') V)

/-- Compose pairings on their actual character domains. The cutoff modulus is
`p.degreeMap.modulus ∘ q.degreeMap.modulus`. -/
def comp (q : TropicalPairing (d := e) (e := f) (ρ := ρ') (ρ' := ρ'') V)
    (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U)
    (h : ∀ m, p.characterMap m ∈ V) :
    TropicalPairing (d := d) (e := f) (ρ := ρ) (ρ' := ρ'') U where
  degreeMap := q.degreeMap.comp p.degreeMap
  characterMap := q.characterMap.comp (p.characterMap.codRestrict V h)
  eval_eq m n hn := by
    simpa only [LinearMap.comp_apply, LinearMap.codRestrict_apply,
      PositiveDegreeMap.comp_apply] using
      (q.eval_eq ((p.characterMap.codRestrict V h) m) (p.degreeMap.map_mem hn)).trans
        (by simpa only [LinearMap.codRestrict_apply] using p.eval_eq m hn)

@[simp]
theorem comp_degreeMap (h : ∀ m, p.characterMap m ∈ V) :
    (q.comp p h).degreeMap = q.degreeMap.comp p.degreeMap := (rfl)

@[simp]
theorem comp_characterMap (h : ∀ m, p.characterMap m ∈ V) (m : U) :
    (q.comp p h).characterMap m = q.characterMap ⟨p.characterMap m, h m⟩ := (rfl)

/-- A composite keeps characters in any subspace containing the second character image. -/
theorem comp_characterMap_mem {W : Submodule R (Λ'' →+ R)}
    (hp : ∀ m, p.characterMap m ∈ V) (hq : ∀ m, q.characterMap m ∈ W) (m : U) :
    (q.comp p hp).characterMap m ∈ W :=
  hq ⟨p.characterMap m, hp m⟩

@[simp]
theorem id_comp (h : ∀ m, p.characterMap m ∈ V) : (id e ρ' V).comp p h = p := by
  apply TropicalPairing.ext
  · simp only [comp_degreeMap, id_degreeMap, PositiveDegreeMap.id_comp]
  · apply LinearMap.ext
    intro m
    simp only [comp_characterMap, id_characterMap]

@[simp]
theorem comp_id : p.comp (id d ρ U) id_characterMap_mem = p := by
  apply TropicalPairing.ext
  · simp only [comp_degreeMap, id_degreeMap, PositiveDegreeMap.comp_id]
  · apply LinearMap.ext
    intro m
    simp only [comp_characterMap, id_characterMap]

/-- Composition is associative on compatible character domains, including its
cutoff modulus. -/
theorem comp_assoc {Γ''' Λ''' : Type*} [AddCommMonoid Γ'''] [AddCommMonoid Λ''']
    {g : PositiveDegrees Γ'''} {ρ''' : Γ''' →+ Λ'''}
    {W : Submodule R (Λ'' →+ R)}
    (r : TropicalPairing (d := f) (e := g) (ρ := ρ'') (ρ' := ρ''') W)
    (hp : ∀ m, p.characterMap m ∈ V) (hq : ∀ m, q.characterMap m ∈ W) :
    (r.comp q hq).comp p hp =
      r.comp (q.comp p hp) (p.comp_characterMap_mem q hp hq) := by
  apply TropicalPairing.ext
  · simp only [comp_degreeMap, PositiveDegreeMap.comp_assoc]
  · apply LinearMap.ext
    intro m
    simp only [comp_characterMap]

/-- A pairing takes values in any character subspace containing its character image.
This permits a second pairing to act without enlarging its domain. -/
theorem gradedLieHom_mem_tropicalSubalgebra (h : ∀ m, p.characterMap m ∈ V)
    (x : tropicalSubalgebra ρ U d) :
    p.gradedLieHom x ∈ tropicalSubalgebra ρ' V e := by
  induction x using tropicalSubalgebra_induction with
  | zero => simpa only [map_zero] using (tropicalSubalgebra ρ' V e).zero_mem
  | homogeneous n m x hm =>
    rw [mem_tropicalSubalgebra_iff, p.coe_gradedLieHom_of_homogeneous x m hm]
    exact (mem_characterSubalgebra_iff ρ' V _).mp
      ((single_mem_characterSubalgebra_iff ρ' V _ _).mpr (h m))
  | add x y hx hy =>
    simpa only [map_add] using (tropicalSubalgebra ρ' V e).add_mem hx hy

/-- The pairing-induced graded Lie map with its codomain restricted to an
intermediate character subspace. -/
def restrictGradedLieHom (h : ∀ m, p.characterMap m ∈ V) :
    GradedLieHom p.degreeMap (tropicalSubalgebraGrading ρ U d)
      (tropicalSubalgebraGrading ρ' V e) where
  toLieHom :=
    { p.gradedLieHom.toLieHom.toLinearMap.codRestrict
        (tropicalSubalgebra ρ' V e).toSubmodule
        (p.gradedLieHom_mem_tropicalSubalgebra h) with
      map_lie' := by
        intro x y
        exact Subtype.ext (p.gradedLieHom.map_lie x y) }
  map_mem hx := by
    rw [tropicalSubalgebraGrading_def, Submodule.mem_comap]
    exact p.gradedLieHom.map_mem hx

/-- Forgetting the intermediate character restriction recovers the original map. -/
@[simp]
theorem coe_restrictGradedLieHom (h : ∀ m, p.characterMap m ∈ V)
    (x : tropicalSubalgebra ρ U d) :
    (p.restrictGradedLieHom h x).val = p.gradedLieHom x := (rfl)

/-- Identity pairings induce the inclusion into the full positive tangent algebra. -/
@[simp]
theorem gradedLieHom_id_apply (x : tropicalSubalgebra ρ U d) :
    (id d ρ U).gradedLieHom x = x.val := by
  induction x using tropicalSubalgebra_induction with
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]
  | homogeneous n m x hm =>
    apply Subtype.ext
    have he := (id d ρ U).coe_gradedLieHom_of_homogeneous x m hm
    simp only [id_degreeMap, PositiveDegreeMap.id_apply, id_characterMap] at he
    exact he.trans hm
  | add x y hx hy => simpa only [map_add, AddMemClass.coe_add] using congrArg₂ (· + ·) hx hy

/-- Restricted to its original character domain, the identity pairing is the
identity Lie map. -/
@[simp]
theorem restrictGradedLieHom_id :
    ((id d ρ U).restrictGradedLieHom id_characterMap_mem).toLieHom = LieHom.id := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  exact gradedLieHom_id_apply x

/-- Composition of pairings agrees with composition of their Lie maps, using
the character restriction needed by the second pairing. -/
@[simp]
theorem gradedLieHom_comp (h : ∀ m, p.characterMap m ∈ V) :
    (q.comp p h).gradedLieHom.toLieHom =
      q.gradedLieHom.toLieHom.comp (p.restrictGradedLieHom h).toLieHom := by
  apply LieHom.ext
  intro x
  simp only [LieHom.comp_apply, GradedLieHom.coe_toLieHom]
  induction x using tropicalSubalgebra_induction with
  | zero => simp only [map_zero]
  | homogeneous n m x hm =>
    apply Subtype.ext
    rw [(q.comp p h).coe_gradedLieHom_of_homogeneous x m hm,
      q.coe_gradedLieHom_of_homogeneous _ ⟨p.characterMap m, h m⟩
        (by simpa only [coe_restrictGradedLieHom] using
          (p.coe_gradedLieHom_of_homogeneous x m hm).symm)]
    simp only [comp_degreeMap, PositiveDegreeMap.comp_apply, comp_characterMap]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The composition law also holds with a restricted final character domain,
so it can be iterated through further pairings. -/
@[simp]
theorem restrictGradedLieHom_comp {W : Submodule R (Λ'' →+ R)}
    (hp : ∀ m, p.characterMap m ∈ V) (hq : ∀ m, q.characterMap m ∈ W) :
    ((q.comp p hp).restrictGradedLieHom (p.comp_characterMap_mem q hp hq)).toLieHom =
        (q.restrictGradedLieHom hq).toLieHom.comp (p.restrictGradedLieHom hp).toLieHom := by
  apply LieHom.ext
  intro x
  apply Subtype.ext
  exact ((q.comp p hp).coe_restrictGradedLieHom _ x).trans
    ((DFunLike.congr_fun (p.gradedLieHom_comp q hp) x).trans
      (q.coe_restrictGradedLieHom hq _).symm)

section Completion

variable [Algebra ℚ R] [DecidableEq Γ]

/-- On the completion of a selected character domain, the identity pairing
induces the identity group homomorphism. -/
@[simp]
theorem completedMap_restrictGradedLieHom_id :
    ((id d ρ U).restrictGradedLieHom id_characterMap_mem).completedMap =
      MonoidHom.id (d.completedBCHGroup (tropicalSubalgebraGrading ρ U d)) := by
  refine (GradedLieHom.completedMap_eq_of_toLieHom_eq _
    (GradedLieHom.id (d := d) (tropicalSubalgebraGrading ρ U d)) ?_).trans
      GradedLieHom.completedMap_id
  simpa only [GradedLieHom.toLieHom_id] using
    (restrictGradedLieHom_id (d := d) (ρ := ρ) (U := U))

end Completion

end

/-! The composition laws for completed maps compare BCH groups of Lie algebras in a
common universe, as `GradedLieHom.completedMap_comp` requires. -/

section CompletionComp

universe u

variable {R Γ Λ Γ' Λ' Γ'' Λ'' : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  [AddCommMonoid Γ''] [AddCommMonoid Λ''] [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {f : PositiveDegrees Γ''}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {U : Submodule R (Λ →+ R)} {V : Submodule R (Λ' →+ R)}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U)
  (q : TropicalPairing (d := e) (e := f) (ρ := ρ') (ρ' := ρ'') V)

/-- Pairing maps compose on completed BCH groups, with cutoff modulus
`p.degreeMap.modulus ∘ q.degreeMap.modulus`. -/
@[simp]
theorem completedMap_gradedLieHom_comp (h : ∀ m, p.characterMap m ∈ V) :
    (q.comp p h).gradedLieHom.completedMap =
      q.gradedLieHom.completedMap.comp (p.restrictGradedLieHom h).completedMap := by
  exact ((q.comp p h).gradedLieHom.completedMap_eq_of_toLieHom_eq
    (q.gradedLieHom.comp (p.restrictGradedLieHom h))
      (by simpa only [GradedLieHom.toLieHom_comp] using p.gradedLieHom_comp q h)).trans
      (GradedLieHom.completedMap_comp _ _)

/-- Restricted completed maps compose through arbitrary intermediate and final
character domains. -/
@[simp]
theorem completedMap_restrictGradedLieHom_comp {W : Submodule R (Λ'' →+ R)}
    (hp : ∀ m, p.characterMap m ∈ V) (hq : ∀ m, q.characterMap m ∈ W) :
    ((q.comp p hp).restrictGradedLieHom (p.comp_characterMap_mem q hp hq)).completedMap =
        (q.restrictGradedLieHom hq).completedMap.comp
          (p.restrictGradedLieHom hp).completedMap := by
  refine (GradedLieHom.completedMap_eq_of_toLieHom_eq _
    ((q.restrictGradedLieHom hq).comp (p.restrictGradedLieHom hp)) ?_).trans
      (GradedLieHom.completedMap_comp _ _)
  simpa only [GradedLieHom.toLieHom_comp] using p.restrictGradedLieHom_comp q hp hq

end CompletionComp

end Mei.TropicalPairing
