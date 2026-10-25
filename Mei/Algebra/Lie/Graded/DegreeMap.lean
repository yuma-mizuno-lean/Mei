/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Truncation
public import Mei.Algebra.Lie.Quotient.Map

/-!
# Graded Lie maps and degree truncation towers

A `Mei.GradedLieHom` is a Lie homomorphism taking homogeneous pieces to the
pieces prescribed by a positive degree map. Its cutoff modulus determines a
map from a source truncation to each target truncation. These maps commute with
the surjective transitions in the truncation towers and respect identity and
composition. In particular, they provide compatible finite-order maps for
inverse-limit constructions.

The quotient constructions use `LieIdeal.mapQ` and `LieIdeal.factor`, retaining
the original quotient carriers and computing on representatives.
-/

public section

namespace Mei

variable {N N' N'' R L L' L'' : Type*}
  [AddCommMonoid N] [AddCommMonoid N'] [AddCommMonoid N''] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']

/-- A Lie homomorphism taking degree `n` to degree `T n`. The positive degree
map, including its cutoff modulus, is fixed as a parameter. -/
structure GradedLieHom {d : PositiveDegrees N} {e : PositiveDegrees N'}
    (T : PositiveDegreeMap d e) (ℒ : N → Submodule R L) (ℒ' : N' → Submodule R L')
    extends L →ₗ⁅R⁆ L' where
  /-- Homogeneous elements map to the prescribed homogeneous piece. -/
  map_mem : ∀ {n x}, x ∈ ℒ n → toLieHom x ∈ ℒ' (T n)

namespace GradedLieHom

variable {d : PositiveDegrees N} {e : PositiveDegrees N'} {a : PositiveDegrees N''}
  {T : PositiveDegreeMap d e} {U : PositiveDegreeMap e a}
  {ℒ : N → Submodule R L} {ℒ' : N' → Submodule R L'} {ℒ'' : N'' → Submodule R L''}

instance : FunLike (GradedLieHom T ℒ ℒ') L L' where
  coe f := f.toLieHom
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

/-- A graded Lie homomorphism is determined by its values. -/
@[ext]
theorem ext {f g : GradedLieHom T ℒ ℒ'} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toLieHom (f : GradedLieHom T ℒ ℒ') : ⇑f.toLieHom = f := (rfl)

instance : LinearMapClass (GradedLieHom T ℒ ℒ') R L L' where
  map_add f := f.toLieHom.map_add
  map_smulₛₗ f := f.toLieHom.map_smul

/-- A graded Lie homomorphism preserves brackets. -/
@[simp]
theorem map_lie (f : GradedLieHom T ℒ ℒ') (x y : L) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  f.toLieHom.map_lie x y

/-- Identity graded Lie homomorphism, with identity degree map and modulus. -/
def id (d : PositiveDegrees N) (ℒ : N → Submodule R L) :
    GradedLieHom (PositiveDegreeMap.id d) ℒ ℒ where
  toLieHom := LieHom.id
  map_mem hx := by simpa using hx

@[simp]
theorem id_toLieHom : (id d ℒ).toLieHom = LieHom.id := (rfl)

@[simp]
theorem id_apply (x : L) : id d ℒ x = x := (rfl)

/-- Composition of graded Lie homomorphisms, with the composite cutoff modulus. -/
def comp (g : GradedLieHom U ℒ' ℒ'') (f : GradedLieHom T ℒ ℒ') :
    GradedLieHom (U.comp T) ℒ ℒ'' where
  toLieHom := g.toLieHom.comp f.toLieHom
  map_mem hx := by simpa using g.map_mem (f.map_mem hx)

@[simp]
theorem comp_toLieHom (g : GradedLieHom U ℒ' ℒ'') (f : GradedLieHom T ℒ ℒ') :
    (g.comp f).toLieHom = g.toLieHom.comp f.toLieHom := (rfl)

@[simp]
theorem comp_apply (g : GradedLieHom U ℒ' ℒ'') (f : GradedLieHom T ℒ ℒ') (x : L) :
    g.comp f x = g (f x) := (rfl)

variable [DecidableEq N] [DecidableEq N'] [DecidableEq N'']
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℒ'] [GradedLieAlgebra ℒ'']
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℒ'] [IsPositiveGrading a ℒ'']

/-- A graded Lie homomorphism takes the source degree ideal into the target
ideal at the cutoffs prescribed by its modulus. -/
theorem degreeIdeal_le_comap (f : GradedLieHom T ℒ ℒ') (k : ℕ) :
    d.degreeIdeal ℒ (T.modulus k) ≤ (e.degreeIdeal ℒ' k).comap f.toLieHom := by
  rw [← LieSubmodule.toSubmodule_le_toSubmodule, LieIdeal.comap_toSubmodule,
    d.degreeIdeal_toSubmodule, e.degreeIdeal_toSubmodule,
    ← Submodule.map_le_iff_le_comap]
  exact d.map_degreeSubmodule_le ℒ T ℒ' f.toLieHom.toLinearMap
    (fun _ _ hx => f.map_mem hx) k

/-- The induced Lie homomorphism from source order `l` to target order `k`,
where `l` is at least the source cutoff prescribed by the modulus. The default
source order is exactly `T.modulus k`. -/
def truncatedMap (f : GradedLieHom T ℒ ℒ') (k : ℕ)
    (l : ℕ := T.modulus k) (h : T.modulus k ≤ l := by rfl) :
    d.truncatedLie ℒ l →ₗ⁅R⁆ e.truncatedLie ℒ' k :=
  (d.degreeIdeal ℒ l).mapQ (e.degreeIdeal ℒ' k) f.toLieHom
    ((d.degreeIdeal_antitone ℒ h).trans (f.degreeIdeal_le_comap k))

/-- On quotient representatives, truncation applies the original homomorphism. -/
@[simp]
theorem truncatedMap_mk (f : GradedLieHom T ℒ ℒ') (k l : ℕ)
    (h : T.modulus k ≤ l) (x : L) :
    f.truncatedMap k l h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk (f x) := by
  simp [truncatedMap]

/-- Truncating the identity graded map gives the identity. -/
@[simp]
theorem truncatedMap_id (k : ℕ) : (id d ℒ).truncatedMap k k (by simp) = LieHom.id := by
  simp only [truncatedMap, id_toLieHom, LieIdeal.mapQ_id]

/-- Truncation respects composition; successive cutoff moduli compose in reverse order. -/
theorem truncatedMap_comp (g : GradedLieHom U ℒ' ℒ'') (f : GradedLieHom T ℒ ℒ')
    (k l m : ℕ) (hg : U.modulus k ≤ l) (hf : T.modulus l ≤ m) :
    (g.comp f).truncatedMap k m
        (by simpa using (T.monotone_modulus hg).trans hf) =
      (g.truncatedMap k l hg).comp (f.truncatedMap l m hf) := by
  exact (d.degreeIdeal ℒ m).mapQ_comp (e.degreeIdeal ℒ' l) (a.degreeIdeal ℒ'' k)
    f.toLieHom g.toLieHom
    ((d.degreeIdeal_antitone ℒ hf).trans (f.degreeIdeal_le_comap l))
    ((e.degreeIdeal_antitone ℒ' hg).trans (g.degreeIdeal_le_comap k))

end GradedLieHom

namespace PositiveDegrees

variable (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The surjective transition from a higher-order truncation to a lower-order one. -/
def truncationMap {k l : ℕ} (h : k ≤ l) :
    d.truncatedLie ℒ l →ₗ⁅R⁆ d.truncatedLie ℒ k :=
  (d.degreeIdeal ℒ l).factor (d.degreeIdeal ℒ k) (d.degreeIdeal_antitone ℒ h)

/-- A truncation transition retains the same quotient representative. -/
@[simp]
theorem truncationMap_mk {k l : ℕ} (h : k ≤ l) (x : L) :
    d.truncationMap ℒ h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk x := by
  simp [truncationMap]

/-- The transition at the same order is the identity. -/
@[simp]
theorem truncationMap_refl (k : ℕ) : d.truncationMap ℒ (le_refl k) = LieHom.id :=
  LieIdeal.factor_refl _

/-- Successive degree transitions compose to the direct transition. -/
@[simp]
theorem truncationMap_comp {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) :
    (d.truncationMap ℒ hkl).comp (d.truncationMap ℒ hlm) =
      d.truncationMap ℒ (hkl.trans hlm) :=
  LieIdeal.factor_comp _ _ _ _ _

/-- Every class at lower order lifts to a class at higher order. -/
theorem truncationMap_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (d.truncationMap ℒ h) :=
  LieIdeal.factor_surjective _ _ _

end PositiveDegrees

namespace GradedLieHom

variable {d : PositiveDegrees N} {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule R L} {ℒ' : N' → Submodule R L'}
  [DecidableEq N] [DecidableEq N'] [GradedLieAlgebra ℒ] [GradedLieAlgebra ℒ']
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℒ']

/-- Increasing the source cutoff changes the induced map only by precomposition
with the source truncation transition. -/
@[simp]
theorem truncatedMap_comp_truncationMap (f : GradedLieHom T ℒ ℒ')
    {k l m : ℕ} (hl : T.modulus k ≤ l) (h : l ≤ m) :
    (f.truncatedMap k l hl).comp (d.truncationMap ℒ h) =
      f.truncatedMap k m (hl.trans h) := by
  apply (d.degreeIdeal ℒ m).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- The maps of degree truncations commute with the transitions in both towers. -/
theorem truncationMap_comp_truncatedMap (f : GradedLieHom T ℒ ℒ')
    {k l : ℕ} (h : k ≤ l) :
    (e.truncationMap ℒ' h).comp (f.truncatedMap l) =
      (f.truncatedMap k).comp (d.truncationMap ℒ (T.monotone_modulus h)) := by
  exact LieIdeal.factor_comp_mapQ _ _ _ _ _ _ _ _ _

/-- The induced map is homogeneous on the truncated pieces. This statement
allows degree maps that identify distinct source degrees. -/
theorem truncatedMap_mem (f : GradedLieHom T ℒ ℒ') (k l : ℕ)
    (h : T.modulus k ≤ l) {n : N} {x : d.truncatedLie ℒ l}
    (hx : x ∈ d.truncatedGrading ℒ l n) :
    f.truncatedMap k l h x ∈ e.truncatedGrading ℒ' k (T n) := by
  obtain ⟨y, hy, rfl⟩ := (d.mem_truncatedGrading_iff ℒ).mp hx
  rw [LieIdeal.mkQ_apply, truncatedMap_mk]
  exact (e.mem_truncatedGrading_iff ℒ').mpr ⟨f y, f.map_mem hy, rfl⟩

end GradedLieHom
end Mei
