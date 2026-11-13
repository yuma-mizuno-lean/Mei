/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.PositiveDegreeHom
public import Mei.Algebra.Lie.Graded.Truncation.Basic

/-!
# Graded Lie homomorphisms and split truncations

For a graded section of a retraction, the induced maps split each degree
truncation. Subtracting their composite from the identity gives the projection
onto the truncated kernel.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading)

namespace TauCeti

variable {N M P R L L' L'' : Type*}
  [AddCommMonoid N] [AddCommMonoid M] [AddCommMonoid P] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  {d : PositiveDegrees N} {e : PositiveDegrees M} {p : PositiveDegrees P}

namespace GradedLieHom

variable {T : PositiveDegreeMap d e} {U : PositiveDegreeMap e p}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'} {ℋ : P → Submodule R L''}

/-- Compose degree-preserving maps while retaining the identity degree map. -/
def compId {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    GradedLieHom (PositiveDegreeMap.id d) ℒ ℋ where
  toLieHom := g.toLieHom.comp f.toLieHom
  map_mem hx := by simpa using g.map_mem (f.map_mem hx)

@[simp]
theorem compId_apply {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (x : L) :
    g.compId f x = g (f x) := (rfl)

@[simp]
theorem toLieHom_compId {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    (g.compId f).toLieHom = g.toLieHom.comp f.toLieHom := (rfl)

variable [IsPositiveGrading d ℒ]

/-- The cutoff modulus sends the source degree submodule into the target one.
No decomposition or positivity hypothesis on the target pieces is needed. -/
theorem map_degreeSubmodule_le (f : GradedLieHom T ℒ ℳ) (k : ℕ) :
    (d.degreeSubmodule ℒ (T.modulus k)).map f.toLieHom.toLinearMap ≤
      e.degreeSubmodule ℳ k := by
  exact d.map_degreeSubmodule_le ℒ T ℳ f.toLieHom.toLinearMap
    (fun _ _ hx => f.map_mem hx) k

variable [DecidableEq N] [DecidableEq M] [DecidableEq P]
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading e ℳ] [IsPositiveGrading p ℋ]

/-- The finite graded map is induced on quotients by the underlying Lie map. -/
theorem truncatedMap_eq_mapQ (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) :
    f.truncatedMap k h =
      (d.degreeIdeal ℒ a).mapQ (e.degreeIdeal ℳ k) f.toLieHom
        (fun _ hx => f.map_mem_degreeIdeal k (d.degreeIdeal_antitone ℒ h hx)) := by
  apply (d.degreeIdeal ℒ a).lieHom_qext
  intro x
  rw [LieIdeal.mkQ_apply, truncatedMap_mk]
  exact ((d.degreeIdeal ℒ a).mapQ_apply (e.degreeIdeal ℳ k) f.toLieHom _ x).symm

section SectionComplement

variable {ℳ' : N → Submodule R L'} [GradedLieAlgebra ℳ'] [IsPositiveGrading d ℳ']
  (π : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ')
  (s : GradedLieHom (PositiveDegreeMap.id d) ℳ' ℒ)

/-- The order-`k` endomorphism `id - s ∘ π` of the truncation of `ℒ`. When `s` is a section
of `π`, it is idempotent with image the truncated kernel of `π`
(`isIdempotentElem_idSubSectionComp`, `lieTruncatedMap_idSubSectionComp`). -/
def idSubSectionComp (k : ℕ) : Module.End R (d.truncatedLie ℒ k) :=
  LinearMap.id - (s.truncatedMap k (by simp)).toLinearMap.comp
    (π.truncatedMap k (by simp)).toLinearMap

theorem idSubSectionComp_apply (k : ℕ) (x : d.truncatedLie ℒ k) :
    π.idSubSectionComp s k x =
      x - s.truncatedMap k (by simp) (π.truncatedMap k (by simp) x) := (rfl)

/-- The map fixes every element of the truncated kernel of `π`. -/
@[simp]
theorem idSubSectionComp_of_map_eq_zero (k : ℕ) {x : d.truncatedLie ℒ k}
    (hx : π.truncatedMap k (by simp) x = 0) : π.idSubSectionComp s k x = x := by
  rw [idSubSectionComp_apply, hx, map_zero, sub_zero]

variable {π s} (hsπ : ∀ x, π (s x) = x)
include hsπ

/-- On truncations, `π` is a retraction of its section. -/
@[simp]
theorem lieTruncatedMap_lieTruncatedMap_of_section (k : ℕ) (y : d.truncatedLie ℳ' k) :
    π.truncatedMap k (by simp) (s.truncatedMap k (by simp) y) = y := by
  have hid : (π.truncatedMap k (by simp)).comp (s.truncatedMap k (by simp)) = LieHom.id := by
    apply (d.degreeIdeal ℳ' k).lieHom_qext
    intro x
    simp [LieIdeal.mkQ_apply, hsπ]
  exact DFunLike.congr_fun hid y

/-- For a section, the map kills the truncation of every lifted element. -/
@[simp]
theorem idSubSectionComp_lieTruncatedMap (k : ℕ) (y : d.truncatedLie ℳ' k) :
    π.idSubSectionComp s k (s.truncatedMap k (by simp) y) = 0 := by
  rw [idSubSectionComp_apply, lieTruncatedMap_lieTruncatedMap_of_section hsπ, sub_self]

/-- For a section, the map lands in the truncated kernel of `π`. -/
@[simp]
theorem lieTruncatedMap_idSubSectionComp (k : ℕ) (x : d.truncatedLie ℒ k) :
    π.truncatedMap k (by simp) (π.idSubSectionComp s k x) = 0 := by
  rw [idSubSectionComp_apply, map_sub, lieTruncatedMap_lieTruncatedMap_of_section hsπ, sub_self]

/-- For a section, the map is idempotent: it is the projection onto the truncated kernel
of `π` along the image of `s`. -/
theorem isIdempotentElem_idSubSectionComp (k : ℕ) :
    IsIdempotentElem (π.idSubSectionComp s k) := by
  ext x
  exact idSubSectionComp_of_map_eq_zero π s k (lieTruncatedMap_idSubSectionComp hsπ k x)

/-- For a section, an element fixed by the map lies in the truncated kernel of `π`. -/
theorem lieTruncatedMap_eq_zero_of_idSubSectionComp_eq (k : ℕ) {x : d.truncatedLie ℒ k}
    (hx : π.idSubSectionComp s k x = x) : π.truncatedMap k (by simp) x = 0 := by
  rw [← hx]
  exact lieTruncatedMap_idSubSectionComp hsπ k x

end SectionComplement

end GradedLieHom
end TauCeti
