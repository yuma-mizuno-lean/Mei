/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Truncation
public import Mei.Algebra.PositiveDegrees.Map
public import Mei.Algebra.Lie.Quotient.Map

/-!
# Graded Lie homomorphisms and their truncations

A `Mei.GradedLieHom` carries homogeneous pieces along a specified positive degree
map. Its cutoff modulus controls the degree ideals, so the homomorphism descends
from the source truncation at the prescribed order to each target truncation.
These induced maps respect homogeneous pieces, identities, and composition.

The cutoff estimate needs only positivity of the source pieces; it does not need
an internal decomposition or injectivity of the degree map. In particular,
distinct source degrees may merge in the target.

The induced maps specialize `LieIdeal.mapQ`, which uses `LieIdeal.liftQ` from
Tau Ceti, the universal property of the Lie quotient.
-/

public section

namespace Mei

variable {N M P R L L' L'' : Type*}
  [AddCommMonoid N] [AddCommMonoid M] [AddCommMonoid P] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  {d : PositiveDegrees N} {e : PositiveDegrees M} {p : PositiveDegrees P}

/-- A Lie homomorphism carrying degree `n` to degree `T n`, where `T` includes
the cutoff modulus needed for maps of truncations. -/
structure GradedLieHom (T : PositiveDegreeMap d e)
    (ℒ : N → Submodule R L) (ℳ : M → Submodule R L') extends L →ₗ⁅R⁆ L' where
  /-- Homogeneous elements map to the prescribed homogeneous piece. -/
  map_mem : ∀ {n x}, x ∈ ℒ n → toLieHom x ∈ ℳ (T n)

namespace GradedLieHom

variable {T : PositiveDegreeMap d e} {U : PositiveDegreeMap e p}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'} {ℋ : P → Submodule R L''}

instance : FunLike (GradedLieHom T ℒ ℳ) L L' where
  coe f := f.toLieHom
  coe_injective f g h := by
    have hfg : f.toLieHom = g.toLieHom := DFunLike.coe_injective h
    cases f
    cases g
    cases hfg
    rfl

instance : LinearMapClass (GradedLieHom T ℒ ℳ) R L L' where
  map_add f := f.toLieHom.map_add
  map_smulₛₗ f := f.toLieHom.map_smul

@[simp]
theorem coe_toLieHom (f : GradedLieHom T ℒ ℳ) : ⇑f.toLieHom = f := (rfl)

/-- A graded Lie homomorphism is determined by its values. -/
@[ext]
theorem ext {f g : GradedLieHom T ℒ ℳ} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem map_lie (f : GradedLieHom T ℒ ℳ) (x y : L) :
    f ⁅x, y⁆ = ⁅f x, f y⁆ := f.toLieHom.map_lie x y

/-- The identity graded Lie homomorphism has identity degree map and modulus. -/
def id (ℒ : N → Submodule R L) : GradedLieHom (PositiveDegreeMap.id d) ℒ ℒ where
  toLieHom := LieHom.id
  map_mem hx := by simpa only [LieHom.id_apply, PositiveDegreeMap.id_apply] using hx

@[simp]
theorem id_apply (x : L) : id (d := d) ℒ x = x := (rfl)

/-- Composition carries the composite degree map and its composite cutoff modulus. -/
def comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ) :
    GradedLieHom (U.comp T) ℒ ℋ where
  toLieHom := g.toLieHom.comp f.toLieHom
  map_mem hx := by
    simpa only [PositiveDegreeMap.comp_apply, LieHom.comp_apply] using g.map_mem (f.map_mem hx)

@[simp]
theorem comp_apply (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ) (x : L) :
    g.comp f x = g (f x) := (rfl)

@[simp]
theorem toLieHom_id : (id (d := d) ℒ).toLieHom = LieHom.id := (rfl)

@[simp]
theorem toLieHom_comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ) :
    (g.comp f).toLieHom = g.toLieHom.comp f.toLieHom := (rfl)

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

/-- A graded homomorphism preserves degree ideals at the orders prescribed by its modulus. -/
theorem map_mem_degreeIdeal (f : GradedLieHom T ℒ ℳ) (k : ℕ) {x : L}
    (hx : x ∈ d.degreeIdeal ℒ (T.modulus k)) : f x ∈ e.degreeIdeal ℳ k := by
  apply (LieSubmodule.mem_toSubmodule _).mp
  rw [e.degreeIdeal_toSubmodule]
  have hx' := (LieSubmodule.mem_toSubmodule _).mpr hx
  rw [d.degreeIdeal_toSubmodule] at hx'
  exact f.map_degreeSubmodule_le k (Submodule.mem_map.mpr ⟨x, hx', rfl⟩)

/-- The finite-order Lie homomorphism induced by a graded Lie homomorphism.
The source order may be any `a ≥ T.modulus k`, allowing comparison of cutoffs
without transporting maps between propositionally equal quotient types. -/
def truncatedMap (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ) (h : T.modulus k ≤ a) :
    d.truncatedLie ℒ a →ₗ⁅R⁆ e.truncatedLie ℳ k :=
  (d.degreeIdeal ℒ a).mapQ (e.degreeIdeal ℳ k) f.toLieHom
    (fun _ hx => f.map_mem_degreeIdeal k (d.degreeIdeal_antitone ℒ h hx))

/-- The induced map sends the class of an element to the class of its image. -/
@[simp]
theorem truncatedMap_mk (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) (x : L) :
    f.truncatedMap k h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := by
  exact (d.degreeIdeal ℒ a).mapQ_apply (e.degreeIdeal ℳ k) f.toLieHom _ x

/-- The induced map preserves homogeneous pieces along the original degree map. -/
theorem truncatedMap_mem (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) {n : N} {x : d.truncatedLie ℒ a}
    (hx : x ∈ d.truncatedGrading ℒ a n) :
    f.truncatedMap k h x ∈ e.truncatedGrading ℳ k (T n) := by
  obtain ⟨y, hy, rfl⟩ := (d.mem_truncatedGrading_iff ℒ).mp hx
  refine (e.mem_truncatedGrading_iff ℳ).mpr ⟨f y, f.map_mem hy, ?_⟩
  simpa only [LieIdeal.mkQ_apply] using (f.truncatedMap_mk k h y).symm

/-- Truncation sends the identity graded homomorphism to the identity. -/
@[simp]
theorem truncatedMap_id (k : ℕ) :
    (id (d := d) ℒ).truncatedMap k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k) =
      LieHom.id := by
  apply (d.degreeIdeal ℒ k).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply, LieHom.id_apply]

/-- Truncation respects composition, with source orders controlled by successive moduli. -/
theorem truncatedMap_comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ)
    {a b : ℕ} (k : ℕ) (hf : T.modulus b ≤ a) (hg : U.modulus k ≤ b) :
    (g.comp f).truncatedMap k (by
      simpa only [PositiveDegreeMap.comp_modulus] using
        (T.monotone_modulus hg).trans hf) =
      (g.truncatedMap k hg).comp (f.truncatedMap b hf) := by
  apply (d.degreeIdeal ℒ a).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- Induced maps commute with the transitions obtained by truncating identity maps. -/
theorem truncatedMap_naturality (f : GradedLieHom T ℒ ℳ) {a b k l : ℕ}
    (hab : a ≤ b) (hkl : k ≤ l) (ha : T.modulus k ≤ a) (hb : T.modulus l ≤ b) :
    ((id (d := e) ℳ).truncatedMap k (by simpa using hkl)).comp (f.truncatedMap l hb) =
      (f.truncatedMap k ha).comp ((id (d := d) ℒ).truncatedMap a (by simpa using hab)) := by
  apply (d.degreeIdeal ℒ b).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

end GradedLieHom
end Mei
