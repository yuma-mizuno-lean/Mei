/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.PositiveDegreeHom
public import Mei.Algebra.Lie.Graded.Truncation.Basic

/-!
# Graded Lie homomorphisms and their truncations

A `TauCeti.GradedLieHom` carries homogeneous pieces along a specified positive degree
map. Its cutoff modulus controls the degree ideals, so the homomorphism descends
from the source truncation at the prescribed order to each target truncation.
These induced maps respect homogeneous pieces, identities, and composition.
They commute with the surjective truncation transitions and remain compatible
when the source cutoff is increased, providing finite-order maps for
inverse-limit constructions.

The cutoff estimate needs only positivity of the source pieces; it does not need
an internal decomposition or injectivity of the degree map. In particular,
distinct source degrees may merge in the target.

The induced maps specialize `LieIdeal.mapQ`, which uses `LieIdeal.liftQ` from
Tau Ceti, the universal property of the Lie quotient. The tower compatibility
laws use `LieIdeal.factor` and its quotient laws.
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

/-- A graded homomorphism preserves degree ideals at the orders prescribed by its modulus. -/
theorem map_mem_truncationIdeal (f : GradedLieHom T ℒ ℳ) (k : ℕ) {x : L}
    (hx : x ∈ d.truncationIdeal ℒ (T.modulus k)) : f x ∈ e.truncationIdeal ℳ k := by
  apply (LieSubmodule.mem_toSubmodule _).mp
  rw [e.truncationIdeal_toSubmodule]
  have hx' := (LieSubmodule.mem_toSubmodule _).mpr hx
  rw [d.truncationIdeal_toSubmodule] at hx'
  exact f.map_degreeSubmodule_le k (Submodule.mem_map.mpr ⟨x, hx', rfl⟩)

/-- The finite-order Lie homomorphism induced by a graded Lie homomorphism.
The source order may be any `a ≥ T.modulus k`, allowing comparison of cutoffs
without transporting maps between propositionally equal quotient types. -/
def lieTruncatedMap (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ) (h : T.modulus k ≤ a) :
    d.lieTruncation ℒ a →ₗ⁅R⁆ e.lieTruncation ℳ k :=
  (d.truncationIdeal ℒ a).mapQ (e.truncationIdeal ℳ k) f.toLieHom
    (fun _ hx => f.map_mem_truncationIdeal k (d.truncationIdeal_antitone ℒ h hx))

/-- The induced truncation map is the quotient map of the underlying Lie homomorphism. -/
theorem lieTruncatedMap_def (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) :
    f.lieTruncatedMap k h =
      (d.truncationIdeal ℒ a).mapQ (e.truncationIdeal ℳ k) f.toLieHom
        (fun _ hx => f.map_mem_truncationIdeal k (d.truncationIdeal_antitone ℒ h hx)) := (rfl)

/-- The induced map sends the class of an element to the class of its image. -/
@[simp]
theorem lieTruncatedMap_mk (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) (x : L) :
    f.lieTruncatedMap k h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := by
  exact (d.truncationIdeal ℒ a).mapQ_apply (e.truncationIdeal ℳ k) f.toLieHom _ x

/-- The induced map preserves homogeneous pieces along the original degree map. -/
theorem lieTruncatedMap_mem (f : GradedLieHom T ℒ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) {n : N} {x : d.lieTruncation ℒ a}
    (hx : x ∈ d.lieTruncationGrading ℒ a n) :
    f.lieTruncatedMap k h x ∈ e.lieTruncationGrading ℳ k (T n) := by
  obtain ⟨y, hy, rfl⟩ := (d.mem_lieTruncationGrading_iff ℒ).mp hx
  refine (e.mem_lieTruncationGrading_iff ℳ).mpr ⟨f y, f.map_mem hy, ?_⟩
  simpa only [LieIdeal.mkQ_apply] using (f.lieTruncatedMap_mk k h y).symm

/-- The truncation of a fixed-degree homomorphism commutes with homogeneous components. -/
theorem decompose_lieTruncatedMap {ℳ' : N → Submodule R L'} [GradedLieAlgebra ℳ']
    [IsPositiveGrading d ℳ'] (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ') (k : ℕ)
    (x : d.lieTruncation ℒ k) (n : N) :
    (DirectSum.decompose (d.lieTruncationGrading ℳ' k) (f.lieTruncatedMap k (by simp) x) n :
      d.lieTruncation ℳ' k) =
      f.lieTruncatedMap k (by simp)
        (DirectSum.decompose (d.lieTruncationGrading ℒ k) x n : d.lieTruncation ℒ k) :=
  (DirectSum.map_decompose_shift (d.lieTruncationGrading ℒ k) (d.lieTruncationGrading ℳ' k)
    (f.lieTruncatedMap k (by simp)).toLinearMap.toAddMonoidHom _root_.id Function.injective_id
    (fun _ _ hx => by simpa using f.lieTruncatedMap_mem k (by simp) hx) n x).symm

/-- Truncation sends the identity graded homomorphism to the identity. -/
@[simp]
theorem lieTruncatedMap_id (k : ℕ) :
    (id (d := d) ℒ).lieTruncatedMap k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k) =
      LieHom.id := by
  apply (d.truncationIdeal ℒ k).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply, LieHom.id_apply]

/-- Truncation respects composition, with source orders controlled by successive moduli. -/
theorem lieTruncatedMap_comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ)
    {a b : ℕ} (k : ℕ) (hf : T.modulus b ≤ a) (hg : U.modulus k ≤ b) :
    (g.comp f).lieTruncatedMap k (by
      simpa only [PositiveDegreeMap.comp_modulus] using
        (T.monotone_modulus hg).trans hf) =
      (g.lieTruncatedMap k hg).comp (f.lieTruncatedMap b hf) := by
  apply (d.truncationIdeal ℒ a).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- Increasing the source cutoff changes the induced map only by precomposition
with the source truncation transition. -/
@[simp]
theorem lieTruncatedMap_comp_lieTruncationMap (f : GradedLieHom T ℒ ℳ)
    {k l m : ℕ} (hl : T.modulus k ≤ l) (h : l ≤ m) :
    (f.lieTruncatedMap k hl).comp (d.lieTruncationMap ℒ h) =
      f.lieTruncatedMap k (hl.trans h) := by
  simp only [lieTruncatedMap_def, PositiveDegrees.lieTruncationMap_def]
  simpa only [LieIdeal.factor_refl, LieHom.id_comp] using
    (LieIdeal.factor_comp_mapQ (d.truncationIdeal ℒ m) (e.truncationIdeal ℳ k)
      (d.truncationIdeal ℒ l) (e.truncationIdeal ℳ k)
      (d.truncationIdeal_antitone ℒ h) le_rfl f.toLieHom
      (fun _ hx => f.map_mem_truncationIdeal k (d.truncationIdeal_antitone ℒ (hl.trans h) hx))
      (fun _ hx => f.map_mem_truncationIdeal k (d.truncationIdeal_antitone ℒ hl hx))).symm

/-- Finite graded maps at arbitrary sufficiently large source cutoffs commute
with the quotient transitions. -/
theorem lieTruncationMap_comp_lieTruncatedMap_of_le (f : GradedLieHom T ℒ ℳ)
    {a b k l : ℕ} (hab : a ≤ b) (hkl : k ≤ l)
    (ha : T.modulus k ≤ a) (hb : T.modulus l ≤ b) :
    (e.lieTruncationMap ℳ hkl).comp (f.lieTruncatedMap l hb) =
      (f.lieTruncatedMap k ha).comp (d.lieTruncationMap ℒ hab) := by
  apply (d.truncationIdeal ℒ b).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- The maps of degree truncations commute with the transitions in both towers. -/
theorem lieTruncationMap_comp_lieTruncatedMap (f : GradedLieHom T ℒ ℳ)
    {k l : ℕ} (h : k ≤ l) :
    (e.lieTruncationMap ℳ h).comp (f.lieTruncatedMap l le_rfl) =
      (f.lieTruncatedMap k le_rfl).comp (d.lieTruncationMap ℒ (T.monotone_modulus h)) := by
  exact f.lieTruncationMap_comp_lieTruncatedMap_of_le (T.monotone_modulus h) h le_rfl le_rfl

variable (d ℒ) in
/-- The quotient map onto the order-`k` truncation `L / F^{k+1}L`, as a graded Lie
homomorphism over the identity degree map. -/
def lieTruncationHom (k : ℕ) :
    GradedLieHom (PositiveDegreeMap.id d) ℒ (d.lieTruncationGrading ℒ k) where
  toLieHom := (d.truncationIdeal ℒ k).mkQ
  map_mem hx := by
    simpa only [PositiveDegreeMap.id_apply] using
      (d.mem_lieTruncationGrading_iff ℒ).mpr ⟨_, hx, rfl⟩

@[simp]
theorem toLieHom_lieTruncationHom (k : ℕ) :
    (lieTruncationHom d ℒ k).toLieHom = (d.truncationIdeal ℒ k).mkQ := (rfl)

@[simp]
theorem lieTruncationHom_apply (k : ℕ) (x : L) :
    lieTruncationHom d ℒ k x = (d.truncationIdeal ℒ k).mkQ x := (rfl)

/-- Truncating the quotient homomorphism at its retained order gives the canonical
map from that quotient to its own degree quotient. -/
@[simp]
theorem lieTruncatedMap_lieTruncationHom (k : ℕ) :
    (lieTruncationHom d ℒ k).lieTruncatedMap k (a := k) (by simp) =
      (d.truncationIdeal (d.lieTruncationGrading ℒ k) k).mkQ := by
  apply (d.truncationIdeal ℒ k).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

section SectionComplement

variable {ℳ' : N → Submodule R L'} [GradedLieAlgebra ℳ'] [IsPositiveGrading d ℳ']
  (π : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ')
  (s : GradedLieHom (PositiveDegreeMap.id d) ℳ' ℒ)

/-- The order-`k` endomorphism `id - s ∘ π` of the truncation of `ℒ`. When `s` is a section
of `π`, it is idempotent with image the truncated kernel of `π`
(`isIdempotentElem_idSubSectionComp`, `lieTruncatedMap_idSubSectionComp`). -/
def idSubSectionComp (k : ℕ) : Module.End R (d.lieTruncation ℒ k) :=
  LinearMap.id - (s.lieTruncatedMap k (by simp)).toLinearMap.comp
    (π.lieTruncatedMap k (by simp)).toLinearMap

theorem idSubSectionComp_apply (k : ℕ) (x : d.lieTruncation ℒ k) :
    π.idSubSectionComp s k x =
      x - s.lieTruncatedMap k (by simp) (π.lieTruncatedMap k (by simp) x) := (rfl)

/-- The map fixes every element of the truncated kernel of `π`. -/
@[simp]
theorem idSubSectionComp_of_map_eq_zero (k : ℕ) {x : d.lieTruncation ℒ k}
    (hx : π.lieTruncatedMap k (by simp) x = 0) : π.idSubSectionComp s k x = x := by
  rw [idSubSectionComp_apply, hx, map_zero, sub_zero]

variable {π s} (hsπ : ∀ x, π (s x) = x)
include hsπ

/-- On truncations, `π` is a retraction of its section. -/
@[simp]
theorem lieTruncatedMap_lieTruncatedMap_of_section (k : ℕ) (y : d.lieTruncation ℳ' k) :
    π.lieTruncatedMap k (by simp) (s.lieTruncatedMap k (by simp) y) = y := by
  have hid : (π.lieTruncatedMap k (by simp)).comp (s.lieTruncatedMap k (by simp)) = LieHom.id := by
    apply (d.truncationIdeal ℳ' k).lieHom_qext
    intro x
    simp [LieIdeal.mkQ_apply, hsπ]
  exact DFunLike.congr_fun hid y

/-- For a section, the map kills the truncation of every lifted element. -/
@[simp]
theorem idSubSectionComp_lieTruncatedMap (k : ℕ) (y : d.lieTruncation ℳ' k) :
    π.idSubSectionComp s k (s.lieTruncatedMap k (by simp) y) = 0 := by
  rw [idSubSectionComp_apply, lieTruncatedMap_lieTruncatedMap_of_section hsπ, sub_self]

/-- For a section, the map lands in the truncated kernel of `π`. -/
@[simp]
theorem lieTruncatedMap_idSubSectionComp (k : ℕ) (x : d.lieTruncation ℒ k) :
    π.lieTruncatedMap k (by simp) (π.idSubSectionComp s k x) = 0 := by
  rw [idSubSectionComp_apply, map_sub, lieTruncatedMap_lieTruncatedMap_of_section hsπ, sub_self]

/-- For a section, the map is idempotent: it is the projection onto the truncated kernel
of `π` along the image of `s`. -/
theorem isIdempotentElem_idSubSectionComp (k : ℕ) :
    IsIdempotentElem (π.idSubSectionComp s k) := by
  ext x
  exact idSubSectionComp_of_map_eq_zero π s k (lieTruncatedMap_idSubSectionComp hsπ k x)

/-- For a section, an element fixed by the map lies in the truncated kernel of `π`. -/
theorem lieTruncatedMap_eq_zero_of_idSubSectionComp_eq (k : ℕ) {x : d.lieTruncation ℒ k}
    (hx : π.idSubSectionComp s k x = x) : π.lieTruncatedMap k (by simp) x = 0 := by
  rw [← hx]
  exact lieTruncatedMap_idSubSectionComp hsπ k x

end SectionComplement

end GradedLieHom
end TauCeti
