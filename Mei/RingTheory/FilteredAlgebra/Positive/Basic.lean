/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.RingTheory.FilteredAlgebra.Map

/-!
# Positive elements of filtered completions and positive specializations

Fix a subsemiring `P` of a ring `B` with an ideal filtration. An element of the
completion is *positive* for `P` when each of its finite-order projections is the
class of an element of `P`. For a monoid algebra over a polynomial ring with
natural-number coefficients inside one with rational coefficients, this says that
every finite truncation has a representative with coefficients in the natural
subsemiring, as in positivity statements for wall functions of scattering diagrams
(Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, and
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*).
Positive elements form a subsemiring of the completion, hence are closed under
sums, products and natural powers, and contain the image of `P`.

A positive specialization from `(B, F, P)` to `(C, G, Q)` is a ring homomorphism
that is filtered along some monotone cutoff modulus and maps `P` into `Q`. The
modulus is not part of the data: by `Mei.AlgFiltration.mapCompletion_eq` the induced
completion map does not depend on it. Positive specializations compose, restrict to
semiring maps `P →+* Q`, and their completion maps commute with the canonical maps
from the rings and preserve positivity.

No commutativity, separatedness or adicness is assumed.
-/

public section

namespace Mei

namespace AlgFiltration

variable {B : Type*} [Ring B] (F : Mei.AlgFiltration B) (P : Subsemiring B)

/-- An element of the completion is positive for `P` when, at every finite order, its
projection is the class of an element of `P`. -/
def IsPositive (x : F.completion) : Prop :=
  ∀ k, ∃ a ∈ P, Ideal.Quotient.mk (F.ideal (k + 1)) a = F.projection k x

/-- Unfolding positivity: every finite-order projection is the class of an element of `P`. -/
theorem isPositive_iff (x : F.completion) :
    F.IsPositive P x ↔ ∀ k, ∃ a ∈ P, Ideal.Quotient.mk (F.ideal (k + 1)) a = F.projection k x :=
  Iff.rfl

/-- The subsemiring of the completion consisting of the elements positive for `P`: the
elements whose order-`k` projection lies in the image of `P`, for every `k`. -/
def positiveCompletion : Subsemiring F.completion :=
  ⨅ k, (P.map (Ideal.Quotient.mk (F.ideal (k + 1)))).comap (F.projection k)

/-- The positive subsemiring is the intersection of the preimages, under the finite-order
projections, of the images of `P` in the quotients. -/
theorem positiveCompletion_eq_iInf :
    F.positiveCompletion P =
      ⨅ k, (P.map (Ideal.Quotient.mk (F.ideal (k + 1)))).comap (F.projection k) :=
  (rfl)

/-- Membership in the positive subsemiring is positivity. -/
@[simp]
theorem mem_positiveCompletion {x : F.completion} :
    x ∈ F.positiveCompletion P ↔ F.IsPositive P x := by
  simp [positiveCompletion, Subsemiring.mem_iInf, isPositive_iff]

variable {F P}

/-- Zero is positive. -/
@[simp]
theorem isPositive_zero : F.IsPositive P 0 :=
  (F.mem_positiveCompletion P).mp (zero_mem _)

/-- One is positive. -/
@[simp]
theorem isPositive_one : F.IsPositive P 1 :=
  (F.mem_positiveCompletion P).mp (one_mem _)

/-- Positive elements are closed under addition. -/
theorem IsPositive.add {x y : F.completion} (hx : F.IsPositive P x) (hy : F.IsPositive P y) :
    F.IsPositive P (x + y) :=
  (F.mem_positiveCompletion P).mp
    (add_mem ((F.mem_positiveCompletion P).mpr hx) ((F.mem_positiveCompletion P).mpr hy))

/-- Positive elements are closed under multiplication. -/
theorem IsPositive.mul {x y : F.completion} (hx : F.IsPositive P x) (hy : F.IsPositive P y) :
    F.IsPositive P (x * y) :=
  (F.mem_positiveCompletion P).mp
    (MulMemClass.mul_mem ((F.mem_positiveCompletion P).mpr hx)
      ((F.mem_positiveCompletion P).mpr hy))

/-- Positive elements are closed under natural powers. -/
theorem IsPositive.pow {x : F.completion} (hx : F.IsPositive P x) (n : ℕ) :
    F.IsPositive P (x ^ n) :=
  (F.mem_positiveCompletion P).mp (_root_.pow_mem ((F.mem_positiveCompletion P).mpr hx) n)

/-- The canonical image of an element of `P` is positive. -/
theorem isPositive_toCompletion {a : B} (ha : a ∈ P) : F.IsPositive P (F.toCompletion a) :=
  fun k => ⟨a, ha, (F.projection_toCompletion k a).symm⟩

variable (F P)

/-- The canonical map sends `P` into the positive subsemiring. -/
theorem map_toCompletion_le_positiveCompletion :
    P.map F.toCompletion ≤ F.positiveCompletion P := by
  rintro _ ⟨a, ha, rfl⟩
  exact (F.mem_positiveCompletion P).mpr (isPositive_toCompletion ha)

/-- Enlarging the chosen subsemiring enlarges the positive subsemiring. -/
theorem positiveCompletion_mono : Monotone F.positiveCompletion := by
  intro P P' h x hx
  rw [mem_positiveCompletion] at hx ⊢
  intro k
  obtain ⟨a, ha, hax⟩ := hx k
  exact ⟨a, h ha, hax⟩

/-- Every element is positive for the whole ring. -/
@[simp]
theorem positiveCompletion_top : F.positiveCompletion ⊤ = ⊤ := by
  refine eq_top_iff.mpr fun x _ => (F.mem_positiveCompletion ⊤).mpr fun k => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  exact ⟨a, Subsemiring.mem_top a, ha⟩

end AlgFiltration

variable {B C D : Type*} [Ring B] [Ring C] [Ring D]

/-- A positive specialization from a filtered ring `B` with chosen subsemiring `P` to a
filtered ring `C` with chosen subsemiring `Q`: a ring homomorphism that maps `P` into `Q`
and is filtered along some monotone cutoff modulus `l`, sending the ideal at `l k + 1`
into the ideal at `k + 1`. Only the existence of a modulus is recorded, since the induced
completion map does not depend on the choice. -/
@[ext]
structure PositiveSpecialization (F : AlgFiltration B) (G : AlgFiltration C)
    (P : Subsemiring B) (Q : Subsemiring C) where
  /-- The underlying ring homomorphism. -/
  toRingHom : B →+* C
  /-- Some monotone cutoff modulus makes the homomorphism filtered. -/
  exists_modulus : ∃ l : ℕ → ℕ, Monotone l ∧
    ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap toRingHom
  /-- The chosen subsemiring of the source is mapped into that of the target. -/
  map_mem : ∀ a ∈ P, toRingHom a ∈ Q

namespace PositiveSpecialization

variable {F : AlgFiltration B} {G : AlgFiltration C} {H : AlgFiltration D}
  {P : Subsemiring B} {Q : Subsemiring C} {R : Subsemiring D}

/-- The identity map, with the identity cutoff modulus. -/
protected def id (F : AlgFiltration B) (P : Subsemiring B) : PositiveSpecialization F F P P where
  toRingHom := RingHom.id B
  exists_modulus := ⟨id, monotone_id, fun _ => le_rfl⟩
  map_mem _ ha := ha

/-- The identity specialization has the identity ring homomorphism. -/
@[simp]
theorem id_toRingHom (F : AlgFiltration B) (P : Subsemiring B) :
    (PositiveSpecialization.id F P).toRingHom = RingHom.id B :=
  (rfl)

/-- Composition of positive specializations; successive moduli `l` and `m` compose to
`l ∘ m`. -/
def comp (ψ : PositiveSpecialization G H Q R) (φ : PositiveSpecialization F G P Q) :
    PositiveSpecialization F H P R where
  toRingHom := ψ.toRingHom.comp φ.toRingHom
  exists_modulus := by
    obtain ⟨l, hl, hf⟩ := φ.exists_modulus
    obtain ⟨m, hm, hg⟩ := ψ.exists_modulus
    refine ⟨l ∘ m, hl.comp hm, fun k => ?_⟩
    rw [← Ideal.comap_comap]
    exact (hf (m k)).trans (Ideal.comap_mono (hg k))
  map_mem a ha := ψ.map_mem _ (φ.map_mem a ha)

/-- The composite specialization has the composite ring homomorphism. -/
@[simp]
theorem comp_toRingHom (ψ : PositiveSpecialization G H Q R) (φ : PositiveSpecialization F G P Q) :
    (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom :=
  (rfl)

/-- The identity is a left unit for composition. -/
@[simp]
theorem id_comp (φ : PositiveSpecialization F G P Q) :
    (PositiveSpecialization.id G Q).comp φ = φ := by
  ext
  simp

/-- The identity is a right unit for composition. -/
@[simp]
theorem comp_id (φ : PositiveSpecialization F G P Q) :
    φ.comp (PositiveSpecialization.id F P) = φ := by
  ext
  simp

/-- Composition of positive specializations is associative. -/
theorem comp_assoc {E : Type*} [Ring E] {K : AlgFiltration E} {S : Subsemiring E}
    (χ : PositiveSpecialization H K R S) (ψ : PositiveSpecialization G H Q R)
    (φ : PositiveSpecialization F G P Q) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  (rfl)

/-- The restriction to a semiring homomorphism between the chosen subsemirings. -/
def restrict (φ : PositiveSpecialization F G P Q) : P →+* Q :=
  φ.toRingHom.restrict P Q φ.map_mem

/-- The restriction computes by the underlying ring homomorphism. -/
@[simp]
theorem coe_restrict_apply (φ : PositiveSpecialization F G P Q) (a : P) :
    (φ.restrict a : C) = φ.toRingHom a :=
  (rfl)

/-- The induced map of completions, computed with any cutoff modulus of the
specialization. -/
noncomputable def completionMap (φ : PositiveSpecialization F G P Q) :
    F.completion →+* G.completion :=
  F.mapCompletion G φ.toRingHom φ.exists_modulus.choose φ.exists_modulus.choose_spec.1
    φ.exists_modulus.choose_spec.2

/-- The completion map is the completion map of the underlying homomorphism along any
cutoff modulus. -/
theorem completionMap_eq_mapCompletion (φ : PositiveSpecialization F G P Q) (l : ℕ → ℕ)
    (hl : Monotone l) (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap φ.toRingHom) :
    φ.completionMap = F.mapCompletion G φ.toRingHom l hl hf :=
  F.mapCompletion_eq G φ.toRingHom _ _ l hl hf

/-- The completion map commutes with the canonical maps from the rings. -/
@[simp]
theorem completionMap_toCompletion (φ : PositiveSpecialization F G P Q) (a : B) :
    φ.completionMap (F.toCompletion a) = G.toCompletion (φ.toRingHom a) :=
  F.mapCompletion_toCompletion G _ _ _ _ a

/-- The identity specialization induces the identity completion map. -/
@[simp]
theorem completionMap_id (F : AlgFiltration B) (P : Subsemiring B) :
    (PositiveSpecialization.id F P).completionMap = RingHom.id F.completion := by
  rw [completionMap_eq_mapCompletion _ id monotone_id fun _ => le_rfl]
  exact F.mapCompletion_id

/-- Completion maps of positive specializations compose. -/
theorem completionMap_comp (ψ : PositiveSpecialization G H Q R)
    (φ : PositiveSpecialization F G P Q) :
    (ψ.comp φ).completionMap = ψ.completionMap.comp φ.completionMap := by
  obtain ⟨l, hl, hf⟩ := φ.exists_modulus
  obtain ⟨m, hm, hg⟩ := ψ.exists_modulus
  rw [φ.completionMap_eq_mapCompletion l hl hf, ψ.completionMap_eq_mapCompletion m hm hg,
    ← F.mapCompletion_comp G φ.toRingHom hl hf H ψ.toRingHom m hm hg]
  exact (ψ.comp φ).completionMap_eq_mapCompletion _ _ _

/-- Positive specializations preserve positivity. -/
theorem map_isPositive (φ : PositiveSpecialization F G P Q) {x : F.completion}
    (hx : F.IsPositive P x) : G.IsPositive Q (φ.completionMap x) := by
  obtain ⟨l, hl, hf⟩ := φ.exists_modulus
  rw [φ.completionMap_eq_mapCompletion l hl hf, AlgFiltration.isPositive_iff]
  intro k
  obtain ⟨a, ha, hax⟩ := hx (l k)
  refine ⟨φ.toRingHom a, φ.map_mem a ha, ?_⟩
  rw [AlgFiltration.projection_mapCompletion, ← hax, Ideal.quotientMap_mk]

/-- The completion map sends the positive subsemiring into the positive subsemiring. -/
theorem map_positiveCompletion_le (φ : PositiveSpecialization F G P Q) :
    (F.positiveCompletion P).map φ.completionMap ≤ G.positiveCompletion Q := by
  rintro _ ⟨x, hx, rfl⟩
  exact (G.mem_positiveCompletion Q).mpr
    (φ.map_isPositive ((F.mem_positiveCompletion P).mp hx))

end PositiveSpecialization

end Mei
