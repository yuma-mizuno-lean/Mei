/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.Algebra
public import Mei.RingTheory.FilteredAlgebra.Map

/-!
# Algebra maps between filtered completions

An algebra homomorphism that sends sufficiently deep source ideals into each
prescribed target ideal extends to an algebra homomorphism on completions. A
monotone cutoff modulus specifies the source order used for each target order.
The extension is independent of that choice, respects identities and composition,
and commutes with restriction of scalars.

The construction refines `Mei.AlgFiltration.mapCompletion` on the existing
compatible-family carrier. Its finite-order formula uses Mathlib's
`Ideal.quotientMapₐ`. The algebras may be noncommutative; no separatedness,
adic presentation, freeness or flatness is required.
-/

public section

namespace Mei.AlgFiltration

variable {R A B C : Type*} [CommRing R]
  [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (F : Mei.AlgFiltration A) (G : Mei.AlgFiltration B)
  (f : A →ₐ[R] B) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap (f : A →+* B))

/-- Extend a filtered algebra homomorphism along a monotone cutoff modulus. -/
def mapCompletionₐ : F.completion →ₐ[R] G.completion where
  __ := F.mapCompletion G (f : A →+* B) l hl hf
  commutes' r := by
    apply G.completion_ext
    intro k
    calc
      _ = Ideal.quotientMap (G.ideal (k + 1)) (f : A →+* B) (hf k)
          (F.projection (l k) (algebraMap R F.completion r)) :=
        F.projection_mapCompletion G (f : A →+* B) l hl hf k _
      _ = algebraMap R (B ⧸ G.ideal (k + 1)) r := by
        simp [projection_algebraMap, Ideal.quotientMap_algebraMap]
      _ = _ := (G.projection_algebraMap k r).symm

/-- Forgetting scalars recovers the existing map of ring completions. -/
@[simp]
theorem coe_mapCompletionₐ :
    (F.mapCompletionₐ G f l hl hf : F.completion →+* G.completion) =
      F.mapCompletion G (f : A →+* B) l hl hf := (rfl)

/-- The algebra extension evaluates by its underlying ring extension. -/
@[simp]
theorem mapCompletionₐ_apply (x : F.completion) :
    F.mapCompletionₐ G f l hl hf x = F.mapCompletion G (f : A →+* B) l hl hf x := (rfl)

/-- Each target component is induced by the algebra map on the appropriate source quotient. -/
@[simp]
theorem projectionₐ_comp_mapCompletionₐ (k : ℕ) :
    (G.projectionₐ (R := R) k).comp (F.mapCompletionₐ G f l hl hf) =
      (Ideal.quotientMapₐ (G.ideal (k + 1)) f (hf k)).comp (F.projectionₐ (R := R) (l k)) := by
  apply AlgHom.ext
  intro x
  simp only [AlgHom.comp_apply, projectionₐ_apply, mapCompletionₐ_apply,
    projection_mapCompletion]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection (l k) x)
  rw [← ha, Ideal.quotientMap_mk]
  exact (Ideal.quotient_map_mkₐ (G.ideal (k + 1)) f (hf k) (x := a)).symm

/-- The extension commutes with the canonical algebra maps into the completions. -/
@[simp]
theorem mapCompletionₐ_comp_toCompletionₐ :
    (F.mapCompletionₐ G f l hl hf).comp (F.toCompletionₐ (R := R)) =
      (G.toCompletionₐ (R := R)).comp f := by
  ext a
  simp only [AlgHom.comp_apply, mapCompletionₐ_apply, toCompletionₐ_apply,
    mapCompletion_toCompletion, AlgHom.coe_toRingHom]

/-- All valid cutoff moduli for an algebra map give the same extension. -/
theorem mapCompletionₐ_eq (m : ℕ → ℕ) (hm : Monotone m)
    (hfm : ∀ k, F.ideal (m k + 1) ≤ (G.ideal (k + 1)).comap (f : A →+* B)) :
    F.mapCompletionₐ G f l hl hf = F.mapCompletionₐ G f m hm hfm := by
  apply AlgHom.toRingHom_injective
  exact F.mapCompletion_eq G (f : A →+* B) hl hf m hm hfm

/-- Extending the identity algebra map with the identity modulus gives the identity. -/
@[simp]
theorem mapCompletionₐ_id :
    F.mapCompletionₐ F (AlgHom.id R A) id monotone_id (fun _ => by simp) =
      AlgHom.id R F.completion := by
  apply AlgHom.toRingHom_injective
  exact F.mapCompletion_id

variable (H : Mei.AlgFiltration C) (g : B →ₐ[R] C) (m : ℕ → ℕ) (hm : Monotone m)
  (hg : ∀ k, G.ideal (m k + 1) ≤ (H.ideal (k + 1)).comap (g : B →+* C))

/-- Successive algebra extensions compose with modulus `l ∘ m`. -/
theorem mapCompletionₐ_comp :
    F.mapCompletionₐ H (g.comp f) (l ∘ m) (hl.comp hm)
      (fun k => (hf (m k)).trans (Ideal.comap_mono (hg k))) =
      (G.mapCompletionₐ H g m hm hg).comp (F.mapCompletionₐ G f l hl hf) := by
  apply AlgHom.toRingHom_injective
  simpa only [coe_mapCompletionₐ, AlgHom.comp_toRingHom] using
    F.mapCompletion_comp G (f : A →+* B) hl hf H (g : B →+* C) m hm hg

section RestrictScalars

variable {S : Type*} [CommRing S] [Algebra S R]
  [Algebra S A] [Algebra S B] [IsScalarTower S R A] [IsScalarTower S R B]

/-- Extending an algebra map commutes with restriction to smaller scalars. -/
@[simp]
theorem mapCompletionₐ_restrictScalars :
    (F.mapCompletionₐ G f l hl hf).restrictScalars S =
      F.mapCompletionₐ G (f.restrictScalars S) l hl hf := by
  apply AlgHom.toRingHom_injective
  rfl

end RestrictScalars

end Mei.AlgFiltration
