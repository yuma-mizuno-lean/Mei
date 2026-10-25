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

An algebra homomorphism with a monotone cutoff modulus induces an algebra
homomorphism on compatible-family completions. The underlying ring map is
`Mei.AlgFiltration.mapCompletion`; its scalar compatibility follows from the
canonical algebra maps `Mei.AlgFiltration.toCompletionₐ`. Finite-order components
use Mathlib's `Ideal.quotientMapₐ`.

The induced map is independent of the chosen modulus, respects identity and
composition, and commutes with restriction of scalars. Its projection formula
and filtration bound allow maps of complete coefficient algebras to be used at
any finite order. The algebras may be noncommutative, and no separatedness
or adic-presentation hypothesis is required.
-/

public section

namespace Mei.AlgFiltration

variable {R A B C : Type*} [CommRing R]
  [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
  (F : Mei.AlgFiltration A) (G : Mei.AlgFiltration B)
  (f : A →ₐ[R] B) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap f)

/-- Extend an algebra homomorphism to completions along a monotone cutoff modulus. -/
def mapCompletionₐ : F.completion →ₐ[R] G.completion where
  __ := F.mapCompletion G (f : A →+* B) l hl hf
  commutes' r := by
    have hF := (F.toCompletionₐ (R := R)).commutes r
    have hG := (G.toCompletionₐ (R := R)).commutes r
    simp only [toCompletionₐ_apply] at hF hG
    simpa only [RingHom.toFun_eq_coe, AlgHom.coe_toRingHom, hF, f.commutes, hG] using
      F.mapCompletion_toCompletion G (f : A →+* B) l hl hf (algebraMap R A r)

/-- Forgetting scalars gives the existing filtered ring completion map. -/
@[simp]
theorem coe_mapCompletionₐ :
    (F.mapCompletionₐ G f l hl hf : F.completion →+* G.completion) =
      F.mapCompletion G (f : A →+* B) l hl hf := (rfl)

/-- The order-`k` projection is the induced quotient algebra map at source order `l k`. -/
@[simp]
theorem projection_mapCompletionₐ (k : ℕ) (x : F.completion) :
    G.projection k (F.mapCompletionₐ G f l hl hf x) =
      Ideal.quotientMapₐ (G.ideal (k + 1)) f (hf k) (F.projection (l k) x) :=
  F.projection_mapCompletion G (f : A →+* B) l hl hf k x

/-- Any larger source cutoff computes the same quotient algebra component. -/
theorem projection_mapCompletionₐ_of_le (k a : ℕ) (ha : l k ≤ a) (x : F.completion) :
    G.projection k (F.mapCompletionₐ G f l hl hf x) =
      Ideal.quotientMapₐ (G.ideal (k + 1)) f
        ((F.antitone (Nat.add_le_add_right ha 1)).trans (hf k)) (F.projection a x) :=
  F.projection_mapCompletion_of_le G (f : A →+* B) l hl hf k a ha x

/-- The induced algebra map extends the original map on canonical elements. -/
@[simp]
theorem mapCompletionₐ_toCompletion (a : A) :
    F.mapCompletionₐ G f l hl hf (F.toCompletion a) = G.toCompletion (f a) :=
  F.mapCompletion_toCompletion G (f : A →+* B) l hl hf a

/-- The completion map preserves the original cutoff bound on the induced filtrations. -/
theorem mapCompletionₐ_mem_completionIdeal (k : ℕ) {x : F.completion}
    (hx : x ∈ F.completionIdeal (l k + 1)) :
    F.mapCompletionₐ G f l hl hf x ∈ G.completionIdeal (k + 1) :=
  F.mapCompletion_mem_completionIdeal G (f : A →+* B) l hl hf k hx

/-- Any two valid cutoff moduli induce the same algebra homomorphism on completions. -/
theorem mapCompletionₐ_eq (m : ℕ → ℕ) (hm : Monotone m)
    (hfm : ∀ k, F.ideal (m k + 1) ≤ (G.ideal (k + 1)).comap f) :
    F.mapCompletionₐ G f l hl hf = F.mapCompletionₐ G f m hm hfm := by
  apply AlgHom.toRingHom_injective
  exact F.mapCompletion_eq G (f : A →+* B) hl hf m hm hfm

/-- Completing the identity algebra map gives the identity algebra map. -/
@[simp]
theorem mapCompletionₐ_id :
    F.mapCompletionₐ F (AlgHom.id R A) id monotone_id (fun _ => by simp) =
      AlgHom.id R F.completion := by
  apply AlgHom.toRingHom_injective
  exact F.mapCompletion_id

variable (H : Mei.AlgFiltration C) (g : B →ₐ[R] C) (m : ℕ → ℕ) (hm : Monotone m)
  (hg : ∀ k, G.ideal (m k + 1) ≤ (H.ideal (k + 1)).comap g)

/-- Successive algebra completion maps compose with cutoff modulus `l ∘ m`. -/
theorem mapCompletionₐ_comp :
    F.mapCompletionₐ H (g.comp f) (l ∘ m) (hl.comp hm)
      (fun k => by
        rw [← Ideal.comap_comapₐ]
        exact (hf (m k)).trans (Ideal.comap_mono (hg k))) =
      (G.mapCompletionₐ H g m hm hg).comp (F.mapCompletionₐ G f l hl hf) := by
  apply AlgHom.toRingHom_injective
  simpa only [AlgHom.comp_toRingHom, coe_mapCompletionₐ] using
    F.mapCompletion_comp G (f : A →+* B) hl hf H (g : B →+* C) m hm hg

section RestrictScalars

variable {S : Type*} [CommRing S] [Algebra S R]
  [Algebra S A] [IsScalarTower S R A] [Algebra S B] [IsScalarTower S R B]

/-- Restriction of scalars commutes with the induced algebra map on completions. -/
@[simp]
theorem mapCompletionₐ_restrictScalars :
    (F.mapCompletionₐ G f l hl hf).restrictScalars S =
      F.mapCompletionₐ G (f.restrictScalars S) l hl hf := by
  apply AlgHom.toRingHom_injective
  rfl

end RestrictScalars

end Mei.AlgFiltration
