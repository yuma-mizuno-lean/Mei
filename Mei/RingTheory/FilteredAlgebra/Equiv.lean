/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.AlgHom

/-!
# Completion of filtered algebra equivalences

An algebra equivalence identifying each filtration ideal induces an algebra
equivalence of completions, with the corresponding quotient maps as its finite
projections. This allows a coefficient algebra to be completed using a different
presentation, without changing its filtration or requiring separatedness.

The construction follows `ModuleFiltration.completionEquiv`, using
`AlgFiltration.mapCompletionₐ` in both directions and its composition law.
-/

public section

namespace Mei.AlgFiltration

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B] (F : AlgFiltration A) (G : AlgFiltration B)
  (e : A ≃ₐ[R] B) (he : ∀ k, (G.ideal k).comap e.toAlgHom = F.ideal k)

include he

/-- Exact identification of filtration ideals also holds for the inverse map. -/
theorem comap_ideal_equiv_symm (k : ℕ) :
    (F.ideal k).comap e.symm.toAlgHom = G.ideal k := by
  ext y
  rw [Ideal.mem_comap, ← he k]
  simp

/-- A filtration-preserving algebra equivalence extends to completed algebras. -/
def completionEquiv : F.completion ≃ₐ[R] G.completion where
  __ := F.mapCompletionₐ G e.toAlgHom id monotone_id (fun k => (he (k + 1)).ge)
  invFun := G.mapCompletionₐ F e.symm.toAlgHom id monotone_id
    (fun k => (F.comap_ideal_equiv_symm G e he (k + 1)).ge)
  left_inv x := by
    have h := F.mapCompletionₐ_comp G e.toAlgHom id monotone_id (fun k => (he (k + 1)).ge)
      F e.symm.toAlgHom id monotone_id
      (fun k => (F.comap_ideal_equiv_symm G e he (k + 1)).ge)
    simp only [AlgEquiv.symm_comp, Function.id_comp, mapCompletionₐ_id] at h
    exact (AlgHom.congr_fun h x).symm
  right_inv x := by
    have h := G.mapCompletionₐ_comp F e.symm.toAlgHom id monotone_id
      (fun k => (F.comap_ideal_equiv_symm G e he (k + 1)).ge)
      G e.toAlgHom id monotone_id (fun k => (he (k + 1)).ge)
    simp only [AlgEquiv.comp_symm, Function.id_comp, mapCompletionₐ_id] at h
    exact (AlgHom.congr_fun h x).symm

/-- Finite projections of the completed equivalence are induced quotient maps. -/
@[simp]
theorem projection_completionEquiv (k : ℕ) (x : F.completion) :
    G.projection k (F.completionEquiv G e he x) =
      Ideal.quotientMapₐ (G.ideal (k + 1)) e.toAlgHom (by simp only [he, le_refl])
        (F.projection k x) :=
  F.projection_mapCompletionₐ G e.toAlgHom id monotone_id (fun k => (he (k + 1)).ge) k x

/-- The extension agrees with the original equivalence on canonical elements. -/
@[simp]
theorem completionEquiv_toCompletion (a : A) :
    F.completionEquiv G e he (F.toCompletion a) = G.toCompletion (e a) :=
  F.mapCompletionₐ_toCompletion G e.toAlgHom id monotone_id (fun k => (he (k + 1)).ge) a

/-- Inverting the completed equivalence completes the inverse equivalence. -/
theorem completionEquiv_symm :
    (F.completionEquiv G e he).symm =
      G.completionEquiv F e.symm (F.comap_ideal_equiv_symm G e he) := by
  ext x
  rfl

/-- Finite projections of the inverse use the inverse quotient map. -/
@[simp]
theorem projection_completionEquiv_symm (k : ℕ) (y : G.completion) :
    F.projection k ((F.completionEquiv G e he).symm y) =
      Ideal.quotientMapₐ (F.ideal (k + 1)) e.symm.toAlgHom
        (by simp only [F.comap_ideal_equiv_symm G e he, le_refl]) (G.projection k y) := by
  rw [completionEquiv_symm, projection_completionEquiv]

/-- The inverse extension agrees with the inverse on canonical elements. -/
@[simp]
theorem completionEquiv_symm_toCompletion (b : B) :
    (F.completionEquiv G e he).symm (G.toCompletion b) = F.toCompletion (e.symm b) := by
  rw [completionEquiv_symm, completionEquiv_toCompletion]

end Mei.AlgFiltration
