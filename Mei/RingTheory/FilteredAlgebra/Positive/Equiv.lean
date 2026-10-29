/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.RingTheory.FilteredAlgebra.Positive.Basic
public import Mei.RingTheory.FilteredAlgebra.Equiv

/-!
# Positivity along filtered algebra equivalences

An algebra equivalence identifying every filtration ideal and matching the chosen
positive subsemirings preserves and reflects positivity in completions. This lets a
positivity criterion proved for one presentation of a filtered algebra, such as
power series in free coordinates, be read on another presentation with the same
completion, such as a coefficient monoid algebra with its monomial filtration.

The proof uses `Mei.PositiveSpecialization.map_isPositive` to transport positivity.
-/

public section

namespace Mei.AlgFiltration

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {F : AlgFiltration A} {G : AlgFiltration B} {e : A ≃ₐ[R] B}
  {he : ∀ k, (G.ideal k).comap e.toAlgHom = F.ideal k}
  {P : Subsemiring A} {P' : Subsemiring B}

/-- A filtration-preserving algebra equivalence carrying `P` into `P'` sends elements
positive for `P` to elements positive for `P'`. -/
theorem IsPositive.completionEquiv (hP : ∀ a ∈ P, e a ∈ P') {x : F.completion}
    (hx : F.IsPositive P x) : G.IsPositive P' (F.completionEquiv G e he x) := by
  let φ : PositiveSpecialization F G P P' :=
    { toRingHom := e.toRingHom
      exists_modulus := ⟨id, monotone_id, fun k => (he (k + 1)).ge⟩
      map_mem := hP }
  suffices F.completionEquiv G e he x = φ.completionMap x by
    rw [this]
    exact φ.map_isPositive hx
  rw [φ.completionMap_eq_mapCompletion id monotone_id (fun k => (he (k + 1)).ge)]
  apply G.completion_ext
  intro k
  rw [projection_completionEquiv,
    F.projection_mapCompletion G φ.toRingHom id monotone_id (fun k => (he (k + 1)).ge)]
  rfl

variable (F G e he) in
/-- Positivity is invariant under a filtration-preserving algebra equivalence that
matches the chosen subsemirings. -/
theorem isPositive_completionEquiv_iff (hP : ∀ a, e a ∈ P' ↔ a ∈ P) (x : F.completion) :
    G.IsPositive P' (F.completionEquiv G e he x) ↔ F.IsPositive P x := by
  refine ⟨fun hx => ?_, IsPositive.completionEquiv fun a ha => (hP a).mpr ha⟩
  have h := hx.completionEquiv (he := F.comap_ideal_equiv_symm G e he)
    (fun b hb => (hP _).mp (by simpa only [AlgEquiv.apply_symm_apply] using hb))
  rwa [← completionEquiv_symm, AlgEquiv.symm_apply_apply] at h

end Mei.AlgFiltration
