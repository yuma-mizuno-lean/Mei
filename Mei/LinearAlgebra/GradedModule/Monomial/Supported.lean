/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Monomial.Basic

/-!
# Restricting a monomial presentation to supported degrees

A sum of selected homogeneous pieces inherits the corresponding subset of a
monomial basis. This supplies the monomials of shifted coefficient modules,
whose allowed exponents lie in a translate of the positive monoid. Restriction
uses Mathlib's `Basis.span` and preserves the underlying basis vectors.
-/

public noncomputable section

namespace Mei.MonomialPresentation

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  {ℳ : ι → Submodule R M} (P : MonomialPresentation ℳ)

/-- An injectively indexed family of monomials presents the sum of its pieces.
The equality `hU` permits a named submodule as the carrier. -/
def subfamily {κ : Type*} (f : κ → ι) (hf : Function.Injective f)
    (U : Submodule R M) (hU : U = ⨆ j, ℳ (f j)) :
    MonomialPresentation (fun j => (ℳ (f j)).comap U.subtype) := by
  let v : κ → M := fun j => P.basis (f j)
  have hs : Submodule.span R (Set.range v) = ⨆ j, ℳ (f j) := by
    rw [Submodule.span_range_eq_iSup]
    simp only [v, P.grade_eq_span]
  let b := (Module.Basis.span (P.basis.linearIndependent.comp f hf)).map
    (LinearEquiv.ofEq _ _ (hs.trans hU.symm))
  have hb (j : κ) : (b j : M) = P.basis (f j) := by
    simp [b, LinearEquiv.coe_ofEq_apply]
  refine ⟨b, fun j => ?_⟩
  rw [P.grade_eq_span, ← hb j]
  exact LinearMap.submoduleOf_span_singleton_of_mem _ (b j).property

/-- Selecting an injective family retains its ambient monomials. -/
@[simp]
theorem coe_subfamily_basis {κ : Type*} (f : κ → ι) (hf : Function.Injective f)
    (U : Submodule R M) (hU : U = ⨆ j, ℳ (f j)) (j : κ) :
    ((P.subfamily f hf U hU).basis j : M) = P.basis (f j) := by
  simp [subfamily, LinearEquiv.coe_ofEq_apply]

/-- Selecting an injective family retains its ambient scalar coordinates. -/
@[simp]
theorem subfamily_repr {κ : Type*} (f : κ → ι) (hf : Function.Injective f)
    (U : Submodule R M) (hU : U = ⨆ j, ℳ (f j)) (x : U) (j : κ) :
    (P.subfamily f hf U hU).basis.repr x j = P.basis.repr (x : M) (f j) := by
  classical
  have h : (P.subfamily f hf U hU).basis.coord j =
      (P.basis.coord (f j)).comp U.subtype := by
    apply (P.subfamily f hf U hU).basis.ext
    intro l
    simp [Module.Basis.coord_apply, Finsupp.single_apply, hf.eq_iff]
  exact DFunLike.congr_fun h x

variable (s : Set ι)

/-- Restrict a monomial presentation to the sum of its pieces in `s`. -/
def supported :
    MonomialPresentation (fun i : s => (ℳ i).comap (⨆ j : s, ℳ j).subtype) :=
  P.subfamily (fun i : s => i.val) Subtype.val_injective _ rfl

/-- Restriction keeps each selected monomial as the same ambient vector. -/
@[simp]
theorem coe_supported_basis (i : s) :
    ((P.supported s).basis i : M) = P.basis i := P.coe_subfamily_basis _ _ _ _ i

/-- Restriction preserves every selected scalar coordinate. -/
@[simp]
theorem supported_repr (x : (⨆ j : s, ℳ j : Submodule R M)) (i : s) :
    (P.supported s).basis.repr x i = P.basis.repr (x : M) i :=
  P.subfamily_repr _ _ _ _ x i

end Mei.MonomialPresentation
