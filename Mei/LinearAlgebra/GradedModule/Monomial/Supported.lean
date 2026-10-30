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
  {ℳ : ι → Submodule R M} (P : MonomialPresentation ℳ) (s : Set ι)

/-- Restrict a monomial presentation to the sum of its pieces in `s`. -/
def supported :
    MonomialPresentation (fun i : s => (ℳ i).comap (⨆ j : s, ℳ j).subtype) := by
  let v : s → M := fun i => P.basis i
  have hs : Submodule.span R (Set.range v) = ⨆ j : s, ℳ j := by
    rw [Submodule.span_range_eq_iSup]
    simp only [v, P.grade_eq_span]
  let b := (Module.Basis.span (P.basis.linearIndependent.comp (fun i : s => i.val)
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ hs)
  have hb (i : s) : (b i : M) = P.basis i := by
    simp [b, LinearEquiv.coe_ofEq_apply]
  refine ⟨b, fun i => ?_⟩
  rw [P.grade_eq_span, ← hb i]
  exact LinearMap.submoduleOf_span_singleton_of_mem _ (b i).property

/-- Restriction keeps each selected monomial as the same ambient vector. -/
@[simp]
theorem coe_supported_basis (i : s) :
    ((P.supported s).basis i : M) = P.basis i := by
  simp [supported, LinearEquiv.coe_ofEq_apply]

/-- Restriction preserves every selected scalar coordinate. -/
@[simp]
theorem supported_repr (x : (⨆ j : s, ℳ j : Submodule R M)) (i : s) :
    (P.supported s).basis.repr x i = P.basis.repr (x : M) i := by
  classical
  have h : (P.supported s).basis.coord i =
      (P.basis.coord i.val).comp (⨆ j : s, ℳ j).subtype := by
    apply (P.supported s).basis.ext
    intro j
    simp [Module.Basis.coord_apply, Finsupp.single_apply, Subtype.ext_iff]
  exact DFunLike.congr_fun h x

end Mei.MonomialPresentation
