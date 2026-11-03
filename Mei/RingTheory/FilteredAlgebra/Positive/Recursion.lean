/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.Positive.Basic
public import Mei.RingTheory.FilteredAlgebra.Module
public import Mei.LinearAlgebra.ModuleFiltration.Recursion

/-!
# Positive completed linear recursions

A filtration-raising linear endomorphism preserving a chosen positive subsemiring
has a positive completed recursion solution whenever the incoming element is
positive. At each finite order the solution is represented by a finite sum of
iterates of a positive representative. Different orders may use different
representatives, so the incoming element need not come from the original algebra.

The endomorphism need not be nilpotent on the original algebra or multiplicative.
The same positivity conclusion holds for every solution of the induced linear
recursion on the module completion, by uniqueness.
-/

public section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  {F : AlgFiltration A} {P : Subsemiring A}
  (f : Module.End R A)
  (hf : ∀ k, (F.toModuleFiltration R).submodule k ≤
    ((F.toModuleFiltration R).submodule (k + 1)).comap f)
  (hP : ∀ a ∈ P, f a ∈ P)

include hP

/-- Positive incoming elements have positive completed linear recursion solutions. -/
theorem IsPositive.completionRecursion {x : F.completion} (hx : F.IsPositive P x) :
    F.IsPositive P (F.moduleCompletionEquiv
      ((F.toModuleFiltration R).completionRecursion f hf
        ((F.moduleCompletionEquiv (R := R)).symm x))) := by
  apply hx.apply_of_projection_congr
  · intro k x y hxy
    simp only [projection_moduleCompletionEquiv, ModuleFiltration.projection_completionRecursion,
      projection_moduleCompletionEquiv_symm, hxy]
  · intro a ha
    rw [isPositive_iff]
    intro k
    refine ⟨f.finiteRecursion (k + 1) a,
      f.finiteRecursion_mem P.toAddSubmonoid hP (k + 1) ha, ?_⟩
    simp only [moduleCompletionEquiv_symm_toCompletion, projection_moduleCompletionEquiv,
      ModuleFiltration.projection_completionRecursion, ModuleFiltration.projection_of,
      ModuleFiltration.quotientRecursion_mk, Submodule.mkQ_apply,
      Submodule.Quotient.restrictScalarsEquiv_mk, Ideal.Quotient.mk_eq_mk]

/-- Every completed recursion solution is positive when its incoming value is positive. -/
theorem isPositive_moduleCompletionEquiv_of_eq_add
    {a x : (F.toModuleFiltration R).completion}
    (ha : F.IsPositive P (F.moduleCompletionEquiv a))
    (hx : x = a + (F.toModuleFiltration R).completionMap (F.toModuleFiltration R) f
      id monotone_id
      (fun k _ hu => (F.toModuleFiltration R).antitone (Nat.le_succ (k + 1))
        (hf (k + 1) hu)) x) :
    F.IsPositive P (F.moduleCompletionEquiv x) := by
  rw [(F.toModuleFiltration R).eq_completionRecursion_of_eq_add_completionMap f hf hx]
  simpa only [LinearEquiv.symm_apply_apply] using ha.completionRecursion f hf hP

end Mei.AlgFiltration
