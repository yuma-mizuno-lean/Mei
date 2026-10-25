/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.LinearAlgebra.Pi

/-!
# Matching families of semimodules

The matching families of a diagram of semimodules form a submodule of the product
of its objects. This extends the construction `ModuleCat.sectionsSubmodule` to
semirings and semimodules, so matching and gluing need no additive inverses.
The carrier is Mathlib's `Functor.sections` for the underlying diagram of types.
-/

public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {R : Type*} [Semiring R] {J : Type*} [Category* J]

/-- The submodule of families that match along every arrow of a diagram. -/
def sectionsSubmodule (F : J ⥤ SemimoduleCat R) : Submodule R (∀ j, F.obj j) where
  carrier := (F ⋙ forget (SemimoduleCat R)).sections
  zero_mem' := by intro i j f; exact (F.map f).hom.map_zero
  add_mem' := by
    intro s t hs ht i j f
    exact ((F.map f).hom.map_add _ _).trans (congrArg₂ (· + ·) (hs f) (ht f))
  smul_mem' := by
    intro r s hs i j f
    exact ((F.map f).hom.map_smul r _).trans (congrArg (r • ·) (hs f))

/-- Membership is the matching equation for every arrow. -/
@[simp]
theorem mem_sectionsSubmodule {F : J ⥤ SemimoduleCat R} {s : ∀ j, F.obj j} :
    s ∈ sectionsSubmodule F ↔ ∀ ⦃i j⦄ (f : i ⟶ j), (F.map f) (s i) = s j := Iff.rfl

end CategoryTheory.Functor
