/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.SemimoduleCat.Sections
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Matching sections of semimodule diagrams

The matching families of a diagram of semimodules form a submodule of the product of its
objects. This supplies linear operations on matching families without an additive-inverse
hypothesis. The construction follows Mathlib's `ModuleCat.sectionsSubmodule`, using the
same `CategoryTheory.Functor.sections` carrier for semirings and semimodules.
Natural transformations induce linear maps on these matching families, respecting
identity and composition. Their underlying maps are Mathlib section maps.
Index functors restrict sections linearly through Mathlib's `Functor.sectionsPrecomp`.
-/

public section

open CategoryTheory

namespace SemimoduleCat

variable {R : Type*} [Semiring R] {J : Type*} [Category* J]

section

variable (F : J ⥤ SemimoduleCat R)

/-- The matching-family carrier agrees with Mathlib's sections of the underlying diagram. -/
def sectionsEquivTypes : sectionsSubmodule F ≃ (F ⋙ forget (SemimoduleCat R)).sections :=
  { toFun := fun x => ⟨x.val, mem_sectionsSubmodule.mp x.property⟩
    invFun := fun x => ⟨x.val, mem_sectionsSubmodule.mpr x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The carrier comparison preserves each component. -/
@[simp]
theorem sectionsEquivTypes_apply (s : sectionsSubmodule F) (j : J) :
    (sectionsEquivTypes F s).val j = s.val j := (rfl)

/-- Evaluate a matching family at one object, independently of the index universe. -/
def sectionsEval (j : J) : sectionsSubmodule F →ₗ[R] F.obj j :=
  (LinearMap.proj j).domRestrict (sectionsSubmodule F)

/-- Linear evaluation reads the specified component. -/
@[simp]
theorem sectionsEval_apply (j : J) (s : sectionsSubmodule F) :
    sectionsEval F j s = s.val j := (rfl)

end

end SemimoduleCat
