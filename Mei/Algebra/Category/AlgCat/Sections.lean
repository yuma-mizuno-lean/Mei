/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.AlgCat.Limits

/-!
# Algebra maps on matching families

Natural transformations of algebra diagrams induce algebra homomorphisms on their
matching families. This equips coefficientwise transport with multiplicative and
scalar compatibility while retaining Mathlib's `AlgCat.sectionsSubalgebra` carrier.
The underlying function is Mathlib's `Functor.sectionsFunctor` map.
-/

public section

open CategoryTheory

namespace AlgCat

universe u v w t
variable {R : Type u} [CommRing R] {J : Type v} [Category.{t} J]
  {F G H : J ⥤ AlgCat.{w} R}

/-- Apply a natural transformation of algebra diagrams to each component of a section. -/
def sectionsMap (α : F ⟶ G) : sectionsSubalgebra F →ₐ[R] sectionsSubalgebra G where
  toFun := (Functor.sectionsFunctor J).map (Functor.whiskerRight α (forget _))
  map_zero' := by ext j; exact map_zero (α.app j).hom
  map_one' := by ext j; exact map_one (α.app j).hom
  map_add' x y := by ext j; exact map_add (α.app j).hom _ _
  map_mul' x y := by ext j; exact map_mul (α.app j).hom _ _
  commutes' r := by ext j; exact (α.app j).hom.commutes r

/-- The component formula for a natural transformation acting on algebra sections. -/
@[simp]
theorem sectionsMap_apply (α : F ⟶ G) (x : sectionsSubalgebra F) (j : J) :
    (sectionsMap α x).val j = (α.app j).hom (x.val j) := (rfl)

/-- Identity transformations induce the identity algebra homomorphism on sections. -/
@[simp]
theorem sectionsMap_id : sectionsMap (𝟙 F) = AlgHom.id R _ := by
  ext x j
  rfl

/-- The algebra map on sections respects composition of natural transformations. -/
@[simp]
theorem sectionsMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    sectionsMap (α ≫ β) = (sectionsMap β).comp (sectionsMap α) := by
  ext x j
  rfl

end AlgCat
