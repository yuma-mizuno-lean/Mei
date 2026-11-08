/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Category.AlgCat.Sections
public import Mei.Algebra.Category.SemimoduleCat.Multispan.Span
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Algebra matching families at one face between two chambers

A span of algebra homomorphisms `M ← B → M` between two chambers has matching sections
determined by the face value, whose two images give the chamber values. Neither leg needs to be
injective.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.MultispanIndex

universe v
variable {R : Type*} [CommRing R] {B M : Type v} [Ring B] [Ring M]
  [Algebra R B] [Algebra R M]

/-- The incidence diagram of one face between a negative and a positive chamber, both carrying
an algebra `M`, whose legs are `f` and `g`. -/
abbrev ofAlgHoms (f g : B →ₐ[R] M) :
    MultispanIndex (MultispanShape.ofLinearOrder Bool) (AlgCat R) where
  left _ := AlgCat.of R B
  right _ := AlgCat.of R M
  fst _ := AlgCat.ofHom f
  snd _ := AlgCat.ofHom g

/-- The algebra sections of a span of algebra homomorphisms are the semimodule sections of the
underlying span of linear maps, componentwise. -/
def sectionsLinearEquivOfAlgHoms (f g : B →ₐ[R] M) :
    AlgCat.sectionsSubalgebra (ofAlgHoms f g).multispan ≃ₗ[R]
      SemimoduleCat.sectionsSubmodule (ofLinearMaps f.toLinearMap g.toLinearMap).multispan where
  toFun x := ⟨fun j => match j with
      | .left c => x.val (.left c)
      | .right b => x.val (.right b),
    (mem_sectionsSubmodule_multispan _).mpr
      ⟨fun c => x.property (.fst c), fun c => x.property (.snd c)⟩⟩
  invFun x := ⟨fun j => match j with
      | .left c => x.val (.left c)
      | .right b => x.val (.right b), by
    intro j j' h
    cases h with
    | id j => rfl
    | fst c => exact ((mem_sectionsSubmodule_multispan _).mp x.property).1 c
    | snd c => exact ((mem_sectionsSubmodule_multispan _).mp x.property).2 c⟩
  map_add' _ _ := Subtype.ext (funext fun j => by cases j <;> rfl)
  map_smul' _ _ := Subtype.ext (funext fun j => by cases j <;> rfl)
  left_inv _ := Subtype.ext (funext fun j => by cases j <;> rfl)
  right_inv _ := Subtype.ext (funext fun j => by cases j <;> rfl)

/-- Conversion to semimodule sections preserves face components. -/
@[simp]
theorem sectionsLinearEquivOfAlgHoms_apply_left (f g : B →ₐ[R] M)
    (x : AlgCat.sectionsSubalgebra (ofAlgHoms f g).multispan)
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    (sectionsLinearEquivOfAlgHoms f g x).val (.left c) = x.val (.left c) := by
  rw [sectionsLinearEquivOfAlgHoms]
  rfl

/-- Conversion to semimodule sections preserves chamber components. -/
@[simp]
theorem sectionsLinearEquivOfAlgHoms_apply_right (f g : B →ₐ[R] M)
    (x : AlgCat.sectionsSubalgebra (ofAlgHoms f g).multispan)
    (b : (MultispanShape.ofLinearOrder Bool).R) :
    (sectionsLinearEquivOfAlgHoms f g x).val (.right b) = x.val (.right b) := by
  rw [sectionsLinearEquivOfAlgHoms]
  rfl

/-- Conversion from semimodule sections preserves face components. -/
@[simp]
theorem sectionsLinearEquivOfAlgHoms_symm_apply_left (f g : B →ₐ[R] M)
    (x : SemimoduleCat.sectionsSubmodule
      (ofLinearMaps f.toLinearMap g.toLinearMap).multispan)
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    ((sectionsLinearEquivOfAlgHoms f g).symm x).val (.left c) = x.val (.left c) := by
  rw [sectionsLinearEquivOfAlgHoms]
  rfl

/-- Conversion from semimodule sections preserves chamber components. -/
@[simp]
theorem sectionsLinearEquivOfAlgHoms_symm_apply_right (f g : B →ₐ[R] M)
    (x : SemimoduleCat.sectionsSubmodule
      (ofLinearMaps f.toLinearMap g.toLinearMap).multispan)
    (b : (MultispanShape.ofLinearOrder Bool).R) :
    ((sectionsLinearEquivOfAlgHoms f g).symm x).val (.right b) = x.val (.right b) := by
  rw [sectionsLinearEquivOfAlgHoms]
  rfl

/-- Matching algebra sections of one face are equivalent to its face algebra. The chamber
values are the images of the face value under the two legs. -/
def sectionsAlgEquivOfAlgHoms (f g : B →ₐ[R] M) :
    AlgCat.sectionsSubalgebra (ofAlgHoms f g).multispan ≃ₐ[R] B where
  toFun s := s.val (.left default)
  invFun b := ⟨fun j => match j with
      | .left _ => b
      | .right false => f b
      | .right true => g b, by
    intro j j' h
    cases h with
    | id j => rfl
    | fst c => obtain rfl : c = default := Subsingleton.elim _ _; rfl
    | snd c => obtain rfl : c = default := Subsingleton.elim _ _; rfl⟩
  left_inv s := by
    apply Subtype.ext
    funext j
    cases j with
    | left c =>
      obtain rfl : c = default := Subsingleton.elim _ _
      rfl
    | right b => cases b with
      | false => exact s.property (.fst default)
      | true => exact s.property (.snd default)
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The equivalence reads off the face component. -/
@[simp]
theorem sectionsAlgEquivOfAlgHoms_apply (f g : B →ₐ[R] M)
    (s : AlgCat.sectionsSubalgebra (ofAlgHoms f g).multispan) :
    sectionsAlgEquivOfAlgHoms f g s = s.val (.left default) := (rfl)

/-- The face component of the section with a given face value is that value. -/
@[simp]
theorem sectionsAlgEquivOfAlgHoms_symm_apply_left (f g : B →ₐ[R] M) (b : B)
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    ((sectionsAlgEquivOfAlgHoms f g).symm b).val (.left c) = b := by
  obtain rfl : c = default := Subsingleton.elim _ _
  rfl

/-- The negative chamber value of the section with a given face value is its image under the
negative leg. -/
@[simp]
theorem sectionsAlgEquivOfAlgHoms_symm_apply_right_false (f g : B →ₐ[R] M) (b : B) :
    ((sectionsAlgEquivOfAlgHoms f g).symm b).val (.right false) = f b := (rfl)

/-- The positive chamber value of the section with a given face value is its image under the
positive leg. -/
@[simp]
theorem sectionsAlgEquivOfAlgHoms_symm_apply_right_true (f g : B →ₐ[R] M) (b : B) :
    ((sectionsAlgEquivOfAlgHoms f g).symm b).val (.right true) = g b := (rfl)

end CategoryTheory.Limits.MultispanIndex
