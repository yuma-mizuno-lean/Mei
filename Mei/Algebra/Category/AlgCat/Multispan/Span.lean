/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Category.AlgCat.Sections
public import Mei.Algebra.Category.SemimoduleCat.Multispan.Span

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

/-- The algebra sections of a span of algebra homomorphisms are the semimodule sections of the
underlying span of linear maps, via their common face algebra. -/
def sectionsLinearEquivOfAlgHoms (f g : B →ₐ[R] M) :
    AlgCat.sectionsSubalgebra (ofAlgHoms f g).multispan ≃ₗ[R]
      SemimoduleCat.sectionsSubmodule (ofLinearMaps f.toLinearMap g.toLinearMap).multispan :=
  (sectionsAlgEquivOfAlgHoms f g).toLinearEquiv.trans
    (sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap).symm

/-- Conversion to semimodule sections preserves face components. -/
@[simp]
theorem sectionsLinearEquivOfAlgHoms_apply_left (f g : B →ₐ[R] M)
    (x : AlgCat.sectionsSubalgebra (ofAlgHoms f g).multispan)
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    (sectionsLinearEquivOfAlgHoms f g x).val (.left c) = x.val (.left c) := by
  obtain rfl : c = default := Subsingleton.elim _ _
  change (((sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap).symm
    (sectionsAlgEquivOfAlgHoms f g x)).val (.left default) : B) = x.val (.left default)
  rw [sectionsLinearEquivOfLinearMaps_symm_apply_left, sectionsAlgEquivOfAlgHoms_apply]

/-- Conversion to semimodule sections preserves chamber components. -/
@[simp]
theorem sectionsLinearEquivOfAlgHoms_apply_right (f g : B →ₐ[R] M)
    (x : AlgCat.sectionsSubalgebra (ofAlgHoms f g).multispan)
    (b : (MultispanShape.ofLinearOrder Bool).R) :
    HEq ((sectionsLinearEquivOfAlgHoms f g x).val (.right b)) (x.val (.right b)) := by
  cases b with
  | false =>
    apply heq_of_eq
    change ((((sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap).symm
      (sectionsAlgEquivOfAlgHoms f g x)).val (.right false) : M) = x.val (.right false))
    have hleft := sectionsLinearEquivOfLinearMaps_symm_apply_left f.toLinearMap g.toLinearMap
      (sectionsAlgEquivOfAlgHoms f g x) default
    have h := ofLinearMaps_apply_left f.toLinearMap g.toLinearMap default
      ((sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap).symm
        (sectionsAlgEquivOfAlgHoms f g x)).property
    rw [hleft, sectionsAlgEquivOfAlgHoms_apply] at h
    have hx := x.property (.fst default)
    exact h.1.symm.trans hx
  | true =>
    apply heq_of_eq
    change ((((sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap).symm
      (sectionsAlgEquivOfAlgHoms f g x)).val (.right true) : M) = x.val (.right true))
    have hleft := sectionsLinearEquivOfLinearMaps_symm_apply_left f.toLinearMap g.toLinearMap
      (sectionsAlgEquivOfAlgHoms f g x) default
    have h := ofLinearMaps_apply_left f.toLinearMap g.toLinearMap default
      ((sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap).symm
        (sectionsAlgEquivOfAlgHoms f g x)).property
    rw [hleft, sectionsAlgEquivOfAlgHoms_apply] at h
    have hx := x.property (.snd default)
    exact h.2.symm.trans hx

/-- Conversion from semimodule sections preserves face components. -/
@[simp]
theorem sectionsLinearEquivOfAlgHoms_symm_apply_left (f g : B →ₐ[R] M)
    (x : SemimoduleCat.sectionsSubmodule
      (ofLinearMaps f.toLinearMap g.toLinearMap).multispan)
    (c : (MultispanShape.ofLinearOrder Bool).L) :
    ((sectionsLinearEquivOfAlgHoms f g).symm x).val (.left c) = x.val (.left c) := by
  obtain rfl : c = default := Subsingleton.elim _ _
  change (((sectionsAlgEquivOfAlgHoms f g).symm
    (sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap x)).val (.left default) : B) =
      x.val (.left default)
  rw [sectionsAlgEquivOfAlgHoms_symm_apply_left, sectionsLinearEquivOfLinearMaps_apply]

/-- Conversion from semimodule sections preserves chamber components. -/
@[simp]
theorem sectionsLinearEquivOfAlgHoms_symm_apply_right (f g : B →ₐ[R] M)
    (x : SemimoduleCat.sectionsSubmodule
      (ofLinearMaps f.toLinearMap g.toLinearMap).multispan)
    (b : (MultispanShape.ofLinearOrder Bool).R) :
    HEq (((sectionsLinearEquivOfAlgHoms f g).symm x).val (.right b)) (x.val (.right b)) := by
  cases b with
  | false =>
    apply heq_of_eq
    change ((((sectionsAlgEquivOfAlgHoms f g).symm
      (sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap x)).val (.right false) : M) =
        x.val (.right false))
    rw [sectionsAlgEquivOfAlgHoms_symm_apply_right_false,
      sectionsLinearEquivOfLinearMaps_apply]
    exact (ofLinearMaps_apply_left f.toLinearMap g.toLinearMap default x.property).1
  | true =>
    apply heq_of_eq
    change ((((sectionsAlgEquivOfAlgHoms f g).symm
      (sectionsLinearEquivOfLinearMaps f.toLinearMap g.toLinearMap x)).val (.right true) : M) =
        x.val (.right true))
    rw [sectionsAlgEquivOfAlgHoms_symm_apply_right_true,
      sectionsLinearEquivOfLinearMaps_apply]
    exact (ofLinearMaps_apply_left f.toLinearMap g.toLinearMap default x.property).2

end CategoryTheory.Limits.MultispanIndex
