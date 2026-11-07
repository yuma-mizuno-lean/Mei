/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Basic

/-!
# Matching families at one face between two chambers

A span of linear maps `M ← B → M` is the incidence diagram of one face with a negative
chamber (`false`) and a positive chamber (`true`), both carrying the module `M`. We form it as
a multispan index over Mathlib's `MultispanShape.ofLinearOrder Bool`, whose single face has
`false` and `true` as its two incident chambers.

A matching section of this diagram is determined by its face component, whose images under the
two legs are the chamber values. Linear families of matching sections with prescribed chamber
values therefore correspond to linear common lifts of those values through the span, with no
injectivity assumption. Joint injectivity of the span, which is separate, makes the common lift,
and with it the matching family, unique.
-/

public section

open CategoryTheory

universe v

namespace CategoryTheory.Limits

/-- The negative chamber is the first incident chamber of the only face. -/
@[simp]
theorem MultispanShape.ofLinearOrder_bool_fst (c : (MultispanShape.ofLinearOrder Bool).L) :
    (MultispanShape.ofLinearOrder Bool).fst c = false := by
  obtain rfl : c = default := Subsingleton.elim _ _
  rfl

/-- The positive chamber is the second incident chamber of the only face. -/
@[simp]
theorem MultispanShape.ofLinearOrder_bool_snd (c : (MultispanShape.ofLinearOrder Bool).L) :
    (MultispanShape.ofLinearOrder Bool).snd c = true := by
  obtain rfl : c = default := Subsingleton.elim _ _
  rfl

namespace MultispanIndex

variable {R : Type*} {B M : Type v} [Semiring R] [AddCommMonoid B] [Module R B]
  [AddCommMonoid M] [Module R M]

/-- The incidence diagram of one face with face module `B` between a negative chamber and
a positive chamber, both carrying `M`, whose legs are `f` and `g`. -/
abbrev ofLinearMaps (f g : B →ₗ[R] M) :
    MultispanIndex (MultispanShape.ofLinearOrder Bool) (SemimoduleCat R) where
  left _ := SemimoduleCat.of R B
  right _ := SemimoduleCat.of R M
  fst _ := SemimoduleCat.ofHom f
  snd _ := SemimoduleCat.ofHom g

/-- The face component of a matching section maps to its chamber values. -/
theorem ofLinearMaps_apply_left (f g : B →ₗ[R] M) (c : (MultispanShape.ofLinearOrder Bool).L)
    {s : ∀ j, (ofLinearMaps f g).multispan.obj j}
    (hs : s ∈ SemimoduleCat.sectionsSubmodule (ofLinearMaps f g).multispan) :
    f (s (.left c)) = s (.right false) ∧ g (s (.left c)) = s (.right true) := by
  obtain ⟨h₁, h₂⟩ := (mem_sectionsSubmodule_multispan _).mp hs
  obtain rfl : c = default := Subsingleton.elim _ _
  exact ⟨h₁ default, h₂ default⟩

/-- Matching sections of one face are its face components: the chamber values are the images of
the face value under the two legs, so no joint injectivity is needed to recover them. -/
def sectionsLinearEquivOfLinearMaps (f g : B →ₗ[R] M) :
    SemimoduleCat.sectionsSubmodule (ofLinearMaps f g).multispan ≃ₗ[R] B where
  toFun s := s.val (.left default)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨fun j => match j with
      | .left _ => b
      | .right false => f b
      | .right true => g b,
    (mem_sectionsSubmodule_multispan _).mpr
      ⟨fun c => by obtain rfl : c = default := Subsingleton.elim _ _; rfl,
        fun c => by obtain rfl : c = default := Subsingleton.elim _ _; rfl⟩⟩
  left_inv s := by
    refine Subtype.ext (funext fun j => ?_)
    have h := ofLinearMaps_apply_left f g default s.property
    match j with
    | .left c => obtain rfl : c = default := Subsingleton.elim _ _; rfl
    | .right false => exact h.1
    | .right true => exact h.2
  right_inv _ := rfl

/-- The equivalence reads off the face component. -/
@[simp]
theorem sectionsLinearEquivOfLinearMaps_apply (f g : B →ₗ[R] M)
    (s : SemimoduleCat.sectionsSubmodule (ofLinearMaps f g).multispan) :
    sectionsLinearEquivOfLinearMaps f g s = s.val (.left default) := (rfl)

/-- The negative chamber value of the section with a given face value. -/
@[simp]
theorem sectionsLinearEquivOfLinearMaps_symm_apply_right_false (f g : B →ₗ[R] M) (b : B) :
    ((sectionsLinearEquivOfLinearMaps f g).symm b).val (.right false) = f b := (rfl)

/-- The positive chamber value of the section with a given face value. -/
@[simp]
theorem sectionsLinearEquivOfLinearMaps_symm_apply_right_true (f g : B →ₗ[R] M) (b : B) :
    ((sectionsLinearEquivOfLinearMaps f g).symm b).val (.right true) = g b := (rfl)

/-- Linear families of matching sections with prescribed chamber values correspond to
linear common lifts through the two legs, uniquely on both sides or on neither. -/
theorem existsUnique_sections_ofLinearMaps_iff {E : Type*} [AddCommMonoid E] [Module R E]
    (f g : B →ₗ[R] M) (a₀ a₁ : E → M) :
    (∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (ofLinearMaps f g).multispan,
        ∀ x, (ℓ x).val (.right false) = a₀ x ∧ (ℓ x).val (.right true) = a₁ x) ↔
      ∃! ℓ : E →ₗ[R] B, ∀ x, f (ℓ x) = a₀ x ∧ g (ℓ x) = a₁ x := by
  let e := sectionsLinearEquivOfLinearMaps f g
  let Φ : (E →ₗ[R] SemimoduleCat.sectionsSubmodule (ofLinearMaps f g).multispan) ≃
      (E →ₗ[R] B) :=
    { toFun := fun ℓ => (e : _ →ₗ[R] B) ∘ₗ ℓ
      invFun := fun m => (e.symm : B →ₗ[R] _) ∘ₗ m
      left_inv := fun ℓ => by ext; simp
      right_inv := fun m => by ext; simp }
  refine Iff.trans (existsUnique_congr fun ℓ => forall_congr' fun x => ?_)
    (Φ.existsUnique_congr_right (q := fun m => ∀ x, f (m x) = a₀ x ∧ g (m x) = a₁ x))
  have h := ofLinearMaps_apply_left f g default (ℓ x).property
  simp only [Φ, Equiv.coe_fn_mk, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e,
    sectionsLinearEquivOfLinearMaps_apply, h.1, h.2]
  exact Iff.rfl

end MultispanIndex

end CategoryTheory.Limits
