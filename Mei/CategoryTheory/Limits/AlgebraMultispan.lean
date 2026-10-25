/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.AlgCat.Sections
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.Algebra.Algebra.Prod

/-!
# Algebra sections of jointly injective spans

For a diagram of spans `N b → M (u b)`, `N b → M (v b)`, retain just the
values at the `M` objects, constrained to lie in the range of each paired span.
If the spans are jointly injective, these values determine a unique matching
family on the whole incidence category. Reconstruction preserves products and scalars; its
value at a span object is the unique common preimage of the adjacent values.
Natural transformations preserve this description of sections.

The incidence category is Mathlib's `WalkingMultispan`, rather than a new free
category. The section equivalence is assembled by Mathlib's `AlgEquiv.ofBijective`
from restriction, existence of common preimages and joint injectivity.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.MultispanIndex

universe u v w t
variable {R : Type u} [CommRing R] {J : MultispanShape.{v, w}}
  (I : MultispanIndex J (AlgCat.{t} R))

/-- Chamber values satisfying the range condition for every span. -/
def compatibleAlgebraFamilies : Subalgebra R (∀ b, I.right b) :=
  ⨅ a, ((I.fst a).hom.prod (I.snd a).hom).range.comap
    ((Pi.evalAlgHom R (fun b => I.right b) (J.fst a)).prod
      (Pi.evalAlgHom R (fun b => I.right b) (J.snd a)))

/-- Compatibility is membership of each adjacent pair in the actual span range. -/
@[simp]
theorem mem_compatibleAlgebraFamilies (x : ∀ b, I.right b) :
    x ∈ I.compatibleAlgebraFamilies ↔
      ∀ a, (x (J.fst a), x (J.snd a)) ∈ ((I.fst a).hom.prod (I.snd a).hom).range := by
  simp [compatibleAlgebraFamilies]

/-- Restrict a matching family on the incidence category to its chamber values. -/
def restrictAlgebraSections : AlgCat.sectionsSubalgebra I.multispan →ₐ[R]
    I.compatibleAlgebraFamilies where
  toFun x := by
    exact ⟨fun b => x.val (.right b), (mem_compatibleAlgebraFamilies I _).mpr fun a =>
      ⟨x.val (.left a), Prod.ext (x.property (.fst a)) (x.property (.snd a))⟩⟩
  map_zero' := by ext b; rfl
  map_one' := by ext b; rfl
  map_add' x y := by ext b; rfl
  map_mul' x y := by ext b; rfl
  commutes' r := by ext b; rfl

/-- Restriction reads exactly the components at chamber objects. -/
@[simp]
theorem restrictAlgebraSections_apply (x : AlgCat.sectionsSubalgebra I.multispan) (b : J.R) :
    (I.restrictAlgebraSections x).val b = x.val (.right b) := (rfl)

variable (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))

include hinj

/-- Under joint injectivity, chamber values determine all components of a section. -/
theorem restrictAlgebraSections_injective : Function.Injective I.restrictAlgebraSections := by
  intro x y hxy
  apply Subtype.ext
  funext j
  cases j with
  | right b => exact congrArg (fun z => z.val b) hxy
  | left a =>
    apply hinj a
    apply Prod.ext
    · exact (x.property (.fst a)).trans
        ((congrArg (fun z => z.val (J.fst a)) hxy).trans (y.property (.fst a)).symm)
    · exact (x.property (.snd a)).trans
        ((congrArg (fun z => z.val (J.snd a)) hxy).trans (y.property (.snd a)).symm)

omit hinj in
/-- Every compatible chamber family has a matching extension. Neither injectivity nor
surjectivity of either individual leg is required. -/
theorem restrictAlgebraSections_surjective : Function.Surjective I.restrictAlgebraSections := by
  intro x
  choose lift hlift using fun a => (mem_compatibleAlgebraFamilies I _).mp x.property a
  let s : ∀ j, I.multispan.obj j := fun j => match j with
    | .left a => lift a
    | .right b => x.val b
  have hs : s ∈ AlgCat.sectionsSubalgebra I.multispan := by
    intro j j' f
    cases f with
    | id j => rfl
    | fst a => exact congrArg _root_.Prod.fst (hlift a)
    | snd a => exact congrArg _root_.Prod.snd (hlift a)
  exact ⟨⟨s, hs⟩, by ext b; rfl⟩

/-- Matching families are algebraically equivalent to chamber families obeying the span
range constraints. This includes repeated endpoints and infinite incidence sets. -/
noncomputable def sectionsAlgEquivCompatibleFamilies :
    AlgCat.sectionsSubalgebra I.multispan ≃ₐ[R] I.compatibleAlgebraFamilies :=
  AlgEquiv.ofBijective I.restrictAlgebraSections
    ⟨I.restrictAlgebraSections_injective hinj, I.restrictAlgebraSections_surjective⟩

/-- The forward equivalence is restriction to chamber components. -/
@[simp]
theorem sectionsAlgEquivCompatibleFamilies_apply
    (x : AlgCat.sectionsSubalgebra I.multispan) (b : J.R) :
    (I.sectionsAlgEquivCompatibleFamilies hinj x).val b = x.val (.right b) := (rfl)

/-- Reconstruction has the prescribed value at every chamber. -/
@[simp]
theorem sectionsAlgEquivCompatibleFamilies_symm_apply_right
    (x : I.compatibleAlgebraFamilies) (b : J.R) :
    ((I.sectionsAlgEquivCompatibleFamilies hinj).symm x).val (.right b) = x.val b :=
  congrArg (fun z => z.val b) ((I.sectionsAlgEquivCompatibleFamilies hinj).apply_symm_apply x)

/-- The reconstructed value at a span object is characterized by its two images. -/
@[simp]
theorem sectionsAlgEquivCompatibleFamilies_symm_apply_left_iff
    (x : I.compatibleAlgebraFamilies) (a : J.L) (y : I.left a) :
    ((I.sectionsAlgEquivCompatibleFamilies hinj).symm x).val (.left a) = y ↔
      (I.fst a).hom y = x.val (J.fst a) ∧ (I.snd a).hom y = x.val (J.snd a) := by
  let s := (I.sectionsAlgEquivCompatibleFamilies hinj).symm x
  have hf : (I.fst a).hom (s.val (.left a)) = x.val (J.fst a) :=
    (s.property (.fst a)).trans
      (I.sectionsAlgEquivCompatibleFamilies_symm_apply_right hinj x _)
  have hg : (I.snd a).hom (s.val (.left a)) = x.val (J.snd a) :=
    (s.property (.snd a)).trans
      (I.sectionsAlgEquivCompatibleFamilies_symm_apply_right hinj x _)
  constructor
  · intro heq
    exact ⟨heq ▸ hf, heq ▸ hg⟩
  · intro hy
    exact hinj a (Prod.ext (hf.trans hy.1.symm) (hg.trans hy.2.symm))

omit hinj

variable {I} {I' I'' : MultispanIndex J (AlgCat.{t} R)}

/-- A natural transformation of span diagrams carries compatible chamber values to
compatible chamber values, without any injectivity hypothesis. -/
def compatibleAlgebraFamiliesMap (α : I.multispan ⟶ I'.multispan) :
    I.compatibleAlgebraFamilies →ₐ[R] I'.compatibleAlgebraFamilies where
  toFun x := by
    refine ⟨fun b => (α.app (.right b)).hom (x.val b),
      (mem_compatibleAlgebraFamilies I' _).mpr ?_⟩
    intro a
    obtain ⟨z, hz⟩ := (mem_compatibleAlgebraFamilies I _).mp x.property a
    refine ⟨(α.app (.left a)).hom z, ?_⟩
    have hf := congrArg (fun f => f.hom z) (α.naturality (.fst a))
    have hg := congrArg (fun f => f.hom z) (α.naturality (.snd a))
    simp only [multispan_map_fst] at hf
    simp only [multispan_map_snd] at hg
    exact Prod.ext
      (hf.symm.trans (congrArg (α.app (.right (J.fst a))).hom
        (congrArg _root_.Prod.fst hz)))
      (hg.symm.trans (congrArg (α.app (.right (J.snd a))).hom
        (congrArg _root_.Prod.snd hz)))
  map_zero' := by ext b; exact map_zero (α.app (.right b)).hom
  map_one' := by ext b; exact map_one (α.app (.right b)).hom
  map_add' x y := by ext b; exact map_add (α.app (.right b)).hom _ _
  map_mul' x y := by ext b; exact map_mul (α.app (.right b)).hom _ _
  commutes' r := by ext b; exact (α.app (.right b)).hom.commutes r

/-- Maps of compatible families act componentwise at the chamber objects. -/
@[simp]
theorem compatibleAlgebraFamiliesMap_apply (α : I.multispan ⟶ I'.multispan)
    (x : I.compatibleAlgebraFamilies) (b : J.R) :
    (compatibleAlgebraFamiliesMap α x).val b = (α.app (.right b)).hom (x.val b) := (rfl)

/-- Identity transformations act identically on compatible families. -/
@[simp]
theorem compatibleAlgebraFamiliesMap_id :
    compatibleAlgebraFamiliesMap (𝟙 I.multispan) = AlgHom.id R _ := by
  ext x b
  rfl

/-- The map on compatible families respects composition. -/
@[simp]
theorem compatibleAlgebraFamiliesMap_comp (α : I.multispan ⟶ I'.multispan)
    (β : I'.multispan ⟶ I''.multispan) :
    compatibleAlgebraFamiliesMap (α ≫ β) =
      (compatibleAlgebraFamiliesMap β).comp (compatibleAlgebraFamiliesMap α) := by
  ext x b
  rfl

/-- Restriction to chambers commutes with a natural transformation of span diagrams. -/
theorem restrictAlgebraSections_naturality (α : I.multispan ⟶ I'.multispan) :
    I'.restrictAlgebraSections.comp (AlgCat.sectionsMap α) =
      (compatibleAlgebraFamiliesMap α).comp I.restrictAlgebraSections := by
  ext x b
  simp

/-- Unique reconstruction of the face values commutes with coefficient maps. -/
theorem sectionsAlgEquivCompatibleFamilies_symm_naturality
    (hinj : ∀ a, Function.Injective ((I.fst a).hom.prod (I.snd a).hom))
    (hinj' : ∀ a, Function.Injective ((I'.fst a).hom.prod (I'.snd a).hom))
    (α : I.multispan ⟶ I'.multispan) (x : I.compatibleAlgebraFamilies) :
    AlgCat.sectionsMap α ((I.sectionsAlgEquivCompatibleFamilies hinj).symm x) =
      (I'.sectionsAlgEquivCompatibleFamilies hinj').symm (compatibleAlgebraFamiliesMap α x) := by
  apply I'.restrictAlgebraSections_injective hinj'
  ext b
  simp

end CategoryTheory.Limits.MultispanIndex
