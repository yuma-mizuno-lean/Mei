/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Sections
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.LinearAlgebra.Prod

/-!
# Matching families for jointly injective spans

For an incidence diagram, regard the right objects as chamber modules and the left objects
as face modules. A matching section is determined by its chamber values when each pair of
face maps is jointly injective. Its possible chamber values are exactly those whose pairs
at every face lie in the range of the two face maps. `matchingFamilyEquiv` gives this as a
linear equivalence, with explicit chamber evaluations and equations characterizing the
reconstructed face values.

The incidence category is Mathlib's `WalkingMultispan`: its only nonidentity arrows are the
two incidences at each face. No finite index set, grading, or surjectivity of either leg is
required. We use `LinearEquiv.ofBijective` to equip restriction to chamber values with its
linear inverse; the compatible-family carrier is `SemimoduleCat.sectionsSubmodule`.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.MultispanIndex

variable {R : Type*} [Semiring R] {J : MultispanShape}
  (I : MultispanIndex J (SemimoduleCat R))

/-- Chamber families whose incident pairs belong to the range of each face span. -/
def compatibleFamilies : Submodule R (∀ j, I.right j) where
  carrier := {s | ∀ b, (s (J.fst b), s (J.snd b)) ∈
    LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)}
  zero_mem' := by intro b; exact Submodule.zero_mem _
  add_mem' := by intro s t hs ht b; exact Submodule.add_mem _ (hs b) (ht b)
  smul_mem' := by intro r s hs b; exact Submodule.smul_mem _ r (hs b)

/-- A compatible chamber family has a simultaneous preimage at every face. -/
@[simp]
theorem mem_compatibleFamilies {s : ∀ j, I.right j} :
    s ∈ I.compatibleFamilies ↔ ∀ b, ∃ x : I.left b,
      I.fst b x = s (J.fst b) ∧ I.snd b x = s (J.snd b) := by
  simp [compatibleFamilies, LinearMap.mem_range, Prod.ext_iff]

/-- Compatibility for a section of an incidence diagram is determined by its two kinds
of generating arrows. -/
@[simp high]
theorem mem_sectionsSubmodule_multispan {s : ∀ j, I.multispan.obj j} :
    s ∈ SemimoduleCat.sectionsSubmodule I.multispan ↔
      (∀ b, I.fst b (s (.left b)) = s (.right (J.fst b))) ∧
      (∀ b, I.snd b (s (.left b)) = s (.right (J.snd b))) := by
  rw [SemimoduleCat.mem_sectionsSubmodule]
  constructor
  · intro hs
    exact ⟨fun b => hs (WalkingMultispan.Hom.fst b),
      fun b => hs (WalkingMultispan.Hom.snd b)⟩
  · rintro ⟨hf, hg⟩ x y f
    cases f with
    | id x => simp
    | fst b => exact hf b
    | snd b => exact hg b

/-- Restrict a matching family to its chamber values. -/
def restrictSections : SemimoduleCat.sectionsSubmodule I.multispan →ₗ[R]
    I.compatibleFamilies where
  toFun s := ⟨fun j => s.val (.right j), (I.mem_compatibleFamilies).mpr fun b =>
    ⟨s.val (.left b), (I.mem_sectionsSubmodule_multispan.mp s.property).1 b,
      (I.mem_sectionsSubmodule_multispan.mp s.property).2 b⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction evaluates a section at its chamber object. -/
@[simp]
theorem restrictSections_apply (s : SemimoduleCat.sectionsSubmodule I.multispan) (j : J.R) :
    (I.restrictSections s).val j = s.val (.right j) := (rfl)

/-- Every compatible chamber family extends to a matching section. This existence statement
needs no injectivity; only uniqueness needs joint injectivity. -/
theorem restrictSections_surjective : Function.Surjective I.restrictSections := by
  classical
  intro s
  have hs := (I.mem_compatibleFamilies).mp s.property
  choose x hx hy using hs
  let t : ∀ j, I.multispan.obj j := fun j => match j with
    | .left b => x b
    | .right j => s.val j
  have ht : t ∈ SemimoduleCat.sectionsSubmodule I.multispan :=
    (I.mem_sectionsSubmodule_multispan).mpr ⟨hx, hy⟩
  exact ⟨⟨t, ht⟩, rfl⟩

/-- Jointly injective face spans make restriction to chambers injective. -/
theorem restrictSections_injective
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    Function.Injective I.restrictSections := by
  intro s t hst
  have hr (j : J.R) : s.val (.right j) = t.val (.right j) :=
    congrArg (fun x : I.compatibleFamilies => x.val j) hst
  apply Subtype.ext
  funext j
  cases j with
  | right j => exact hr j
  | left b =>
    apply hinj b
    apply Prod.ext
    · exact ((I.mem_sectionsSubmodule_multispan.mp s.property).1 b).trans
        ((hr _).trans ((I.mem_sectionsSubmodule_multispan.mp t.property).1 b).symm)
    · exact ((I.mem_sectionsSubmodule_multispan.mp s.property).2 b).trans
        ((hr _).trans ((I.mem_sectionsSubmodule_multispan.mp t.property).2 b).symm)

/-- Matching sections are linearly equivalent to compatible chamber families when the
face maps are jointly injective. -/
noncomputable def matchingFamilyEquiv
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    SemimoduleCat.sectionsSubmodule I.multispan ≃ₗ[R] I.compatibleFamilies :=
  LinearEquiv.ofBijective I.restrictSections
    ⟨I.restrictSections_injective hinj, I.restrictSections_surjective⟩

/-- The equivalence forgets the face values. -/
@[simp]
theorem matchingFamilyEquiv_apply
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : SemimoduleCat.sectionsSubmodule I.multispan) :
    I.matchingFamilyEquiv hinj s = I.restrictSections s := (rfl)

/-- Reconstructing a section retains the prescribed chamber values. -/
@[simp]
theorem matchingFamilyEquiv_symm_apply_right
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (j : J.R) :
    ((I.matchingFamilyEquiv hinj).symm s).val (.right j) = s.val j := by
  exact congrArg (fun x : I.compatibleFamilies => x.val j)
    ((I.matchingFamilyEquiv hinj).apply_symm_apply s)

/-- The reconstructed face value maps to the prescribed first chamber value. -/
@[simp]
theorem fst_matchingFamilyEquiv_symm_apply_left
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) :
    I.fst b (((I.matchingFamilyEquiv hinj).symm s).val (.left b)) = s.val (J.fst b) := by
  exact ((I.mem_sectionsSubmodule_multispan.mp
    ((I.matchingFamilyEquiv hinj).symm s).property).1 b).trans
    (I.matchingFamilyEquiv_symm_apply_right hinj s _)

/-- The reconstructed face value maps to the prescribed second chamber value. -/
@[simp]
theorem snd_matchingFamilyEquiv_symm_apply_left
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) :
    I.snd b (((I.matchingFamilyEquiv hinj).symm s).val (.left b)) = s.val (J.snd b) := by
  exact ((I.mem_sectionsSubmodule_multispan.mp
    ((I.matchingFamilyEquiv hinj).symm s).property).2 b).trans
    (I.matchingFamilyEquiv_symm_apply_right hinj s _)

end CategoryTheory.Limits.MultispanIndex
