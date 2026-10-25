/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Sections
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.Submodule.Equiv

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

`existsUnique_sections_lift_iff` characterizes linear gluing from an arbitrary semimodule:
the chamber maps lift uniquely precisely when their incident pairs lie in each span image.
It uses Mathlib's `LinearMap.pi` and `LinearMap.codRestrict` to package the compatible maps.
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

/-- A reconstructed face value is the unique inverse image of its incident pair. -/
theorem matchingFamilyEquiv_symm_apply_left
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) :
    ((I.matchingFamilyEquiv h).symm s).val (.left b) =
      (LinearEquiv.ofInjective ((I.fst b).hom.prod (I.snd b).hom) (h b)).symm
        ⟨(s.val (J.fst b), s.val (J.snd b)), by
          obtain ⟨z, hz, hz'⟩ := (I.mem_compatibleFamilies).mp s.property b
          exact ⟨z, by simpa only [LinearMap.prod_apply, Function.prod_apply]
            using Prod.ext hz hz'⟩⟩ := by
  apply h b
  rw [LinearEquiv.ofInjective_symm_apply]
  simpa only [LinearMap.prod_apply, Function.prod_apply] using
    Prod.ext (I.fst_matchingFamilyEquiv_symm_apply_left h s b)
      (I.snd_matchingFamilyEquiv_symm_apply_left h s b)

/-- Linear chamber maps extend uniquely to matching families exactly when each
incident pair takes values in the span image. Each span then receives a common lift. -/
theorem existsUnique_sections_lift_iff
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    {E : Type*} [AddCommMonoid E] [Module R E] (α : ∀ j, E →ₗ[R] I.right j) :
    (∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule I.multispan,
        ∀ x j, (ℓ x).val (.right j) = α j x) ↔
      ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
        LinearMap.range ((I.fst b).hom.prod (I.snd b).hom) := by
  constructor
  · rintro ⟨ℓ, hℓ, -⟩ x b
    obtain ⟨z, hz, hz'⟩ :=
      (I.mem_compatibleFamilies).mp (I.restrictSections (ℓ x)).property b
    refine ⟨z, Prod.ext ?_ ?_⟩
    · simpa only [LinearMap.prod_apply, Function.prod_apply, restrictSections_apply, hℓ]
        using hz
    · simpa only [LinearMap.prod_apply, Function.prod_apply, restrictSections_apply, hℓ]
        using hz'
  intro hα
  let a : E →ₗ[R] I.compatibleFamilies :=
    (LinearMap.pi α).codRestrict I.compatibleFamilies (fun x =>
      (I.mem_compatibleFamilies).mpr fun b => by
        obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (hα x b)
        exact ⟨z, congrArg _root_.Prod.fst hz, congrArg _root_.Prod.snd hz⟩)
  refine ⟨(I.matchingFamilyEquiv h).symm.toLinearMap.comp a, ?_, ?_⟩
  · intro x j
    exact I.matchingFamilyEquiv_symm_apply_right h (a x) j
  · intro ℓ hℓ
    apply LinearMap.ext
    intro x
    apply I.restrictSections_injective h
    apply Subtype.ext
    funext j
    exact (hℓ x j).trans
      (I.matchingFamilyEquiv_symm_apply_right h (a x) j).symm

/-- A face value is the reconstructed common lift exactly when its two images are the
prescribed chamber values. Joint injectivity gives uniqueness of this lift. -/
theorem eq_matchingFamilyEquiv_symm_apply_left_iff
    (hinj : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) {x : I.left b} :
    x = ((I.matchingFamilyEquiv hinj).symm s).val (.left b) ↔
      I.fst b x = s.val (J.fst b) ∧ I.snd b x = s.val (J.snd b) := by
  refine ⟨by rintro rfl; simp, fun h => hinj b (Prod.ext ?_ ?_)⟩
  · exact h.1.trans (I.fst_matchingFamilyEquiv_symm_apply_left hinj s b).symm
  · exact h.2.trans (I.snd_matchingFamilyEquiv_symm_apply_left hinj s b).symm

end CategoryTheory.Limits.MultispanIndex
