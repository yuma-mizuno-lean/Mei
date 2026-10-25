/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.ModuleCat.Semi.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Matching families of jointly injective spans

For a family of spans `B b → M (u b)`, `B b → M (v b)`, compatible chamber
values are those whose pair at every span lies in the image of its two legs.
Restriction to the chambers is a surjective linear map from matching families.
If the two legs of each span are jointly injective, restriction is a linear
equivalence: all face values are determined by the chamber values.

The final existence and uniqueness theorem glues linear families, including
common lifts of coefficient maps, without choosing lifts as extra data.
All constructions allow semirings and arbitrary, possibly infinite, families.

We use Mathlib's `MultispanIndex` and `WalkingMultispan` for the free incidence
category, and `LinearEquiv.ofInjective` to reconstruct each face value from its
pair of images.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.MultispanIndex

variable {R : Type*} [Semiring R] {J : MultispanShape}

/-- Chamber values whose incident pairs belong to the images of the spans. -/
def compatibleFamilies (I : MultispanIndex J (SemimoduleCat R)) :
    Submodule R (∀ j, I.right j) where
  carrier := {s | ∀ b, (s (J.fst b), s (J.snd b)) ∈
    LinearMap.range ((I.fst b).hom.prod (I.snd b).hom)}
  zero_mem' := fun b => (LinearMap.range _).zero_mem
  add_mem' := by
    intro s t hs ht b
    exact (LinearMap.range _).add_mem (hs b) (ht b)
  smul_mem' := by
    intro r s hs b
    exact (LinearMap.range _).smul_mem r (hs b)

/-- Compatibility is exactly membership in the paired image at each span. -/
@[simp]
theorem mem_compatibleFamilies {I : MultispanIndex J (SemimoduleCat R)}
    {s : ∀ j, I.right j} :
    s ∈ I.compatibleFamilies ↔ ∀ b, (s (J.fst b), s (J.snd b)) ∈
      LinearMap.range ((I.fst b).hom.prod (I.snd b).hom) := Iff.rfl

/-- Restrict a matching family to its chamber values. -/
def restrictSections (I : MultispanIndex J (SemimoduleCat R)) :
    I.multispan.sectionsSubmodule →ₗ[R] I.compatibleFamilies where
  toFun s := ⟨fun j => s.val (.right j), mem_compatibleFamilies.mpr fun b => by
    refine ⟨s.val (.left b), ?_⟩
    exact Prod.ext
      ((Functor.mem_sectionsSubmodule.mp s.property) (WalkingMultispan.Hom.fst b))
      ((Functor.mem_sectionsSubmodule.mp s.property) (WalkingMultispan.Hom.snd b))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrictSections_apply (I : MultispanIndex J (SemimoduleCat R))
    (s : I.multispan.sectionsSubmodule) (j : J.R) :
    (I.restrictSections s).val j = s.val (.right j) := (rfl)

/-- Every compatible family has a matching extension; injectivity is unnecessary here. -/
theorem restrictSections_surjective (I : MultispanIndex J (SemimoduleCat R)) :
    Function.Surjective I.restrictSections := by
  intro s
  choose t ht using fun b =>
    LinearMap.mem_range.mp ((mem_compatibleFamilies.mp s.property) b)
  refine ⟨⟨fun j => match j with
    | .left b => t b
    | .right j => s.val j, ?_⟩, rfl⟩
  apply Functor.mem_sectionsSubmodule.mpr
  rintro _ _ (j | b | b)
  · simp only [WalkingMultispan.Hom.id_eq_id, Functor.map_id]
    rfl
  · exact congrArg _root_.Prod.fst (ht b)
  · exact congrArg _root_.Prod.snd (ht b)

/-- Joint injectivity of each span makes chamber restriction injective. -/
theorem restrictSections_injective (I : MultispanIndex J (SemimoduleCat R))
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    Function.Injective I.restrictSections := by
  intro s t hst
  have hr (j) : s.val (.right j) = t.val (.right j) :=
    congrArg (fun x : I.compatibleFamilies => x.val j) hst
  apply Subtype.ext
  funext j
  cases j with
  | right j => exact hr j
  | left b =>
    have hs := Functor.mem_sectionsSubmodule.mp s.property
    have ht := Functor.mem_sectionsSubmodule.mp t.property
    apply h b
    apply Prod.ext
    · exact (hs (WalkingMultispan.Hom.fst b)).trans
        ((hr _).trans (ht (WalkingMultispan.Hom.fst b)).symm)
    · exact (hs (WalkingMultispan.Hom.snd b)).trans
        ((hr _).trans (ht (WalkingMultispan.Hom.snd b)).symm)

/-- Matching families are precisely compatible chamber families when every span
is jointly injective. -/
noncomputable def sectionsEquivCompatibleFamilies
    (I : MultispanIndex J (SemimoduleCat R))
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom)) :
    I.multispan.sectionsSubmodule ≃ₗ[R] I.compatibleFamilies :=
  LinearEquiv.ofBijective I.restrictSections
    ⟨I.restrictSections_injective h, I.restrictSections_surjective⟩

@[simp]
theorem sectionsEquivCompatibleFamilies_apply
    (I : MultispanIndex J (SemimoduleCat R))
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.multispan.sectionsSubmodule) :
    I.sectionsEquivCompatibleFamilies h s = I.restrictSections s := (rfl)

/-- Reconstructing a matching family retains its prescribed chamber values. -/
@[simp]
theorem sectionsEquivCompatibleFamilies_symm_apply_right
    (I : MultispanIndex J (SemimoduleCat R))
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (j : J.R) :
    ((I.sectionsEquivCompatibleFamilies h).symm s).val (.right j) = s.val j := by
  exact congrArg (fun x : I.compatibleFamilies => x.val j)
    ((I.sectionsEquivCompatibleFamilies h).apply_symm_apply s)

/-- A reconstructed face value is the unique inverse image of its incident pair. -/
@[simp]
theorem sectionsEquivCompatibleFamilies_symm_apply_left
    (I : MultispanIndex J (SemimoduleCat R))
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) :
    ((I.sectionsEquivCompatibleFamilies h).symm s).val (.left b) =
      (LinearEquiv.ofInjective ((I.fst b).hom.prod (I.snd b).hom) (h b)).symm
        ⟨(s.val (J.fst b), s.val (J.snd b)), (mem_compatibleFamilies.mp s.property) b⟩ := by
  have hs := Functor.mem_sectionsSubmodule.mp
    ((I.sectionsEquivCompatibleFamilies h).symm s).property
  apply h b
  rw [LinearEquiv.ofInjective_symm_apply]
  apply Prod.ext
  · exact (hs (WalkingMultispan.Hom.fst b)).trans
      (I.sectionsEquivCompatibleFamilies_symm_apply_right h s _)
  · exact (hs (WalkingMultispan.Hom.snd b)).trans
      (I.sectionsEquivCompatibleFamilies_symm_apply_right h s _)

/-- Linear chamber maps extend uniquely to matching families exactly when each
incident pair takes values in the span image. Each span then receives a common lift. -/
theorem existsUnique_sections_lift_iff (I : MultispanIndex J (SemimoduleCat R))
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    {E : Type*} [AddCommMonoid E] [Module R E] (α : ∀ j, E →ₗ[R] I.right j) :
    (∃! ℓ : E →ₗ[R] I.multispan.sectionsSubmodule,
        ∀ x j, (ℓ x).val (.right j) = α j x) ↔
      ∀ x b, (α (J.fst b) x, α (J.snd b) x) ∈
        LinearMap.range ((I.fst b).hom.prod (I.snd b).hom) := by
  constructor
  · rintro ⟨ℓ, hℓ, -⟩ x b
    have hx := (mem_compatibleFamilies.mp (I.restrictSections (ℓ x)).property) b
    simpa only [restrictSections_apply, hℓ] using hx
  intro hα
  let a : E →ₗ[R] I.compatibleFamilies :=
    (LinearMap.pi α).codRestrict I.compatibleFamilies
      (fun x => mem_compatibleFamilies.mpr (hα x))
  refine ⟨(I.sectionsEquivCompatibleFamilies h).symm.toLinearMap.comp a, ?_, ?_⟩
  · intro x j
    exact I.sectionsEquivCompatibleFamilies_symm_apply_right h (a x) j
  · intro ℓ hℓ
    apply LinearMap.ext
    intro x
    apply I.restrictSections_injective h
    apply Subtype.ext
    funext j
    exact (hℓ x j).trans
      (I.sectionsEquivCompatibleFamilies_symm_apply_right h (a x) j).symm

end CategoryTheory.Limits.MultispanIndex
