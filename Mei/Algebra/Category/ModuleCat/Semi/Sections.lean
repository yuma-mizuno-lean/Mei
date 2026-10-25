/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.LinearAlgebra.Pi
public import Mei.LinearAlgebra.CommonLift

/-!
# Matching families of semimodule diagrams over incidence shapes

For a diagram `F : J ⥤ SemimoduleCat R` over a semiring, the matching families, which are
compatible with every arrow of `J`, form the submodule `SemimoduleCat.sectionsSubmodule F` of
`∀ j, F.obj j`. Its carrier is Mathlib's `Functor.sections` of the underlying type-valued
diagram, as for `ModuleCat.sectionsSubmodule`.

A `WalkingMultispan J` is the free incidence category on the two maps `J.fst J.snd : J.L → J.R`:
it has one arrow from `left b` to `right (J.fst b)` and one to `right (J.snd b)`, and no
other non-identity arrows. Think of `J.R` as chambers and of `J.L` as faces, each face being
incident to two chambers. For a diagram `F` of this shape, the two maps out of `F.obj (left b)`
form a span, and `SemimoduleCat.multispanRightSections F` consists of the families on chambers
whose two values at every face lie in the joint range of its span. When every face span is
jointly injective, restriction to chambers is a linear equivalence from matching families onto
these families (`SemimoduleCat.multispanSectionsEquiv`); the value at a face is the unique
common lift of its two chamber values (`LinearMap.codLift`).

This is the semimodule analogue of Mathlib's `MulticospanIndex.sectionsEquiv` for the dual
shape: there the right objects are determined by the left ones, while here the left objects
are determined by the right ones only under joint injectivity.
-/

public section

open CategoryTheory Limits

universe w w' u v

namespace SemimoduleCat

variable {R : Type u} [Semiring R]

section Sections

variable {J : Type*} [Category* J] (F : J ⥤ SemimoduleCat.{v} R)

/-- The families compatible with every arrow of a diagram of semimodules, as a submodule of the
product of its objects. -/
def sectionsSubmodule : Submodule R (∀ j, F.obj j) where
  carrier := (F ⋙ forget (SemimoduleCat R)).sections
  add_mem' {s t} hs ht j j' f := by simp [← hs f, ← ht f]
  zero_mem' f := by simp
  smul_mem' r s hs j j' f := by simp [← hs f]

variable {F} in
@[simp]
theorem mem_sectionsSubmodule_iff {s : ∀ j, F.obj j} :
    s ∈ sectionsSubmodule F ↔ ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).hom (s i) = s j :=
  Iff.rfl

/-- A matching family is compatible with every arrow of the diagram. -/
theorem map_sectionsSubmodule_apply (s : sectionsSubmodule F) {i j : J} (f : i ⟶ j) :
    (F.map f).hom (s.1 i) = s.1 j :=
  mem_sectionsSubmodule_iff.1 s.2 f

end Sections

section Multispan

variable {J : MultispanShape.{w, w'}} (F : WalkingMultispan J ⥤ SemimoduleCat.{v} R)

/-- The span at a left object `b` of a diagram over a walking multispan: the pair of maps from
`F.obj (left b)` to the objects at `right (J.fst b)` and `right (J.snd b)`. -/
abbrev multispanSpan (b : J.L) :
    F.obj (.left b) →ₗ[R] F.obj (.right (J.fst b)) × F.obj (.right (J.snd b)) :=
  (F.map (WalkingMultispan.Hom.fst b)).hom.prod (F.map (WalkingMultispan.Hom.snd b)).hom

/-- The families on the right objects whose two values at every left object `b` lie in the
joint range of the span at `b`. -/
def multispanRightSections : Submodule R (∀ x : J.R, F.obj (.right x)) :=
  ⨅ b : J.L, (LinearMap.range (multispanSpan F b)).comap
    ((LinearMap.proj (J.fst b)).prod (LinearMap.proj (J.snd b)))

variable {F} in
@[simp]
theorem mem_multispanRightSections_iff {s : ∀ x : J.R, F.obj (.right x)} :
    s ∈ multispanRightSections F ↔
      ∀ b : J.L, (s (J.fst b), s (J.snd b)) ∈ LinearMap.range (multispanSpan F b) := by
  simp [multispanRightSections]

/-- Restriction of a matching family to the right objects. -/
def multispanSectionsRestrict : sectionsSubmodule F →ₗ[R] multispanRightSections F :=
  LinearMap.codRestrict _ ((LinearMap.pi fun x : J.R =>
      LinearMap.proj (φ := fun j => F.obj j) (WalkingMultispan.right x)) ∘ₗ
    (sectionsSubmodule F).subtype) fun s =>
      mem_multispanRightSections_iff.2 fun b => ⟨s.1 (.left b), by
        simp [map_sectionsSubmodule_apply]⟩

@[simp]
theorem multispanSectionsRestrict_apply (s : sectionsSubmodule F) (x : J.R) :
    (multispanSectionsRestrict F s).1 x = s.1 (.right x) :=
  (rfl)

variable {F}
variable (hF : ∀ b : J.L, Function.Injective (multispanSpan F b))

/-- The value at a left object `b` of the matching family extending a family on right objects:
the unique common lift of its two values at the ends of `b`. -/
noncomputable def multispanLeftLift (b : J.L) :
    multispanRightSections F →ₗ[R] F.obj (.left b) :=
  (((LinearMap.proj (J.fst b)).prod (LinearMap.proj (J.snd b))) ∘ₗ
      (multispanRightSections F).subtype).codLift _ (hF b) fun s =>
    mem_multispanRightSections_iff.1 s.2 b

theorem multispanSpan_multispanLeftLift (b : J.L) (s : multispanRightSections F) :
    multispanSpan F b (multispanLeftLift hF b s) = (s.1 (J.fst b), s.1 (J.snd b)) :=
  LinearMap.congr_fun (LinearMap.comp_codLift _ _ (hF b) _) s

@[simp]
theorem map_fst_multispanLeftLift (b : J.L) (s : multispanRightSections F) :
    (F.map (WalkingMultispan.Hom.fst b)).hom (multispanLeftLift hF b s) = s.1 (J.fst b) :=
  congrArg Prod.fst (multispanSpan_multispanLeftLift hF b s)

@[simp]
theorem map_snd_multispanLeftLift (b : J.L) (s : multispanRightSections F) :
    (F.map (WalkingMultispan.Hom.snd b)).hom (multispanLeftLift hF b s) = s.1 (J.snd b) :=
  congrArg Prod.snd (multispanSpan_multispanLeftLift hF b s)

/-- An element at a left object `b` is the common lift of a family on right objects exactly when
its two images agree with the values of the family at the ends of `b`. -/
theorem eq_multispanLeftLift_iff {b : J.L} {s : multispanRightSections F} {y : F.obj (.left b)} :
    y = multispanLeftLift hF b s ↔ (F.map (WalkingMultispan.Hom.fst b)).hom y = s.1 (J.fst b) ∧
      (F.map (WalkingMultispan.Hom.snd b)).hom y = s.1 (J.snd b) := by
  refine ⟨by rintro rfl; simp, fun h => hF b (Prod.ext ?_ ?_)⟩ <;> simp [h]

/-- The family on all objects extending a family on right objects by common lifts. -/
private noncomputable def multispanExtend :
    multispanRightSections F →ₗ[R] ∀ j : WalkingMultispan J, F.obj j :=
  LinearMap.pi fun j => match j with
    | .left b => multispanLeftLift hF b
    | .right x => LinearMap.proj x ∘ₗ (multispanRightSections F).subtype

@[simp]
private theorem multispanExtend_apply_left (s : multispanRightSections F) (b : J.L) :
    multispanExtend hF s (.left b) = multispanLeftLift hF b s :=
  (rfl)

@[simp]
private theorem multispanExtend_apply_right (s : multispanRightSections F) (x : J.R) :
    multispanExtend hF s (.right x) = s.1 x :=
  (rfl)

private theorem multispanExtend_mem (s : multispanRightSections F) :
    multispanExtend hF s ∈ sectionsSubmodule F := by
  rw [mem_sectionsSubmodule_iff]
  rintro _ _ (_ | b | b) <;> simp

/-- A matching family is the extension of its restriction to the right objects. -/
private theorem multispanExtend_multispanSectionsRestrict (s : sectionsSubmodule F) :
    multispanExtend hF (multispanSectionsRestrict F s) = s.1 := by
  funext j
  cases j with
  | left b =>
    exact ((eq_multispanLeftLift_iff hF).2 (by simp [map_sectionsSubmodule_apply])).symm
  | right x => simp

/-- When every span of a diagram over a walking multispan is jointly injective, restriction to
the right objects identifies its matching families with the families on right objects whose
values at the two ends of every left object lie in the joint range of its span. -/
noncomputable def multispanSectionsEquiv :
    sectionsSubmodule F ≃ₗ[R] multispanRightSections F :=
  LinearEquiv.ofLinearMap (multispanSectionsRestrict F)
    (LinearMap.codRestrict _ (multispanExtend hF) (multispanExtend_mem hF))
    (LinearMap.ext fun s => Subtype.ext <| funext fun x => by simp)
    (LinearMap.ext fun s => Subtype.ext <| multispanExtend_multispanSectionsRestrict hF s)

@[simp]
theorem multispanSectionsEquiv_apply (s : sectionsSubmodule F) (x : J.R) :
    (multispanSectionsEquiv hF s).1 x = s.1 (.right x) :=
  (rfl)

@[simp]
theorem multispanSectionsEquiv_symm_apply_right (s : multispanRightSections F) (x : J.R) :
    ((multispanSectionsEquiv hF).symm s).1 (.right x) = s.1 x :=
  (rfl)

@[simp]
theorem multispanSectionsEquiv_symm_apply_left (s : multispanRightSections F) (b : J.L) :
    ((multispanSectionsEquiv hF).symm s).1 (.left b) = multispanLeftLift hF b s :=
  (rfl)

end Multispan

end SemimoduleCat
