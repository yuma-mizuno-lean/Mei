/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.SemimoduleCat.Multispan.Basic
public import Mei.Algebra.Category.SemimoduleCat.Sections

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

Linear chamber maps `α j : E →ₗ[R] I.right j` from an arbitrary semimodule whose incident
pairs lie in each span image assemble to a linear map `piCompatibleFamilies` into compatible
families. For jointly injective spans, `sectionsLift` glues them to a linear map into matching
sections whose face values map to the incident chamber values, and
`existsUnique_sections_lift_iff` shows that such a gluing exists, and is then
unique, precisely when every incident pair lies in the span image.

Natural transformations of the incidence diagrams transport compatible chamber
families and matching sections. Joint injectivity makes reconstruction of face
values commute with these coefficient changes, including maps with kernels.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.MultispanIndex

variable {R : Type*} [Semiring R] {J : MultispanShape}
  (I : MultispanIndex J (SemimoduleCat R))

/-- A reconstructed face value is the unique inverse image of its incident pair. -/
theorem matchingFamilyEquiv_symm_apply_left
    (h : ∀ b, Function.Injective ((I.fst b).hom.prod (I.snd b).hom))
    (s : I.compatibleFamilies) (b : J.L) :
    ((I.matchingFamilyEquiv h).symm s).val (.left b) =
      (LinearEquiv.ofInjective ((I.fst b).hom.prod (I.snd b).hom) (h b)).symm
        ⟨(s.val (J.fst b), s.val (J.snd b)),
          I.mem_compatibleFamilies_iff_forall_mem_range.mp s.property b⟩ := by
  apply h b
  rw [LinearEquiv.ofInjective_symm_apply]
  simpa only [LinearMap.prod_apply, Function.prod_apply] using
    Prod.ext (I.fst_matchingFamilyEquiv_symm_apply_left h s b)
      (I.snd_matchingFamilyEquiv_symm_apply_left h s b)

end CategoryTheory.Limits.MultispanIndex
