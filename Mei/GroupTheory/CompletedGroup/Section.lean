/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.CategoryTheory.Grothendieck.SingleObj
public import Mei.GroupTheory.CompletedGroup.Basic

/-!
# Completed groups as section labels

The completed group of a tower is the automorphism group of the identity-transport section of
its one-object groupoids. Each component of a label is the corresponding finite-order
projection, so these labels combine with `CompletedGroup.map_projection` and the projection
rules for ordered products and reindexed maps.

The identification composes `CompletedGroup.sectionsSubgroupEquiv` with
`Functor.singleObjSectionAutEquiv`.
-/

public section

open CategoryTheory Mei Mei.CompletedGroup Opposite

universe w

namespace CategoryTheory.Functor

variable (F : ℕᵒᵖ ⥤ GrpCat.{w})

/-- A completed group is the automorphism group of the tower's identity-transport section. -/
noncomputable def completedGroupAutEquiv : completedGroup F ≃* Aut F.singleObjSection :=
  (sectionsSubgroupEquiv F).trans F.singleObjSectionAutEquiv

/-- Each fiber arrow is the corresponding finite-order projection. -/
@[simp]
theorem completedGroupAutEquiv_hom_app (g : completedGroup F) (k : ℕ) :
    (completedGroupAutEquiv F g).asIso.hom.app (op k) = projection k g := by
  rw [completedGroupAutEquiv, MulEquiv.trans_apply, singleObjSectionAutEquiv_hom_app]
  exact sectionsSubgroupEquiv_apply_val F g (op k)

/-- Recovering a completed group element from a label retains every finite projection. -/
@[simp]
theorem projection_completedGroupAutEquiv_symm (a : Aut F.singleObjSection) (k : ℕ) :
    projection k ((completedGroupAutEquiv F).symm a) = a.asIso.hom.app (op k) := by
  rw [completedGroupAutEquiv, MulEquiv.symm_trans_apply, projection_sectionsSubgroupEquiv_symm]
  exact F.singleObjSectionAutEquiv_symm_apply a (op k)

end CategoryTheory.Functor
