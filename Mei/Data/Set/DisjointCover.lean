/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Set.Lattice.Disjoint

/-!
# Reindexing disjoint covers by their points

A disjoint cover of each set in a labelled family parameterizes the incidences
between points and labels. `Mei.sigmaDisjointCoverEquiv` performs this reindexing
without identifying different labels whose domains overlap. It assembles
Mathlib's `Set.unionEqSigmaOfDisjoint` and preserves both the point and the label.
-/

public noncomputable section

open Set

namespace Mei

variable {α ι : Type*} {κ : ι → Type*} {D : ι → Set α} {X : ∀ t, κ t → Set α}
  (hdisj : ∀ t, Pairwise fun j l => Disjoint (X t j) (X t l))
  (hcover : ∀ t, ⋃ j, X t j = D t)

/-- Reindex chart points in disjoint covers by the point and its original label. -/
def sigmaDisjointCoverEquiv : (Σ t, Σ j, X t j) ≃ Σ Q, {t // Q ∈ D t} :=
  (Equiv.sigmaCongrRight fun t =>
    (unionEqSigmaOfDisjoint (hdisj t)).symm.trans (equivOfEq (hcover t))).trans
    { toFun := fun z => ⟨z.2.val, z.1, z.2.property⟩
      invFun := fun z => ⟨z.2.val, z.1, z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The incidence represented by a chart point consists of its point and label. -/
theorem sigmaDisjointCoverEquiv_apply (z : Σ t, Σ j, X t j) :
    sigmaDisjointCoverEquiv hdisj hcover z =
      ⟨z.2.2.val, z.1, hcover z.1 ▸ mem_iUnion.mpr ⟨z.2.1, z.2.2.property⟩⟩ := (rfl)

/-- Reindexing a chart point preserves its underlying point. -/
@[simp]
theorem sigmaDisjointCoverEquiv_apply_fst (z : Σ t, Σ j, X t j) :
    (sigmaDisjointCoverEquiv hdisj hcover z).1 = z.2.2.val := by
  simp only [sigmaDisjointCoverEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.coe_fn_mk, equivOfEq_apply, coe_unionEqSigmaOfDisjoint_symm_apply]

/-- Reindexing a chart point preserves its original label. -/
@[simp]
theorem sigmaDisjointCoverEquiv_apply_val (z : Σ t, Σ j, X t j) :
    (sigmaDisjointCoverEquiv hdisj hcover z).2.val = z.1 := (rfl)

/-- Reindexing back to chart points preserves the underlying point. -/
@[simp]
theorem sigmaDisjointCoverEquiv_symm_apply_val
    (z : Σ Q, {t // Q ∈ D t}) :
    ((sigmaDisjointCoverEquiv hdisj hcover).symm z).2.2.val = z.1 := by
  rw [← sigmaDisjointCoverEquiv_apply_fst hdisj hcover, Equiv.apply_symm_apply]

/-- Reindexing back to chart points preserves the original label. -/
@[simp]
theorem sigmaDisjointCoverEquiv_symm_apply_fst
    (z : Σ Q, {t // Q ∈ D t}) :
    ((sigmaDisjointCoverEquiv hdisj hcover).symm z).1 = z.2.val := by
  rw [← sigmaDisjointCoverEquiv_apply_val hdisj hcover, Equiv.apply_symm_apply]

end Mei
