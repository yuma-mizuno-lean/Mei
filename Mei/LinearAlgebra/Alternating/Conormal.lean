/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.LinearAlgebra.Orientation

/-!
# Conormal alternating forms

For a submodule `W` of `M`, the conormal forms are the alternating forms on `M` that vanish as
soon as one argument lies in `W`. A ray of such forms orients the quotient `M ⧸ W` from the
conormal side, without passing to the quotient module. Conormality of a ray does not depend on
the representing form, and reversing a ray preserves it.

These rays orient the normal quotients of polyhedra in polyhedral cochains.
-/

public section

variable {R M ι : Type*}

namespace Submodule

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The alternating forms on `M` that vanish as soon as one argument lies in `W`. -/
def conormalForms (W : Submodule R M) (ι : Type*) : Submodule R (M [⋀^ι]→ₗ[R] R) where
  carrier := {α | ∀ (v : ι → M) (j : ι), v j ∈ W → α v = 0}
  add_mem' {α β} hα hβ v j hv := by simp [hα v j hv, hβ v j hv]
  zero_mem' _ _ _ := rfl
  smul_mem' c α hα v j hv := by simp [hα v j hv]

/-- Membership in `conormalForms` is vanishing on every tuple with an argument in `W`. -/
@[simp]
theorem mem_conormalForms {W : Submodule R M} {α : M [⋀^ι]→ₗ[R] R} :
    α ∈ W.conormalForms ι ↔ ∀ (v : ι → M) (j : ι), v j ∈ W → α v = 0 := Iff.rfl

/-- Every alternating form is conormal to the zero submodule. -/
@[simp]
theorem conormalForms_bot : (⊥ : Submodule R M).conormalForms ι = ⊤ := by
  ext α
  simp only [mem_conormalForms, mem_bot, Submodule.mem_top, iff_true]
  exact fun v j hv => α.map_coord_zero j hv

end CommRing

end Submodule

namespace Module.Ray

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]

/-- A ray of alternating forms is conormal to `W` when it is represented by a form vanishing as
soon as one argument lies in `W`. By `isConormal_rayOfNeZero_iff`, every representative then
vanishes in this way. -/
def IsConormal (o : Module.Ray R (M [⋀^ι]→ₗ[R] R)) (W : Submodule R M) : Prop :=
  o.someVector ∈ W.conormalForms ι

/-- A ray is conormal exactly when any representing form is a conormal form. -/
@[simp]
theorem isConormal_rayOfNeZero_iff {α : M [⋀^ι]→ₗ[R] R} (hα : α ≠ 0) {W : Submodule R M} :
    (rayOfNeZero R α hα).IsConormal W ↔ α ∈ W.conormalForms ι := by
  have hβ := Module.Ray.someVector_ne_zero (rayOfNeZero R α hα)
  have hβα : SameRay R (rayOfNeZero R α hα).someVector α :=
    (ray_eq_iff hβ hα).mp (Module.Ray.someVector_ray _)
  obtain ⟨r, -, hr⟩ := hβα.exists_pos_left hβ hα
  obtain ⟨s, -, hs⟩ := hβα.symm.exists_pos_left hα hβ
  rw [IsConormal]
  exact ⟨fun hmem => hr ▸ Submodule.smul_mem _ r hmem,
    fun hmem => hs ▸ Submodule.smul_mem _ s hmem⟩

/-- Reversing a ray does not change conormality. -/
@[simp]
theorem isConormal_neg_iff {o : Module.Ray R (M [⋀^ι]→ₗ[R] R)} {W : Submodule R M} :
    (-o).IsConormal W ↔ o.IsConormal W := by
  induction o using Module.Ray.ind with
  | h α hα =>
    rw [neg_rayOfNeZero, isConormal_rayOfNeZero_iff, isConormal_rayOfNeZero_iff,
      Submodule.neg_mem_iff]

/-- Every ray of alternating forms is conormal to the zero submodule. -/
theorem isConormal_bot (o : Module.Ray R (M [⋀^ι]→ₗ[R] R)) : o.IsConormal ⊥ := by
  rw [IsConormal, Submodule.conormalForms_bot]
  exact Submodule.mem_top

end Module.Ray
