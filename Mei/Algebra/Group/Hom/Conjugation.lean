/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Tactic.Group

/-!
# Conjugation through a quotient with abelian kernel

If the kernel of a group homomorphism is covered by the image of an abelian
group, conjugation on that image depends only on the projected element.
This applies to extensions of groups by additive coefficient modules, without
requiring either a chosen splitting or injectivity of the coefficient map.
-/

public section

namespace MonoidHom

variable {N G B : Type*} [CommGroup N] [Group G] [MulOneClass B]

/-- Conjugation on an abelian group image depends only on the projection when
the image contains the kernel. -/
theorem conj_eq_of_apply_eq (f : G →* B) (i : N →* G) (hker : f.ker ≤ i.range)
    {x y : G} (hxy : f x = f y) (a : N) :
    x * i a * x⁻¹ = y * i a * y⁻¹ := by
  have hz : y⁻¹ * x ∈ f.ker := (f.eq_iff).mp hxy
  obtain ⟨c, hc⟩ := hker hz
  calc
    x * i a * x⁻¹ = y * ((y⁻¹ * x) * i a * (y⁻¹ * x)⁻¹) * y⁻¹ := by group
    _ = y * i a * y⁻¹ := by
      rw [← hc, ((Commute.all c a).map i).mul_inv_cancel]

end MonoidHom
