/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Gluing
public import Mei.RingTheory.Node.ScalarTower
public import Mathlib.Algebra.Category.AlgCat.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# The nodal slab as a categorical limit

For a commutative `B`-algebra `R` and arbitrary `t, f : R`, the chamber gluing
cospan has the existing `slabAlgebra t f k` as its limit in `AlgCat B`. The
comparison with the chosen categorical limit preserves both projections.
No nilpotence or nonzerodivisor hypothesis is required for this fiber product.
Maps from the localized overlap are determined by their values after `rightGluing`.

We use Mathlib's `PullbackCone.IsLimit.mk` and `IsLimit.conePointUniqueUpToIso`,
and the gluing maps and slab algebra of `Mei.NodeAlgebra`. The local model follows
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Mei.NodeAlgebra

namespace Mei.NodeAlgebra

variable {R : Type*} [CommRing R]

variable (B : Type*) [CommRing B] [Algebra B R] (t f : R) (k : ℕ)

/-- The two nodal chambers glued over the localized overlap, viewed as `B`-algebras. -/
abbrev gluingCospan : WalkingCospan ⥤ AlgCat B :=
  cospan
    (AlgCat.ofHom ((leftGluing t f k).restrictScalars B))
    (AlgCat.ofHom ((rightGluing t f k).restrictScalars B))

/-- The existing slab projections give a cone on the gluing cospan. -/
abbrev slabCone : Cone (gluingCospan B t f k) :=
  PullbackCone.mk
    (AlgCat.ofHom (((AlgHom.fst R _ _).comp (slabAlgebra t f k).val).restrictScalars B))
    (AlgCat.ofHom (((AlgHom.snd R _ _).comp (slabAlgebra t f k).val).restrictScalars B))
    (by ext z; exact (mem_slabAlgebra_iff _ _ _).mp z.property)

/-- The cone point is the original fiber-product slab, with its original `B`-action. -/
@[simp]
theorem slabCone_pt : (slabCone B t f k).pt = AlgCat.of B (slabAlgebra t f k) := (rfl)

/-- The first cone leg is the actual left projection. -/
@[simp↓]
theorem slabCone_π_left (z : slabAlgebra t f k) :
    ((slabCone B t f k).π.app .left).hom z = z.val.1 := (rfl)

/-- The second cone leg is the actual right projection. -/
@[simp↓]
theorem slabCone_π_right (z : slabAlgebra t f k) :
    ((slabCone B t f k).π.app .right).hom z = z.val.2 := (rfl)

/-- Matching chamber coefficients are precisely the elements of the slab algebra. -/
def slabConeIsLimit : IsLimit (slabCone B t f k) := by
  refine PullbackCone.IsLimit.mk _ (fun s => ?_) ?_ ?_ ?_
  · exact AlgCat.ofHom ((s.fst.hom.prod s.snd.hom).codRestrict
      ((slabAlgebra t f k).restrictScalars B) (fun x => by
        rw [Subalgebra.mem_restrictScalars, mem_slabAlgebra_iff]
        exact ConcreteCategory.congr_hom s.condition x))
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s f hL hR
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (ConcreteCategory.congr_hom hL x) (ConcreteCategory.congr_hom hR x)

/-- The categorical matching algebra is canonically the existing slab algebra. -/
def slabLimitIso : AlgCat.of B (slabAlgebra t f k) ≅ limit (gluingCospan B t f k) :=
  (slabConeIsLimit B t f k).conePointUniqueUpToIso (limit.isLimit _)

/-- The comparison to the chosen categorical limit preserves every evaluation. -/
@[reassoc (attr := simp)]
theorem slabLimitIso_hom_π (j : WalkingCospan) :
    (slabLimitIso B t f k).hom ≫ limit.π (gluingCospan B t f k) j =
      (slabCone B t f k).π.app j := by
  simp [slabLimitIso, IsLimit.conePointUniqueUpToIso]

/-- The inverse comparison also preserves every evaluation. -/
@[reassoc (attr := simp↓)]
theorem slabLimitIso_inv_π (j : WalkingCospan) :
    (slabLimitIso B t f k).inv ≫ (slabCone B t f k).π.app j =
      limit.π (gluingCospan B t f k) j := by
  rw [← slabLimitIso_hom_π B t f k j, Iso.inv_hom_id_assoc]

end Mei.NodeAlgebra
