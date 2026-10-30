/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Naturality
public import Mei.RingTheory.Node.Diagram

/-!
# The focus-focus gluing diagram across coefficient orders

The two truncated chambers and their localized overlap form a cospan of
`K`-algebras at each order. Cutoff reductions give natural transformations of
these cospans, forming a tower. The existing slab algebra is a limit of the
cospan, and the maps induced on these limits are exactly the existing slab
reductions. Thus matching coefficients and their reductions can be used through
the categorical limit interface while retaining the original coefficient ring.

The construction uses `cospanHomMk`, `PullbackCone.IsLimit.mk`, the gluing
identities of `Mei.NodeAlgebra.localizedOverlapMap`, and the chamber and slab
reductions of `Mei.FocusFocus`. The local model follows Gross–Siebert,
*An Invitation to Toric Degenerations*, §2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped LaurentPolynomial Mei.NodeAlgebra

namespace Mei.FocusFocus

open AddMonoidAlgebra TauCeti Mei.NodeAlgebra _root_.LaurentPolynomial Mei.LaurentPolynomial

variable (K : Type*) [CommRing K]

local notation "S(" k ")" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ(" k ")" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "A(" k ")" => slabAlgebra (C (τ(k))) (1 + T 1) k
local notation "D(" k ")" => LocalizedOverlap (C (τ(k))) (1 + T 1) k

/-- The chamber gluing cospan over `K`, with the left incidence twisted by `1+w`. -/
abbrev gluingCospan (k : ℕ) : WalkingCospan ⥤ AlgCat K :=
  Mei.NodeAlgebra.gluingCospan K (C (τ(k))) (1 + T 1) k

/-- The left object is the actual nodal left chamber. -/
@[simp]
theorem gluingCospan_obj_left (k : ℕ) :
    (gluingCospan K k).obj .left = AlgCat.of K (TruncatedExponentChamber K k 1) := (rfl)

/-- The right object is the actual nodal right chamber. -/
@[simp]
theorem gluingCospan_obj_right (k : ℕ) :
    (gluingCospan K k).obj .right = AlgCat.of K (TruncatedExponentChamber K k 0) := (rfl)

/-- The overlap object inverts the slab function after imposing both cutoffs. -/
@[simp]
theorem gluingCospan_obj_one (k : ℕ) :
    (gluingCospan K k).obj .one = AlgCat.of K (D(k)) := (rfl)

private def chamberReduction {k l : ℕ} (hl : l ≤ k) (i : Fin 2) :
    TruncatedExponentChamber K k i →ₐ[K] TruncatedExponentChamber K l i :=
  letI : Algebra (S(k)[ℤ]) (S(l)[ℤ]) := (truncatedScalarMap (RingHom.id K) hl).toAlgebra
  letI : IsScalarTower K (S(k)[ℤ]) (S(l)[ℤ]) := by
    have h := congrArg (fun g : S(k)[ℤ] →+* S(l)[ℤ] => g.toAlgebra.toSMul)
      (truncatedScalarAlgHom_toRingHom (K := K) (hl := hl))
    exact h ▸ IsScalarTower.of_algHom (truncatedScalarAlgHom K hl)
  match i with
  | 0 =>
    letI := IsScalarTower.to₁₂₄ K (S(k)[ℤ]) (S(l)[ℤ]) (TruncatedExponentChamber K l 0)
    (rightChamberMap (C (τ(k))) (truncatedScalarMap_C_root (RingHom.id K) hl)
      hl).restrictScalars K
  | 1 =>
    letI := IsScalarTower.to₁₂₄ K (S(k)[ℤ]) (S(l)[ℤ]) (TruncatedExponentChamber K l 1)
    (leftChamberMap (C (τ(k))) (truncatedScalarMap_C_root (RingHom.id K) hl)
      hl).restrictScalars K

private def overlapReduction {k l : ℕ} (hl : l ≤ k) : D(k) →ₐ[K] D(l) :=
  letI : Algebra (S(k)[ℤ]) (S(l)[ℤ]) := (truncatedScalarMap (RingHom.id K) hl).toAlgebra
  letI : IsScalarTower K (S(k)[ℤ]) (S(l)[ℤ]) := by
    have h := congrArg (fun g : S(k)[ℤ] →+* S(l)[ℤ] => g.toAlgebra.toSMul)
      (truncatedScalarAlgHom_toRingHom (K := K) (hl := hl))
    exact h ▸ IsScalarTower.of_algHom (truncatedScalarAlgHom K hl)
  letI : IsScalarTower K (S(k)[ℤ]) (D(l)) :=
    IsScalarTower.to₁₂₄ K (S(k)[ℤ]) (S(l)[ℤ]) (D(l))
  let g : D(k) →ₐ[S(k)[ℤ]] D(l) :=
    localizedOverlapMap (C (τ(k))) (1 + T 1)
      (f' := (1 + T 1 : S(l)[ℤ])) (truncatedScalarMap_C_root (RingHom.id K) hl)
      (by simp [RingHom.algebraMap_toAlgebra]) hl
  g.restrictScalars K

private theorem overlapReduction_left {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 1) :
    overlapReduction K hl (leftGluing (C (τ(k))) (1 + T 1) k z) =
      leftGluing (C (τ(l))) (1 + T 1) l (chamberReduction K hl 1 z) := by
  let : Algebra (S(k)[ℤ]) (S(l)[ℤ]) := (truncatedScalarMap (RingHom.id K) hl).toAlgebra
  simpa only [overlapReduction, chamberReduction,
    AlgHom.restrictScalars_apply] using
    localizedOverlapMap_leftGluing (C (τ(k))) (1 + T 1)
    (f' := (1 + T 1 : S(l)[ℤ])) (truncatedScalarMap_C_root (RingHom.id K) hl)
    (by simp [RingHom.algebraMap_toAlgebra]) hl z

private theorem overlapReduction_right {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 0) :
    overlapReduction K hl (rightGluing (C (τ(k))) (1 + T 1) k z) =
      rightGluing (C (τ(l))) (1 + T 1) l (chamberReduction K hl 0 z) := by
  let : Algebra (S(k)[ℤ]) (S(l)[ℤ]) := (truncatedScalarMap (RingHom.id K) hl).toAlgebra
  simpa only [overlapReduction, chamberReduction,
    AlgHom.restrictScalars_apply] using
    localizedOverlapMap_rightGluing (C (τ(k))) (1 + T 1)
    (f' := (1 + T 1 : S(l)[ℤ])) (truncatedScalarMap_C_root (RingHom.id K) hl)
    (by simp [RingHom.algebraMap_toAlgebra]) hl z

/-- Reduction of the entire gluing cospan, including its localized overlap. -/
def gluingCospanReduction {k l : ℕ} (hl : l ≤ k) :
    gluingCospan K k ⟶ gluingCospan K l :=
  cospanHomMk (AlgCat.ofHom (overlapReduction K hl))
    (AlgCat.ofHom (chamberReduction K hl 1)) (AlgCat.ofHom (chamberReduction K hl 0))
    (by ext z; exact overlapReduction_left K hl z)
    (by ext z; exact overlapReduction_right K hl z)

/-- The left component is the existing chamber reduction. -/
@[simp↓]
theorem gluingCospanReduction_app_left {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 1) :
    ((gluingCospanReduction K hl).app .left).hom z =
      truncatedExponentChamberMap (RingHom.id K) hl 1 z := by
  rw [truncatedExponentChamberMap_one]
  rfl

/-- The right component is the existing chamber reduction. -/
@[simp↓]
theorem gluingCospanReduction_app_right {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 0) :
    ((gluingCospanReduction K hl).app .right).hom z =
      truncatedExponentChamberMap (RingHom.id K) hl 0 z := by
  rw [truncatedExponentChamberMap_zero]
  rfl

/-- Overlap reduction intertwines the right gluing incidence with the existing
right chamber reduction. Its values on this image determine the localization map. -/
@[simp↓]
theorem gluingCospanReduction_app_one_rightGluing {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 0) :
    ((gluingCospanReduction K hl).app .one).hom (rightGluing (C (τ(k))) (1 + T 1) k z) =
      rightGluing (C (τ(l))) (1 + T 1) l
        (truncatedExponentChamberMap (RingHom.id K) hl 0 z) := by
  rw [← gluingCospanReduction_app_right K hl z]
  exact overlapReduction_right K hl z

/-- Reduction to the same order is the identity of the entire gluing diagram. -/
@[simp]
theorem gluingCospanReduction_refl (k : ℕ) : gluingCospanReduction K (k := k) le_rfl = 𝟙 _ := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _)
  · apply AlgCat.hom_ext
    apply AlgHom.toRingHom_injective
    apply localizedOverlap_ringHom_ext
    intro z
    simp only [AlgHom.coe_toRingHom, NatTrans.id_app, AlgCat.hom_id]
    rw [gluingCospanReduction_app_one_rightGluing, truncatedExponentChamberMap_id]
    rfl
  · apply AlgCat.hom_ext
    apply AlgHom.ext
    intro z
    simp only [gluingCospanReduction_app_left, truncatedExponentChamberMap_id,
      NatTrans.id_app, AlgCat.hom_id, AlgHom.id_apply, RingHom.id_apply]
  · apply AlgCat.hom_ext
    apply AlgHom.ext
    intro z
    simp only [gluingCospanReduction_app_right, truncatedExponentChamberMap_id,
      NatTrans.id_app, AlgCat.hom_id, AlgHom.id_apply, RingHom.id_apply]

/-- Successive reductions compose on both chambers and on the localized overlap. -/
theorem gluingCospanReduction_comp {k l m : ℕ} (hl : l ≤ k) (hm : m ≤ l) :
    gluingCospanReduction K hl ≫ gluingCospanReduction K hm =
      gluingCospanReduction K (hm.trans hl) := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _)
  · apply AlgCat.hom_ext
    apply AlgHom.toRingHom_injective
    apply localizedOverlap_ringHom_ext
    intro z
    simp only [AlgHom.coe_toRingHom, NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply]
    rw [gluingCospanReduction_app_one_rightGluing, gluingCospanReduction_app_one_rightGluing,
      gluingCospanReduction_app_one_rightGluing]
    exact congrArg (rightGluing (C (τ(m))) (1 + T 1) m)
      (RingHom.congr_fun (truncatedExponentChamberMap_comp (RingHom.id K) hl 0
        (RingHom.id K) hm) _)
  · apply AlgCat.hom_ext
    apply AlgHom.ext
    intro z
    simp only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      gluingCospanReduction_app_left]
    exact RingHom.congr_fun
      (truncatedExponentChamberMap_comp (RingHom.id K) hl 1 (RingHom.id K) hm) z
  · apply AlgCat.hom_ext
    apply AlgHom.ext
    intro z
    simp only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      gluingCospanReduction_app_right]
    exact RingHom.congr_fun
      (truncatedExponentChamberMap_comp (RingHom.id K) hl 0 (RingHom.id K) hm) z

/-- The gluing cospans form a tower in `K`-algebra diagrams. -/
abbrev gluingCospanTower : ℕᵒᵖ ⥤ (WalkingCospan ⥤ AlgCat K) where
  obj k := gluingCospan K k.unop
  map f := gluingCospanReduction K (leOfHom f.unop)
  map_id k := gluingCospanReduction_refl K k.unop
  map_comp f g := (gluingCospanReduction_comp K (leOfHom f.unop) (leOfHom g.unop)).symm

/-- Evaluation of the tower at an order recovers its gluing cospan. -/
@[simp]
theorem gluingCospanTower_obj (k : ℕᵒᵖ) :
    (gluingCospanTower K).obj k = gluingCospan K k.unop := (rfl)

/-- Every arrow of the tower is the prescribed cutoff reduction. -/
@[simp]
theorem gluingCospanTower_map {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (gluingCospanTower K).map f = gluingCospanReduction K (leOfHom f.unop) := (rfl)

/-- The existing slab projections give a cone on the gluing cospan. -/
abbrev slabCone (k : ℕ) : Cone (gluingCospan K k) :=
  Mei.NodeAlgebra.slabCone K (C (τ(k))) (1 + T 1) k

/-- The cone point is the original fiber-product slab, with its original `K`-action. -/
@[simp]
theorem slabCone_pt (k : ℕ) : (slabCone K k).pt = AlgCat.of K A(k) := (rfl)

/-- Matching chamber coefficients are precisely the elements of the slab algebra. -/
def slabConeIsLimit (k : ℕ) : IsLimit (slabCone K k) :=
  Mei.NodeAlgebra.slabConeIsLimit K (C (τ(k))) (1 + T 1) k

/-- The categorical matching algebra is canonically the existing slab algebra. -/
def slabLimitIso (k : ℕ) : AlgCat.of K A(k) ≅ limit (gluingCospan K k) :=
  Mei.NodeAlgebra.slabLimitIso K (C (τ(k))) (1 + T 1) k

/-- The comparison to the chosen categorical limit preserves every evaluation. -/
@[reassoc (attr := simp)]
theorem slabLimitIso_hom_π (k : ℕ) (j : WalkingCospan) :
    (slabLimitIso K k).hom ≫ limit.π (gluingCospan K k) j =
      (slabCone K k).π.app j :=
  Mei.NodeAlgebra.slabLimitIso_hom_π K (C (τ(k))) (1 + T 1) k j

/-- The inverse comparison also preserves every evaluation. -/
@[reassoc (attr := simp↓)]
theorem slabLimitIso_inv_π (k : ℕ) (j : WalkingCospan) :
    (slabLimitIso K k).inv ≫ (slabCone K k).π.app j =
      limit.π (gluingCospan K k) j :=
  Mei.NodeAlgebra.slabLimitIso_inv_π K (C (τ(k))) (1 + T 1) k j

/-- Categorical reduction of matching coefficients is the existing slab reduction. -/
@[simp↓]
theorem slabConeIsLimit_map_apply {k l : ℕ} (hl : l ≤ k) (z : A(k)) :
    ((slabConeIsLimit K l).map (slabCone K k) (gluingCospanReduction K hl)).hom z =
      truncatedSlabMap (RingHom.id K) hl z := by
  apply Subtype.ext
  apply Prod.ext
  · have h := AlgHom.congr_fun (congrArg AlgCat.Hom.hom
      (IsLimit.map_π (slabCone K k) (slabConeIsLimit K l) (gluingCospanReduction K hl) .left)) z
    simpa only [AlgCat.hom_comp, AlgHom.comp_apply,
      Mei.NodeAlgebra.slabCone_π_left K (C (τ(l))) (1 + T 1) l,
      Mei.NodeAlgebra.slabCone_π_left K (C (τ(k))) (1 + T 1) k,
      truncatedSlabMap_fst, gluingCospanReduction_app_left] using h
  · have h := AlgHom.congr_fun (congrArg AlgCat.Hom.hom
      (IsLimit.map_π (slabCone K k) (slabConeIsLimit K l) (gluingCospanReduction K hl) .right)) z
    simpa only [AlgCat.hom_comp, AlgHom.comp_apply,
      Mei.NodeAlgebra.slabCone_π_right K (C (τ(l))) (1 + T 1) l,
      Mei.NodeAlgebra.slabCone_π_right K (C (τ(k))) (1 + T 1) k,
      truncatedSlabMap_snd, gluingCospanReduction_app_right] using h

/-- The slab-to-limit comparison is natural under every cutoff reduction. -/
@[reassoc]
theorem slabLimitIso_hom_limMap {k l : ℕ} (hl : l ≤ k) :
    (slabLimitIso K k).hom ≫ limMap (gluingCospanReduction K hl) =
      (slabConeIsLimit K l).map (slabCone K k) (gluingCospanReduction K hl) ≫
        (slabLimitIso K l).hom := by
  apply limit.hom_ext
  intro j
  simp only [Category.assoc, limMap_π, slabLimitIso_hom_π_assoc, slabLimitIso_hom_π,
    IsLimit.map_π]

/-- On actual slab elements, the naturality square uses the original reduction,
including elements annihilated at the lower order. -/
@[simp]
theorem slabLimitIso_hom_limMap_apply {k l : ℕ} (hl : l ≤ k) (z : A(k)) :
    (limMap (gluingCospanReduction K hl)).hom ((slabLimitIso K k).hom.hom z) =
      (slabLimitIso K l).hom.hom (truncatedSlabMap (RingHom.id K) hl z) := by
  have h := AlgHom.congr_fun (congrArg AlgCat.Hom.hom (slabLimitIso_hom_limMap K hl)) z
  simpa only [AlgCat.hom_comp, AlgHom.comp_apply, slabConeIsLimit_map_apply K hl] using h

end Mei.FocusFocus
