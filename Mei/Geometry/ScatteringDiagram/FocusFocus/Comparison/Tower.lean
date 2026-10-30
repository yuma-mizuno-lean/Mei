/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison.Diagram

/-!
# The chamber-to-Laurent comparison through all cutoffs

The Laurent slab incidence diagrams form a tower over the original coefficient
ring. Their reductions apply the truncated-parameter map to Laurent coefficients
and to the nodal slab, retaining both Laurent exponents. The faithful chamber
realizations and inverse slab dictionary give a natural transformation from the
nodal incidence tower to this Laurent tower. Thus a compatible family of chamber
and face coefficients remains compatible after Laurent realization.

We use `chamberLaurentIncidenceComparison`, its coefficient reduction squares,
`slabIncidenceTower`, and Mathlib's `spanHomMk`. The nodal model follows
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial

variable (K : Type*) [CommRing K]

local notation "S(" k ")" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ(" k ")" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "e(" k ")" => algebraEquiv (τ(k)) k (AdjoinRoot.root_X_pow_pow (k + 1))

local instance (k : ℕ) : IsScalarTower K (S(k)) (SlabNode (τ(k))) :=
  IsScalarTower.to₁₂₄ K (S(k)) (S(k))[ℤ] _

private abbrev coefficientReduction {k l : ℕ} (hl : l ≤ k) :
    (S(k))[ℤ × ℤ] →ₐ[K] (S(l))[ℤ × ℤ] :=
  mapAlgHom (ℤ × ℤ) (AdjoinRoot.mapAlgHom (AlgHom.id K K) _ _
    (by simpa using pow_dvd_pow (Polynomial.X : Polynomial K) (Nat.add_le_add_right hl 1)))

/-- Cutoff reduction of the Laurent slab span. The face map is transported by
the slab dictionary and the chamber maps reduce coefficients. -/
def laurentSlabIncidenceReduction {k l : ℕ} (hl : l ≤ k) :
    laurentSlabIncidence K k ⟶ laurentSlabIncidence K l :=
  spanHomMk
    (AlgCat.ofHom ((e(k)).toAlgHom.restrictScalars K) ≫
      (slabIncidenceReduction K hl).app .zero ≫
      (chamberLaurentIncidenceComparison K l).app .zero)
    (AlgCat.ofHom (coefficientReduction K hl))
    (AlgCat.ofHom (coefficientReduction K hl))
    (by
      apply AlgCat.hom_ext
      apply AlgHom.ext
      intro z
      have h := NatTrans.naturality (chamberLaurentIncidenceComparison K k)
        WalkingSpan.Hom.fst
      have h' := NatTrans.naturality (chamberLaurentIncidenceComparison K l)
        WalkingSpan.Hom.fst
      have hr := NatTrans.naturality (slabIncidenceReduction K hl) WalkingSpan.Hom.fst
      have hv := congrArg (fun f => f.hom ((e(k)) z)) h
      have hv' := congrArg (fun f => f.hom
        (((slabIncidenceReduction K hl).app .zero).hom ((e(k)) z))) h'
      have hvr := congrArg (fun f => f.hom ((e(k)) z)) hr
      have hcoeff (a : TruncatedExponentChamber K k 1) :
          coefficientReduction K hl (leftChamberExponentMap K k a) =
            leftChamberExponentMap K l
              (((slabIncidenceReduction K hl).app .left).hom a) := by
        simpa only [slabIncidenceReduction_app_left, coefficientReduction,
          ← AlgHom.coe_toRingHom, toRingHom_mapAlgHom, AdjoinRoot.mapAlgHom,
          AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom] using
          (leftChamberExponentMap_truncatedExponentChamberMap (RingHom.id K) hl a).symm
      simp only [AlgCat.hom_comp, AlgHom.comp_apply,
        chamberLaurentIncidenceComparison_app_zero,
        chamberLaurentIncidenceComparison_app_left, AlgEquiv.symm_apply_apply] at hv hv'
      simp only [AlgCat.hom_comp, AlgHom.comp_apply] at hvr
      simpa only [AlgCat.hom_comp, AlgHom.comp_apply, AlgCat.hom_ofHom,
        AlgHom.restrictScalars_apply, AlgEquiv.toAlgHom_apply,
        chamberLaurentIncidenceComparison_app_zero] using
        (hv'.symm.trans ((congrArg (leftChamberExponentMap K l) hvr.symm).trans
          ((hcoeff _).symm.trans
            (congrArg (coefficientReduction K hl) hv)))).symm)
    (by
      apply AlgCat.hom_ext
      apply AlgHom.ext
      intro z
      have h := NatTrans.naturality (chamberLaurentIncidenceComparison K k)
        WalkingSpan.Hom.snd
      have h' := NatTrans.naturality (chamberLaurentIncidenceComparison K l)
        WalkingSpan.Hom.snd
      have hr := NatTrans.naturality (slabIncidenceReduction K hl) WalkingSpan.Hom.snd
      have hv := congrArg (fun f => f.hom ((e(k)) z)) h
      have hv' := congrArg (fun f => f.hom
        (((slabIncidenceReduction K hl).app .zero).hom ((e(k)) z))) h'
      have hvr := congrArg (fun f => f.hom ((e(k)) z)) hr
      have hcoeff (a : TruncatedExponentChamber K k 0) :
          coefficientReduction K hl (rightChamberExponentMap K k a) =
            rightChamberExponentMap K l
              (((slabIncidenceReduction K hl).app .right).hom a) := by
        simpa only [slabIncidenceReduction_app_right, coefficientReduction,
          ← AlgHom.coe_toRingHom, toRingHom_mapAlgHom, AdjoinRoot.mapAlgHom,
          AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom] using
          (rightChamberExponentMap_truncatedExponentChamberMap (RingHom.id K) hl a).symm
      simp only [AlgCat.hom_comp, AlgHom.comp_apply,
        chamberLaurentIncidenceComparison_app_zero,
        chamberLaurentIncidenceComparison_app_right, AlgEquiv.symm_apply_apply] at hv hv'
      simp only [AlgCat.hom_comp, AlgHom.comp_apply] at hvr
      simpa only [AlgCat.hom_comp, AlgHom.comp_apply, AlgCat.hom_ofHom,
        AlgHom.restrictScalars_apply, AlgEquiv.toAlgHom_apply,
        chamberLaurentIncidenceComparison_app_zero] using
        (hv'.symm.trans ((congrArg (rightChamberExponentMap K l) hvr.symm).trans
          ((hcoeff _).symm.trans
            (congrArg (coefficientReduction K hl) hv)))).symm)

/-- The face reduction is the canonical reduction in nodal coordinates. -/
@[simp↓]
theorem laurentSlabIncidenceReduction_app_zero {k l : ℕ} (hl : l ≤ k)
    (z : SlabNode (τ(k))) :
    ((laurentSlabIncidenceReduction K hl).app .zero).hom z =
      (e(l)).symm (truncatedSlabMap (RingHom.id K) hl ((e(k)) z)) := by
  simpa only [laurentSlabIncidenceReduction, spanHomMk, AlgCat.hom_comp,
    AlgCat.hom_ofHom, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    AlgEquiv.toAlgHom_apply, chamberLaurentIncidenceComparison_app_zero] using
    congrArg (e(l)).symm (slabIncidenceReduction_app_zero K hl ((e(k)) z))

/-- The left Laurent map reduces coefficients and fixes both exponents. -/
@[simp↓]
theorem laurentSlabIncidenceReduction_app_left {k l : ℕ} (hl : l ≤ k)
    (z : (S(k))[ℤ × ℤ]) :
    ((laurentSlabIncidenceReduction K hl).app .left).hom z =
      mapRingHom (ℤ × ℤ) (AdjoinRoot.map (RingHom.id K) _ _ (by
        simpa using pow_dvd_pow (Polynomial.X : Polynomial K) (Nat.add_le_add_right hl 1))) z :=
  (rfl)

/-- The right Laurent map has the same coefficientwise formula. -/
@[simp↓]
theorem laurentSlabIncidenceReduction_app_right {k l : ℕ} (hl : l ≤ k)
    (z : (S(k))[ℤ × ℤ]) :
    ((laurentSlabIncidenceReduction K hl).app .right).hom z =
      mapRingHom (ℤ × ℤ) (AdjoinRoot.map (RingHom.id K) _ _ (by
        simpa using pow_dvd_pow (Polynomial.X : Polynomial K) (Nat.add_le_add_right hl 1))) z :=
  (rfl)

/-- Underthe slab dictionary the transported face map is the usual nodal
coefficient map, fixing both node coordinates. -/
theorem laurentSlabIncidenceReduction_app_zero_eq_mapOfEq {k l : ℕ} (hl : l ≤ k)
    (z : SlabNode (τ(k))) :
    ((laurentSlabIncidenceReduction K hl).app .zero).hom z =
      (letI : Algebra (S(k))[ℤ] (S(l))[ℤ] :=
        (Mei.LaurentPolynomial.truncatedScalarMap (RingHom.id K) hl).toAlgebra
       mapOfEq (C (τ(k)) * (1 + T 1))
         (by simp [RingHom.algebraMap_toAlgebra]) z) := by
  rw [laurentSlabIncidenceReduction_app_zero]
  simpa only [AlgEquiv.symm_apply_apply] using
    algebraEquiv_symm_truncatedSlabMap (RingHom.id K) hl ((e(k)) z)

/-- Realizing chambers in Laurent coordinates commutes with cutoff reduction
on every object of the incidence diagram. -/
@[reassoc (attr := simp)]
theorem chamberLaurentIncidenceComparison_reduction {k l : ℕ} (hl : l ≤ k) :
    chamberLaurentIncidenceComparison K k ≫ laurentSlabIncidenceReduction K hl =
      slabIncidenceReduction K hl ≫ chamberLaurentIncidenceComparison K l := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _) <;> apply AlgCat.hom_ext <;> apply AlgHom.ext <;> intro z
  · simp only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      chamberLaurentIncidenceComparison_app_zero, laurentSlabIncidenceReduction_app_zero,
      AlgEquiv.apply_symm_apply, slabIncidenceReduction_app_zero]
  · simpa only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      chamberLaurentIncidenceComparison_app_left,
      laurentSlabIncidenceReduction_app_left, slabIncidenceReduction_app_left] using
      (leftChamberExponentMap_truncatedExponentChamberMap (RingHom.id K) hl z).symm
  · simpa only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      chamberLaurentIncidenceComparison_app_right,
      laurentSlabIncidenceReduction_app_right, slabIncidenceReduction_app_right] using
      (rightChamberExponentMap_truncatedExponentChamberMap (RingHom.id K) hl z).symm

/-- Reducing to the same cutoff fixes every Laurent incidence coefficient. -/
@[simp]
theorem laurentSlabIncidenceReduction_refl (k : ℕ) :
    laurentSlabIncidenceReduction K (k := k) le_rfl = 𝟙 _ := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _) <;> apply AlgCat.hom_ext <;> apply AlgHom.ext <;> intro z
  · simp only [laurentSlabIncidenceReduction_app_zero, truncatedSlabMap_id,
      RingHom.id_apply, AlgEquiv.symm_apply_apply, NatTrans.id_app,
      AlgCat.hom_id, AlgHom.id_apply]
  all_goals
    simp only [laurentSlabIncidenceReduction_app_left,
      laurentSlabIncidenceReduction_app_right, NatTrans.id_app, AlgCat.hom_id,
      AlgHom.id_apply]
    have hid : AdjoinRoot.map (RingHom.id K) (Polynomial.X ^ (k + 1))
        (Polynomial.X ^ (k + 1)) (by simp) = RingHom.id _ := by
      ext <;> simp
    rw [hid, mapRingHom_id, RingHom.id_apply]

/-- Successive reductions compose, including the slab face and both Laurent
chambers. -/
theorem laurentSlabIncidenceReduction_comp {k l m : ℕ} (hl : l ≤ k) (hm : m ≤ l) :
    laurentSlabIncidenceReduction K hl ≫ laurentSlabIncidenceReduction K hm =
      laurentSlabIncidenceReduction K (hm.trans hl) := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _) <;> apply AlgCat.hom_ext <;> apply AlgHom.ext <;> intro z
  · simp only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      laurentSlabIncidenceReduction_app_zero, AlgEquiv.apply_symm_apply]
    congr 1
    exact RingHom.congr_fun
      (truncatedSlabMap_comp (RingHom.id K) hl (RingHom.id K) hm) _
  all_goals
    simp only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      laurentSlabIncidenceReduction_app_left, laurentSlabIncidenceReduction_app_right]
    rw [← RingHom.comp_apply, ← mapRingHom_comp]
    congr 2
    ext <;> simp

/-- The full-exponent Laurent slab diagrams form a tower over the original
coefficient ring. -/
abbrev laurentSlabIncidenceTower : ℕᵒᵖ ⥤ (WalkingSpan ⥤ AlgCat K) where
  obj k := laurentSlabIncidence K k.unop
  map f := laurentSlabIncidenceReduction K (leOfHom f.unop)
  map_id k := laurentSlabIncidenceReduction_refl K k.unop
  map_comp f g := (laurentSlabIncidenceReduction_comp K
    (leOfHom f.unop) (leOfHom g.unop)).symm

/-- Tower arrows are the actual coefficient reductions of the Laurent spans. -/
@[simp]
theorem laurentSlabIncidenceTower_map {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (laurentSlabIncidenceTower K).map f =
      laurentSlabIncidenceReduction K (leOfHom f.unop) := (rfl)

/-- The inverse slab dictionary and faithful chamber embeddings compare the
entire coefficient towers, retaining compatibility through all cutoffs. -/
def chamberLaurentIncidenceTowerComparison :
    slabIncidenceTower K ⟶ laurentSlabIncidenceTower K where
  app k := chamberLaurentIncidenceComparison K k.unop
  naturality _ _ f := (chamberLaurentIncidenceComparison_reduction K (leOfHom f.unop)).symm

/-- At every cutoff the tower comparison is the original comparison of spans. -/
@[simp]
theorem chamberLaurentIncidenceTowerComparison_app (k : ℕᵒᵖ) :
    (chamberLaurentIncidenceTowerComparison K).app k =
      chamberLaurentIncidenceComparison K k.unop := (rfl)

end Mei.FocusFocus
