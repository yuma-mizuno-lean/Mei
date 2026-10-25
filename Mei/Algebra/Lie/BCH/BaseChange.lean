/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion
public import Mei.Algebra.Lie.BaseChange
public import Mei.Algebra.Lie.Graded.BaseChange

/-!
# Completed scalar extension of BCH groups

Completed scalar extension is the inverse limit of the BCH groups of the scalar
extensions of the finite Lie quotients. It agrees with the completed BCH group
of the extended graded Lie algebra. In particular, scalar extension takes place
before the inverse limit; no commutation of tensor products with infinite limits
is asserted. The comparison preserves filtration orders and convergent ordered
products. Neither flatness nor freeness is required.

The comparison uses `Mei.PositiveDegrees.truncatedBaseChangeEquiv`, based on
Tau Ceti's `LieIdeal.quotientBaseChangeEquiv`, and the compatible-family maps
`Mei.CompletedGroup.mapEquiv`. Rational scalars act on the left tensor factor,
retaining the existing tensor-product module structure.
-/

public section

noncomputable section

open CategoryTheory Opposite TensorProduct

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (S : Type*) [CommRing S] [Algebra R S] [Algebra ℚ S]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The tower obtained by extending each finite Lie quotient and then applying BCH. -/
-- Tower objects must compute to expose their concrete tensor-product coordinates.
@[expose]
def baseChangeGroupTower : ℕᵒᵖ ⥤ GrpCat where
  obj k := GrpCat.of (BCHGroup (S ⊗[R] d.truncatedLie ℒ k.unop))
  map f := GrpCat.ofHom (LieHom.baseChange S
    (d.truncationMap ℒ (leOfHom f.unop))).bchGroupMap
  map_id k := by
    apply GrpCat.hom_ext
    simp
  map_comp f g := by
    apply GrpCat.hom_ext
    simp only [GrpCat.hom_comp, GrpCat.hom_ofHom, ← LieHom.bchGroupMap_comp,
      ← LieHom.baseChange_comp, truncationMap_comp]

/-- The transitions are the BCH maps of the extended quotient transitions. -/
@[simp]
theorem baseChangeGroupTower_map_hom {k l : ℕᵒᵖ} (f : k ⟶ l) :
    ((d.baseChangeGroupTower S ℒ).map f).hom =
      (LieHom.baseChange S (d.truncationMap ℒ (leOfHom f.unop))).bchGroupMap := (rfl)

/-- Extending the finite quotients gives a tower isomorphic to the degree tower
of the extended graded Lie algebra. -/
def baseChangeGroupTowerIso :
    d.groupTower (fun n => (ℒ n).baseChange S) ≅ d.baseChangeGroupTower S ℒ :=
  NatIso.ofComponents (fun k =>
    { hom := GrpCat.ofHom (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).toLieHom.bchGroupMap
      inv := GrpCat.ofHom (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).symm.toLieHom.bchGroupMap
      hom_inv_id := by
        apply GrpCat.hom_ext
        -- The functor objects hide the concrete group types at categorical composition.
        change (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).symm.toLieHom.bchGroupMap.comp
            (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).toLieHom.bchGroupMap = MonoidHom.id _
        rw [← LieHom.bchGroupMap_comp]
        have he : (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).symm.toLieHom.comp
            (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).toLieHom = LieHom.id := by
          apply LieHom.ext
          intro x
          exact (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).symm_apply_apply x
        rw [he, LieHom.bchGroupMap_id]
      inv_hom_id := by
        apply GrpCat.hom_ext
        -- The functor objects hide the concrete group types at categorical composition.
        change (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).toLieHom.bchGroupMap.comp
            (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).symm.toLieHom.bchGroupMap =
              MonoidHom.id _
        rw [← LieHom.bchGroupMap_comp]
        have he : (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).toLieHom.comp
            (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).symm.toLieHom = LieHom.id := by
          apply LieHom.ext
          intro x
          exact (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).apply_symm_apply x
        rw [he, LieHom.bchGroupMap_id] }) (by
    intro k l f
    apply GrpCat.hom_ext
    -- Categorical composition hides the concrete BCH quotient and tensor maps.
    change (d.truncatedBaseChangeEquiv (S := S) ℒ l.unop).toLieHom.bchGroupMap.comp
        (d.truncationMap (fun n => (ℒ n).baseChange S) (leOfHom f.unop)).bchGroupMap =
      (LieHom.baseChange S (d.truncationMap ℒ (leOfHom f.unop))).bchGroupMap.comp
        (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).toLieHom.bchGroupMap
    simp only [← LieHom.bchGroupMap_comp]
    congr 1
    apply LieHom.ext
    intro x
    exact d.truncatedBaseChangeEquiv_truncationMap ℒ (leOfHom f.unop) x)

/-- The finite-order comparison is extension of the Lie quotient equivalence in
exponential coordinates. -/
@[simp]
theorem baseChangeGroupTowerIso_hom_app (k : ℕᵒᵖ) :
    ((d.baseChangeGroupTowerIso S ℒ).hom.app k).hom =
      (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).toLieHom.bchGroupMap := (rfl)

/-- The inverse finite-order comparison uses the inverse Lie quotient equivalence. -/
@[simp]
theorem baseChangeGroupTowerIso_inv_app (k : ℕᵒᵖ) :
    ((d.baseChangeGroupTowerIso S ℒ).inv.app k).hom =
      (d.truncatedBaseChangeEquiv (S := S) ℒ k.unop).symm.toLieHom.bchGroupMap := (rfl)

-- The explicit identity comparison keeps the reindexed functor type in the term,
-- rather than relying on definitional equality when rewriting completion maps.
private def baseChangeTowerMap :
    (OrderHom.id : ℕ →o ℕ).toFunctor.op ⋙
      d.groupTower (fun n => (ℒ n).baseChange S) ⟶ d.baseChangeGroupTower S ℒ :=
  eqToHom (by rfl) ≫ (d.baseChangeGroupTowerIso S ℒ).hom

private def baseChangeTowerInv :
    (OrderHom.id : ℕ →o ℕ).toFunctor.op ⋙ d.baseChangeGroupTower S ℒ ⟶
      d.groupTower (fun n => (ℒ n).baseChange S) :=
  eqToHom (by rfl) ≫ (d.baseChangeGroupTowerIso S ℒ).inv

/-- Completed scalar extension: extend each finite Lie quotient, then take the
inverse limit of its BCH groups. -/
abbrev completedBCHBaseChange := completedGroup (d.baseChangeGroupTower S ℒ)

/-- Completing after extending the graded Lie algebra agrees with completed
scalar extension formed from its finite quotients. -/
def completedBCHBaseChangeEquiv :
    d.completedBCHGroup (fun n => (ℒ n).baseChange S) ≃* d.completedBCHBaseChange S ℒ :=
  CompletedGroup.mapEquiv OrderHom.id OrderHom.id
    (baseChangeTowerMap S d ℒ) (baseChangeTowerInv S d ℒ)
    (fun k => ⟨k, le_rfl, le_rfl, by
      have he := NatTrans.congr_app (d.baseChangeGroupTowerIso S ℒ).hom_inv_id (op k)
      simp only [NatTrans.comp_app, NatTrans.id_app] at he
      exact (congrArg (fun f => (d.groupTower (fun n => (ℒ n).baseChange S)).map
        (homOfLE (le_refl k)).op ≫ f) he).trans (Category.comp_id _)⟩)
    (fun k => ⟨k, le_rfl, le_rfl, by
      have he := NatTrans.congr_app (d.baseChangeGroupTowerIso S ℒ).inv_hom_id (op k)
      simp only [NatTrans.comp_app, NatTrans.id_app] at he
      exact (congrArg (fun f => (d.baseChangeGroupTower S ℒ).map
        (homOfLE (le_refl k)).op ≫ f) he).trans (Category.comp_id _)⟩)

/-- Projection of the comparison applies the finite quotient comparison at the
same order. -/
@[simp]
theorem projection_completedBCHBaseChangeEquiv (k : ℕ)
    (x : d.completedBCHGroup (fun n => (ℒ n).baseChange S)) :
    CompletedGroup.projection k (d.completedBCHBaseChangeEquiv S ℒ x) =
      (d.truncatedBaseChangeEquiv (S := S) ℒ k).toLieHom.bchGroupMap
        (CompletedGroup.projection k x) := by
  rw [completedBCHBaseChangeEquiv, CompletedGroup.mapEquiv_apply,
    CompletedGroup.projection_map]
  rfl

/-- Projection of the inverse comparison uses the inverse finite quotient map. -/
@[simp]
theorem projection_completedBCHBaseChangeEquiv_symm (k : ℕ)
    (x : d.completedBCHBaseChange S ℒ) :
    CompletedGroup.projection k ((d.completedBCHBaseChangeEquiv S ℒ).symm x) =
      (d.truncatedBaseChangeEquiv (S := S) ℒ k).symm.toLieHom.bchGroupMap
        (CompletedGroup.projection k x) := by
  rw [completedBCHBaseChangeEquiv, CompletedGroup.mapEquiv_symm_apply,
    CompletedGroup.projection_map]
  rfl

/-- Completed scalar extension preserves and reflects every filtration order. -/
@[simp]
theorem completedBCHBaseChangeEquiv_mem_degreeFiltration (a : ℕ)
    (x : d.completedBCHGroup (fun n => (ℒ n).baseChange S)) :
    d.completedBCHBaseChangeEquiv S ℒ x ∈
        CompletedGroup.degreeFiltration (d.baseChangeGroupTower S ℒ) a ↔
      x ∈ CompletedGroup.degreeFiltration
        (d.groupTower (fun n => (ℒ n).baseChange S)) a := by
  cases a with
  | zero => simp
  | succ k =>
    simp only [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker,
      projection_completedBCHBaseChangeEquiv]
    have h (y : BCHGroup (d.truncatedLie (fun n => (ℒ n).baseChange S) k)) :
        (d.truncatedBaseChangeEquiv (S := S) ℒ k).toLieHom.bchGroupMap y = 1 ↔ y = 1 := by
      constructor
      · intro hy
        apply BCHGroup.log_injective
        apply (d.truncatedBaseChangeEquiv (S := S) ℒ k).injective
        simpa using congrArg BCHGroup.log hy
      · rintro rfl
        exact map_one _
    exact h (CompletedGroup.projection k x)

variable {ι : Type*}

/-- A family has finite support at every order before the comparison exactly
when it does afterwards. -/
@[simp]
theorem hasFiniteSupport_completedBCHBaseChangeEquiv_iff
    (x : ι → d.completedBCHGroup (fun n => (ℒ n).baseChange S)) :
    CompletedGroup.HasFiniteSupport (fun i => d.completedBCHBaseChangeEquiv S ℒ (x i)) ↔
      CompletedGroup.HasFiniteSupport x := by
  constructor
  · intro hx
    have h : CompletedGroup.HasFiniteSupport (fun i =>
        (d.completedBCHBaseChangeEquiv S ℒ).symm (d.completedBCHBaseChangeEquiv S ℒ (x i))) := by
      simpa only [completedBCHBaseChangeEquiv, CompletedGroup.mapEquiv_symm_apply] using
        hx.map OrderHom.id (baseChangeTowerInv S d ℒ)
    simpa only [MulEquiv.symm_apply_apply] using h
  · intro hx
    simpa only [completedBCHBaseChangeEquiv, CompletedGroup.mapEquiv_apply] using
      hx.map OrderHom.id (baseChangeTowerMap S d ℒ)

/-- The completed scalar-extension comparison preserves convergent products
with the smallest index leftmost. -/
@[simp]
theorem completedBCHBaseChangeEquiv_orderedProd [LinearOrder ι]
    (x : ι → d.completedBCHGroup (fun n => (ℒ n).baseChange S))
    (hx : CompletedGroup.HasFiniteSupport x) :
    d.completedBCHBaseChangeEquiv S ℒ (CompletedGroup.orderedProd x hx) =
      CompletedGroup.orderedProd (fun i => d.completedBCHBaseChangeEquiv S ℒ (x i))
        ((d.hasFiniteSupport_completedBCHBaseChangeEquiv_iff S ℒ x).mpr hx) := by
  simpa only [completedBCHBaseChangeEquiv, CompletedGroup.mapEquiv_apply] using
    CompletedGroup.map_orderedProd OrderHom.id (baseChangeTowerMap S d ℒ) x hx

end Mei.PositiveDegrees
