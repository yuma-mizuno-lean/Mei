/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion
public import Mei.Algebra.Lie.Graded.RestrictScalars

/-!
# Scalar restriction of completed BCH groups

Restricting scalars in a positive Lie grading preserves its completed BCH group.
The comparison sends the exponential of a quotient representative to the exponential
of that same representative at every order. It commutes with graded Lie maps,
including maps that regrade and change the cutoff, and identifies the degree
filtrations and convergent ordered products.

The finite comparisons use `TauCeti.PositiveDegrees.truncatedRestrictScalarsEquiv`
and `LieEquiv.bchGroupEquiv`. Their inverse limit uses
`TauCeti.CompletedGroup.mapEquiv`, on the compatible-family carrier coming from
Mathlib's `GrpCat.sectionsSubgroup`. No freeness, flatness or nilpotence of the
original Lie algebra is needed.
-/

public section

open TauCeti.CompletedGroup (projection)

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading GradedLieHom)

noncomputable section

open CategoryTheory Opposite

namespace TauCeti.PositiveDegrees

open Mei

variable {N R S L : Type*} [AddCommMonoid N] [DecidableEq N]
  [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S] [SMul R S]
  [LieRing L] [LieAlgebra S L] [LieAlgebra R L] [LieAlgebra ℚ L]
  [IsScalarTower R S L] [IsScalarTower ℚ R L] [IsScalarTower ℚ S L]
  (d : PositiveDegrees N) (ℒ : N → Submodule S L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Scalar restriction identifies the finite BCH towers at the same cutoff. -/
def groupTowerRestrictScalarsIso :
    d.groupTower (fun n => (ℒ n).restrictScalars R) ≅ d.groupTower ℒ :=
  NatIso.ofComponents
    (fun k => (d.truncatedRestrictScalarsEquiv (R := R) ℒ k.unop).bchGroupEquiv.toGrpIso)
    (by
      intro k l f
      apply GrpCat.hom_ext
      -- Categorical composition conceals the concrete BCH quotient homomorphisms.
      change
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ l.unop).bchGroupEquiv.toMonoidHom.comp
            (d.truncationMap (fun n => (ℒ n).restrictScalars R)
              (leOfHom f.unop)).bchGroupMap =
          (d.truncationMap ℒ (leOfHom f.unop)).bchGroupMap.comp
            (d.truncatedRestrictScalarsEquiv (R := R) ℒ k.unop).bchGroupEquiv.toMonoidHom
      rw [← LieHom.bchGroupMap_restrictScalars (R := R)
        (d.truncationMap ℒ (leOfHom f.unop))]
      simp only [MulEquiv.toMonoidHom_eq_coe, LieEquiv.coe_bchGroupEquiv, ← LieHom.bchGroupMap_comp]
      congr 1
      simpa only [truncationMap_eq_factor] using
        d.truncatedRestrictScalarsEquiv_comp_truncationMap (R := R) ℒ (leOfHom f.unop))

/-- The tower comparison acts by the canonical finite Lie quotient comparison. -/
@[simp]
theorem groupTowerRestrictScalarsIso_hom_app_hom (k : ℕᵒᵖ) :
    ((d.groupTowerRestrictScalarsIso (R := R) ℒ).hom.app k).hom =
      (d.truncatedRestrictScalarsEquiv (R := R) ℒ k.unop).toLieHom.bchGroupMap := by
  -- The natural isomorphism wraps the multiplicative equivalence in a categorical isomorphism.
  change (d.truncatedRestrictScalarsEquiv (R := R) ℒ k.unop).bchGroupEquiv.toMonoidHom = _
  exact LieEquiv.coe_bchGroupEquiv _

/-- The inverse tower comparison acts by the inverse finite Lie quotient comparison. -/
@[simp]
theorem groupTowerRestrictScalarsIso_inv_app_exp (k : ℕᵒᵖ)
    (x : d.truncatedLie ℒ k.unop) :
    (d.groupTowerRestrictScalarsIso (R := R) ℒ).inv.app k (BCHGroup.exp x) =
      BCHGroup.exp ((d.truncatedRestrictScalarsEquiv (R := R) ℒ k.unop).symm x) := by
  exact (d.truncatedRestrictScalarsEquiv (R := R) ℒ k.unop).bchGroupEquiv_symm_exp x

/-- Restricting scalars preserves the completed BCH group, at every finite order. -/
def completedBCHRestrictScalarsEquiv :
    d.completedBCHGroup (fun n => (ℒ n).restrictScalars R) ≃* d.completedBCHGroup ℒ :=
  TauCeti.CompletedGroup.congr (d.groupTowerRestrictScalarsIso (R := R) ℒ)

/-- Projection computes scalar restriction by the finite Lie quotient comparison. -/
@[simp]
theorem projection_completedBCHRestrictScalarsEquiv (k : ℕ)
    (x : d.completedBCHGroup (fun n => (ℒ n).restrictScalars R)) :
    projection k (d.completedBCHRestrictScalarsEquiv (R := R) ℒ x) =
      (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.bchGroupMap
        (projection k x) := by
  rw [completedBCHRestrictScalarsEquiv, TauCeti.CompletedGroup.projection_congr]
  exact DFunLike.congr_fun (d.groupTowerRestrictScalarsIso_hom_app_hom (R := R) ℒ (op k))
    (projection k x)

/-- The inverse comparison also acts at the same finite cutoff. -/
@[simp]
theorem projection_completedBCHRestrictScalarsEquiv_symm (k : ℕ)
    (x : d.completedBCHGroup ℒ) :
    projection k ((d.completedBCHRestrictScalarsEquiv (R := R) ℒ).symm x) =
      BCHGroup.exp ((d.truncatedRestrictScalarsEquiv (R := R) ℒ k).symm
        (BCHGroup.log (projection k x))) := by
  rw [completedBCHRestrictScalarsEquiv, TauCeti.CompletedGroup.projection_congr_symm]
  conv_lhs => arg 2; rw [← BCHGroup.exp_log (projection k x)]
  exact d.groupTowerRestrictScalarsIso_inv_app_exp (R := R) ℒ _ _

/-- The comparison preserves and reflects triviality at every finite cutoff. -/
theorem projection_completedBCHRestrictScalarsEquiv_eq_one_iff (k : ℕ)
    (x : d.completedBCHGroup (fun n => (ℒ n).restrictScalars R)) :
    projection k (d.completedBCHRestrictScalarsEquiv (R := R) ℒ x) = 1 ↔
      projection k x = 1 := by
  rw [projection_completedBCHRestrictScalarsEquiv, ← LieEquiv.coe_bchGroupEquiv]
  exact (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).bchGroupEquiv.injective.eq_iff'
    (map_one _)

/-- At every finite cutoff, the finite comparison sends the projection of the inverse
comparison of `x` back to the projection of `x`. -/
theorem bchGroupEquiv_projection_completedBCHRestrictScalarsEquiv_symm (k : ℕ)
    (x : d.completedBCHGroup ℒ) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).bchGroupEquiv
        (projection k ((d.completedBCHRestrictScalarsEquiv (R := R) ℒ).symm x)) =
      projection k x := by
  have hx := d.projection_completedBCHRestrictScalarsEquiv (R := R) ℒ k
    ((d.completedBCHRestrictScalarsEquiv (R := R) ℒ).symm x)
  rw [MulEquiv.apply_symm_apply] at hx
  rw [hx, ← LieEquiv.coe_bchGroupEquiv, MonoidHom.coe_ofClass]

/-- The comparison identifies the two degree filtrations exactly. -/
@[simp]
theorem completedBCHRestrictScalarsEquiv_mem_degreeFiltration_iff (a : ℕ)
    (x : d.completedBCHGroup (fun n => (ℒ n).restrictScalars R)) :
    d.completedBCHRestrictScalarsEquiv (R := R) ℒ x ∈
        TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) a ↔
      x ∈ TauCeti.CompletedGroup.degreeFiltration
        (d.groupTower (fun n => (ℒ n).restrictScalars R)) a := by
  cases a with
  | zero => simp
  | succ k =>
    simp only [TauCeti.CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker,
      projection_completedBCHRestrictScalarsEquiv]
    have he := (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).bchGroupEquiv.injective
    rw [← LieEquiv.coe_bchGroupEquiv]
    exact he.eq_iff' (map_one _)

variable {ι : Type*}

/-- Scalar restriction preserves families with finite support in every truncation. -/
theorem hasFiniteSupport_completedBCHRestrictScalarsEquiv
    (x : ι → d.completedBCHGroup (fun n => (ℒ n).restrictScalars R))
    (hx : TauCeti.CompletedGroup.HasFiniteSupport x) :
    TauCeti.CompletedGroup.HasFiniteSupport (fun i => d.completedBCHRestrictScalarsEquiv (R := R) ℒ
      (x i)) := by
  simpa only [completedBCHRestrictScalarsEquiv, TauCeti.CompletedGroup.congr_apply] using
    hx.map OrderHom.id (d.groupTowerRestrictScalarsIso (R := R) ℒ).hom

/-- Scalar restriction commutes with ordered products that converge at every cutoff. -/
@[simp]
theorem completedBCHRestrictScalarsEquiv_orderedProd [LinearOrder ι]
    (x : ι → d.completedBCHGroup (fun n => (ℒ n).restrictScalars R))
    (hx : TauCeti.CompletedGroup.HasFiniteSupport x) :
    d.completedBCHRestrictScalarsEquiv (R := R) ℒ (TauCeti.CompletedGroup.orderedProd x hx) =
      TauCeti.CompletedGroup.orderedProd
        (fun i => d.completedBCHRestrictScalarsEquiv (R := R) ℒ (x i))
        (d.hasFiniteSupport_completedBCHRestrictScalarsEquiv ℒ x hx) := by
  simpa only [completedBCHRestrictScalarsEquiv, TauCeti.CompletedGroup.congr_apply] using
    TauCeti.CompletedGroup.map_orderedProd OrderHom.id
      (d.groupTowerRestrictScalarsIso (R := R) ℒ).hom x hx

end TauCeti.PositiveDegrees

universe u

namespace TauCeti.GradedLieHom

open Mei

variable {N M R S : Type*} {L L' : Type u} [AddCommMonoid N] [AddCommMonoid M]
  [DecidableEq N] [DecidableEq M]
  [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S] [SMul R S]
  [LieRing L] [LieAlgebra S L] [LieAlgebra R L] [LieAlgebra ℚ L]
  [IsScalarTower R S L] [IsScalarTower ℚ R L] [IsScalarTower ℚ S L]
  [LieRing L'] [LieAlgebra S L'] [LieAlgebra R L'] [LieAlgebra ℚ L']
  [IsScalarTower R S L'] [IsScalarTower ℚ R L'] [IsScalarTower ℚ S L']
  {d : PositiveDegrees N} {e : PositiveDegrees M} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule S L} {ℳ : M → Submodule S L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ]

/-- Completed graded maps commute with scalar restriction at their original cutoff moduli. -/
theorem completedMap_restrictScalars (f : GradedLieHom T ℒ ℳ) :
    (e.completedBCHRestrictScalarsEquiv (R := R) ℳ).toMonoidHom.comp
        (f.restrictScalars R).completedMap =
      f.completedMap.comp (d.completedBCHRestrictScalarsEquiv (R := R) ℒ).toMonoidHom := by
  ext x k
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv, projection_completedMap]
  have ht := congrArg (fun h => h.bchGroupMap) (f.truncatedMap_restrictScalars (R := R) k le_rfl)
  simp only [LieHom.bchGroupMap_comp, LieHom.bchGroupMap_restrictScalars] at ht
  exact DFunLike.congr_fun ht (projection (T.modulus k) x)

end TauCeti.GradedLieHom
