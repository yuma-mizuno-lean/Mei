/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion
public import Mei.Algebra.Lie.Graded.Completion
public import Mei.LinearAlgebra.ModuleFiltration.Map

/-!
# Exponential coordinates on completed BCH groups

Levelwise exponential and logarithm identify the compatible-family Lie completion
with the completed BCH group as sets. This comparison lets Lie maps out of the
completion describe group representations in exponential coordinates, without
requiring the original Lie algebra to be nilpotent.
In these coordinates, completed graded group maps agree with the linear maps
of module completions, retaining the prescribed cutoff modulus.

The carriers and transition laws are those of `LieIdeal.completion` and
`TauCeti.CompletedGroup`; the finite coordinate maps are `Mei.BCHGroup.exp` and
`Mei.BCHGroup.log`.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading GradedLieHom)

namespace TauCeti.PositiveDegrees

open Mei

open CategoryTheory Opposite

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "π" =>
  LieIdeal.completionProjection (d.truncationIdeal ℒ) (d.truncationIdeal_antitone ℒ)

/-- Levelwise exponential identifies the Lie and BCH group completions as sets. -/
noncomputable def completedBCHExp : d.completedLie ℒ ≃ d.completedBCHGroup ℒ where
  toFun x := ⟨fun k => BCHGroup.exp (π k x), (mem_completedGroup_iff _ _).mpr (by
    intro k l h
    -- The categorical tower map conceals the concrete BCH quotient homomorphism.
    change (d.lieTruncationMap ℒ h).bchGroupMap (BCHGroup.exp (π l x)) =
      BCHGroup.exp (π k x)
    rw [LieHom.bchGroupMap_exp, lieTruncationMap_def,
      LieIdeal.factor_completionProjection])⟩
  invFun g := ⟨fun k =>
    BCHGroup.log (L := d.lieTruncation ℒ k.unop) (TauCeti.CompletedGroup.projection k.unop g),
    (ModuleFiltration.mem_completionSubmodule_iff _ _).mpr (by
      intro k l h
      rw [LieIdeal.completionFiltration_transition, LieHom.coe_toLinearMap]
      have hg := congrArg (BCHGroup.log (L := d.lieTruncation ℒ k))
        (TauCeti.CompletedGroup.map_projection k l h g)
      -- Rewrite the categorical arrow at its concrete quotient group type.
      change BCHGroup.log (L := d.lieTruncation ℒ k) ((d.lieTruncationMap ℒ h).bchGroupMap
        (TauCeti.CompletedGroup.projection l g)) =
          BCHGroup.log (L := d.lieTruncation ℒ k) (TauCeti.CompletedGroup.projection k g) at hg
      simpa only [lieTruncationMap_def] using
        ((d.lieTruncationMap ℒ h).log_bchGroupMap (TauCeti.CompletedGroup.projection l g)).symm.trans hg)⟩
  left_inv x := by
    apply ModuleFiltration.completion_ext
    intro k
    simp only [ModuleFiltration.projection_mk, TauCeti.CompletedGroup.projection_apply,
      BCHGroup.log_exp, LieIdeal.completionProjection_apply]
  right_inv g := by
    apply TauCeti.CompletedGroup.ext
    intro k
    simp only [TauCeti.CompletedGroup.projection_apply, LieIdeal.completionProjection_apply,
      ModuleFiltration.projection_mk]
    exact BCHGroup.exp_log (L := d.lieTruncation ℒ k) (g.val k)

/-- Projection of the completed exponential is the finite exponential coordinate. -/
@[simp]
theorem projection_completedBCHExp (k : ℕ) (x : d.completedLie ℒ) :
    TauCeti.CompletedGroup.projection k (d.completedBCHExp ℒ x) = BCHGroup.exp (π k x) := by
  rw [TauCeti.CompletedGroup.projection_apply, completedBCHExp]
  rfl

/-- Projection of the inverse coordinate map is the logarithm at the same cutoff. -/
@[simp]
theorem completionProjection_completedBCHExp_symm (k : ℕ) (g : d.completedBCHGroup ℒ) :
    π k ((d.completedBCHExp ℒ).symm g) =
      BCHGroup.log (L := d.lieTruncation ℒ k) (TauCeti.CompletedGroup.projection k g) := by
  rw [LieIdeal.completionProjection_apply, completedBCHExp]
  exact ModuleFiltration.projection_mk _ _ _ k

/-- Zero is the exponential coordinate of the identity completed group element. -/
@[simp]
theorem completedBCHExp_zero : d.completedBCHExp ℒ 0 = 1 := by
  apply TauCeti.CompletedGroup.ext
  intro k
  rw [projection_completedBCHExp, map_zero, BCHGroup.exp_zero]
  exact ((TauCeti.CompletedGroup.projection (F := d.groupTower ℒ) k).map_one).symm

/-- Negation of a completed Lie coordinate gives inversion in the completed group. -/
@[simp]
theorem completedBCHExp_neg (x : d.completedLie ℒ) :
    d.completedBCHExp ℒ (-x) = (d.completedBCHExp ℒ x)⁻¹ := by
  apply TauCeti.CompletedGroup.ext
  intro k
  rw [projection_completedBCHExp, map_neg, BCHGroup.exp_neg]
  exact (congrArg Inv.inv (d.projection_completedBCHExp ℒ k x).symm).trans
    ((TauCeti.CompletedGroup.projection k).map_inv (d.completedBCHExp ℒ x)).symm

/-- Completed Lie coordinates with zero bracket add under the completed exponential. -/
theorem completedBCHExp_add_of_lie_eq_zero {x y : d.completedLie ℒ} (h : ⁅x, y⁆ = 0) :
    d.completedBCHExp ℒ (x + y) = d.completedBCHExp ℒ x * d.completedBCHExp ℒ y := by
  apply TauCeti.CompletedGroup.ext
  intro k
  rw [map_mul, projection_completedBCHExp, projection_completedBCHExp,
    projection_completedBCHExp, map_add]
  apply BCHGroup.exp_add_of_lie_eq_zero
  rw [← LieHom.map_lie, h, map_zero]

/-- Integer multiples of a completed Lie coordinate give integer powers. -/
theorem completedBCHExp_zsmul (x : d.completedLie ℒ) (n : ℤ) :
    d.completedBCHExp ℒ (n • x) = d.completedBCHExp ℒ x ^ n := by
  apply TauCeti.CompletedGroup.ext
  intro k
  rw [map_zpow, projection_completedBCHExp, projection_completedBCHExp, map_zsmul,
    BCHGroup.exp_zsmul]
  -- The power on the right is taken in the categorical tower object.
  rfl

/-- The identity completed group element has zero logarithmic coordinate. -/
@[simp]
theorem completedBCHExp_symm_one : (d.completedBCHExp ℒ).symm 1 = 0 := by
  apply (d.completedBCHExp ℒ).injective
  simp only [Equiv.apply_symm_apply, completedBCHExp_zero]

/-- Inversion negates the logarithmic coordinate of a completed group element. -/
@[simp]
theorem completedBCHExp_symm_inv (g : d.completedBCHGroup ℒ) :
    (d.completedBCHExp ℒ).symm g⁻¹ = -(d.completedBCHExp ℒ).symm g := by
  apply (d.completedBCHExp ℒ).injective
  simp only [Equiv.apply_symm_apply, completedBCHExp_neg]

end TauCeti.PositiveDegrees

namespace TauCeti.GradedLieHom

open Mei

universe u

variable {N M R : Type*} {L L' : Type u} [AddCommMonoid N] [AddCommMonoid M]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq N] [DecidableEq M]
  {d : PositiveDegrees N} {e : PositiveDegrees M}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ]
  {T : PositiveDegreeMap d e}

local notation "F" =>
  LieIdeal.completionFiltration (d.truncationIdeal ℒ) (d.truncationIdeal_antitone ℒ)
local notation "G" =>
  LieIdeal.completionFiltration (e.truncationIdeal ℳ) (e.truncationIdeal_antitone ℳ)

/-- In logarithmic coordinates, a completed BCH map is the linear completion map
with the same cutoff modulus. -/
theorem completedBCHExp_symm_completedMap (f : GradedLieHom T ℒ ℳ)
    (g : d.completedBCHGroup ℒ) :
    (e.completedBCHExp ℳ).symm (f.completedMap g) =
      (F).completionMap G f.toLieHom.toLinearMap T.modulus T.monotone_modulus
        (fun k _ hx => f.map_mem_truncationIdeal k hx) ((d.completedBCHExp ℒ).symm g) := by
  apply (G).completion_ext
  intro k
  rw [ModuleFiltration.projection_completionMap]
  rw [← LieIdeal.completionProjection_apply,
    e.completionProjection_completedBCHExp_symm ℳ, projection_completedMap]
  refine ((f.lieTruncatedMap k le_rfl).log_bchGroupMap
    (TauCeti.CompletedGroup.projection (T.modulus k) g)).trans ?_
  rw [← d.completionProjection_completedBCHExp_symm ℒ,
    LieIdeal.completionProjection_apply]
  rw [lieTruncatedMap_def]
  exact LinearMap.congr_fun
    ((d.truncationIdeal ℒ (T.modulus k)).toLinearMap_mapQ (e.truncationIdeal ℳ k)
      f.toLieHom (fun _ hx => f.map_mem_truncationIdeal k hx)) _

end TauCeti.GradedLieHom
