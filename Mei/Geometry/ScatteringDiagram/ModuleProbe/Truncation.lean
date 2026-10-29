/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Grading.Lie

/-!
# Charge-one coefficients in finite module probes

The extended degree of a charge-one coefficient is its relative degree plus one.
Consequently, truncating the probe at order `k + 1` retains exactly the order-`k`
shifted coefficient quotient. We identify this quotient with the image of the
coefficient summand in the truncated probe, and recover coefficients by projection.
The identification commutes with truncation and carries the mixed Lie bracket to
the existing finite coefficient action.

The construction uses Mathlib's quotient linear maps and equivalences onto ranges,
and the homogeneous projections of `ModuleProbe.grading`. The module probe setting
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §3.3.3 (arXiv:1503.06183).
-/

public section
noncomputable section

namespace Mei.ModuleProbe

variable {R M Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]

/-- The probe degree ideal splits into the base cutoff and the shifted coefficient
cutoff, with the latter one order lower. -/
theorem mem_degreeIdeal_succ (k : ℕ) (x : ProbeLie d ℳ p ℒ) :
    x ∈ (positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) (k + 1) ↔
      x.right ∈ d.degreeIdeal ℒ (k + 1) ∧
      moduleCoefficientsEquiv d ℳ p x.left ∈ (d.shiftedFiltration ℳ p).submodule (k + 1) := by
  rw [(positiveDegrees d p).mem_degreeIdeal_iff, d.mem_degreeIdeal_iff,
    d.shiftedFiltration_succ ℳ p,
    d.mem_degreeSubmodule_iff (shiftedGrading ℳ d.monoid p)]
  constructor
  · intro hx
    constructor
    · intro q hq
      have h := hx (q, 0, 0) (by simpa using hq)
      rw [coe_decompose_grading_base] at h
      simpa using congrArg (LieAlgebra.SemiDirectSum.projr _) h
    · intro n hn
      have h := hx (p + n, 1, 0) (by simp [map_add]; omega)
      rw [coe_decompose_grading_module, add_sub_cancel_left] at h
      simpa using congrArg (fun y : ProbeLie d ℳ p ℒ =>
        moduleCoefficientsEquiv d ℳ p y.left) h
  · rintro ⟨hb, hm⟩ ⟨q, c, l⟩ hq
    by_cases hl : l = 0
    · subst l
      by_cases hc₀ : c = 0
      · subst c
        rw [coe_decompose_grading_base, hb q (by simpa using hq), map_zero]
      · by_cases hc₁ : c = 1
        · subst c
          rw [coe_decompose_grading_module, hm (q - p) (by simp [map_sub] at *; omega),
            map_zero, map_zero]
        · exact coe_decompose_grading_charge d ℳ p ℒ x q c 0 hc₀ hc₁
    · exact coe_decompose_grading_normal d ℳ p ℒ x q c l hl

/-- A coefficient disappears at extended order `k + 1` exactly when its relative
order exceeds `k`. -/
@[simp↓]
theorem moduleInclusion_mem_degreeIdeal_succ (k : ℕ) (a : shiftedSubmodule ℳ d.monoid p) :
    moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a) ∈
      (positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) (k + 1) ↔
      a ∈ (d.shiftedFiltration ℳ p).submodule (k + 1) := by
  rw [mem_degreeIdeal_succ]
  simp

/-- Include the order-`k` shifted coefficient quotient in the order-`k + 1` probe. -/
def moduleQuotientInclusion (k : ℕ) : (d.shiftedFiltration ℳ p).quotient k →ₗ[R]
    (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1) :=
  ((d.shiftedFiltration ℳ p).submodule (k + 1)).mapQ
    ((positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) (k + 1)).toSubmodule
    ((moduleInclusion d ℳ p ℒ).toLinearMap.comp
      (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap)
    (fun a ha => (moduleInclusion_mem_degreeIdeal_succ d ℳ p ℒ k a).mpr ha)

/-- The finite coefficient inclusion keeps the original coefficient representative. -/
@[simp]
theorem moduleQuotientInclusion_mk (k : ℕ) (a : shiftedSubmodule ℳ d.monoid p) :
    moduleQuotientInclusion d ℳ p ℒ k (Submodule.Quotient.mk a) =
      LieSubmodule.Quotient.mk
        (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a)) := by
  rfl

/-- Recover the finite shifted coefficient from an arbitrary truncated probe. -/
def moduleQuotientProjection (k : ℕ) :
    (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1) →ₗ[R]
      (d.shiftedFiltration ℳ p).quotient k :=
  ((positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) (k + 1)).toSubmodule.mapQ
    ((d.shiftedFiltration ℳ p).submodule (k + 1))
    ((moduleCoefficientsEquiv d ℳ p).toLinearMap.comp
      (LieAlgebra.SemiDirectSum.projl _))
    (fun x hx => ((mem_degreeIdeal_succ d ℳ p ℒ k x).mp hx).2)

/-- Coefficient recovery is the original left projection on representatives. -/
@[simp]
theorem moduleQuotientProjection_mk (k : ℕ) (x : ProbeLie d ℳ p ℒ) :
    moduleQuotientProjection d ℳ p ℒ k (LieSubmodule.Quotient.mk x) =
      Submodule.Quotient.mk (moduleCoefficientsEquiv d ℳ p x.left) := by
  rfl

/-- Recovering an included coefficient is the identity, including at order zero. -/
@[simp]
theorem moduleQuotientProjection_inclusion (k : ℕ)
    (a : (d.shiftedFiltration ℳ p).quotient k) :
    moduleQuotientProjection d ℳ p ℒ k (moduleQuotientInclusion d ℳ p ℒ k a) = a := by
  obtain ⟨a, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective a
  simp

/-- No retained coefficient is lost by inclusion into the finite probe. -/
theorem moduleQuotientInclusion_injective (k : ℕ) :
    Function.Injective (moduleQuotientInclusion d ℳ p ℒ k) :=
  Function.LeftInverse.injective (moduleQuotientProjection_inclusion d ℳ p ℒ k)

/-- The image of the finite coefficient inclusion is exactly the sum of all
charge-one homogeneous pieces of the truncated probe. -/
theorem range_moduleQuotientInclusion (k : ℕ) :
    (moduleQuotientInclusion d ℳ p ℒ k).range =
      ⨆ q, (positiveDegrees d p).truncatedGrading (grading d ℳ p ℒ) (k + 1) (q, 1, 0) := by
  have hs : Function.Surjective (fun q : Γ => q - p) :=
    fun n => ⟨p + n, add_sub_cancel_left p n⟩
  have hr : ((moduleInclusion d ℳ p ℒ).toLinearMap.comp
      (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap).range =
        ⨆ q, grading d ℳ p ℒ (q, 1, 0) := by
    simp only [grading_module, ← Submodule.map_iSup]
    rw [hs.iSup_comp (shiftedGrading ℳ d.monoid p),
      (DirectSum.Decomposition.isInternal (shiftedGrading ℳ d.monoid p)).submodule_iSup_eq_top,
      Submodule.map_top]
  rw [moduleQuotientInclusion, Submodule.range_mapQ, hr, Submodule.map_iSup]
  simp only [PositiveDegrees.truncatedGrading_eq]

/-- Charge one at extended order `k + 1` is the order-`k` shifted coefficient module. -/
def moduleQuotientEquiv (k : ℕ) : (d.shiftedFiltration ℳ p).quotient k ≃ₗ[R]
    ↥(⨆ q, (positiveDegrees d p).truncatedGrading (grading d ℳ p ℒ) (k + 1) (q, 1, 0)) :=
  (LinearEquiv.ofLeftInverse (moduleQuotientProjection_inclusion d ℳ p ℒ k)).trans
    (LinearEquiv.ofEq _ _ (range_moduleQuotientInclusion d ℳ p ℒ k))

/-- The charge-one equivalence has the canonical finite inclusion as its underlying map. -/
@[simp]
theorem coe_moduleQuotientEquiv (k : ℕ) (a : (d.shiftedFiltration ℳ p).quotient k) :
    (moduleQuotientEquiv d ℳ p ℒ k a :
      (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1)) =
        moduleQuotientInclusion d ℳ p ℒ k a := by
  simp [moduleQuotientEquiv]

/-- The inverse charge-one equivalence is coefficient recovery. -/
@[simp]
theorem moduleQuotientEquiv_symm_apply (k : ℕ)
    (x : ↥(⨆ q, (positiveDegrees d p).truncatedGrading (grading d ℳ p ℒ) (k + 1) (q, 1, 0))) :
    (moduleQuotientEquiv d ℳ p ℒ k).symm x =
      moduleQuotientProjection d ℳ p ℒ k x := by
  obtain ⟨a, rfl⟩ := (moduleQuotientEquiv d ℳ p ℒ k).surjective x
  simp

/-- Probe truncation agrees with the original shifted coefficient transition. -/
@[simp]
theorem truncationMap_moduleQuotientInclusion {k l : ℕ} (h : k ≤ l)
    (a : (d.shiftedFiltration ℳ p).quotient l) :
    (positiveDegrees d p).truncationMap (grading d ℳ p ℒ) (Nat.add_le_add_right h 1)
      (moduleQuotientInclusion d ℳ p ℒ l a) =
      moduleQuotientInclusion d ℳ p ℒ k ((d.shiftedFiltration ℳ p).transition h a) := by
  obtain ⟨a, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (l + 1)).mkQ_surjective a
  simp

/-- Coefficient recovery commutes with transitions on the whole truncated probe. -/
@[simp]
theorem transition_moduleQuotientProjection {k l : ℕ} (h : k ≤ l)
    (x : (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (l + 1)) :
    (d.shiftedFiltration ℳ p).transition h (moduleQuotientProjection d ℳ p ℒ l x) =
      moduleQuotientProjection d ℳ p ℒ k
        ((positiveDegrees d p).truncationMap (grading d ℳ p ℒ) (Nat.add_le_add_right h 1) x) := by
  obtain ⟨x, rfl⟩ := ((positiveDegrees d p).degreeIdeal
    (grading d ℳ p ℒ) (l + 1)).surjective_mkQ x
  simp

/-- The mixed bracket in the finite probe is the existing order-`k` coefficient action. -/
theorem lie_base_moduleQuotientInclusion (k : ℕ) (x : L)
    (a : (d.shiftedLieFiltration ℒ ℳ p).quotient k) :
    ⁅((positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) (k + 1)).mkQ
        (baseInclusion d ℳ p ℒ x), moduleQuotientInclusion d ℳ p ℒ k a⁆ =
      moduleQuotientInclusion d ℳ p ℒ k
        ((d.shiftedLieFiltration ℒ ℳ p).quotientLieAction d ℒ k x a) := by
  obtain ⟨a, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective a
  rw [Submodule.mkQ_apply, moduleQuotientInclusion_mk,
    ModuleFiltration.quotientLieAction_mk, moduleQuotientInclusion_mk,
    LieIdeal.mkQ_apply, ← LieSubmodule.Quotient.mk_bracket,
    lie_baseInclusion_moduleInclusion]
  rw [← (moduleCoefficientsEquiv d ℳ p).symm_apply_apply
    (actionDerivationHom d ℳ p (ℒ := ℒ) x ((moduleCoefficientsEquiv d ℳ p).symm a)),
    moduleCoefficientsEquiv_actionDerivationHom, LinearEquiv.apply_symm_apply]

/-- Two included finite coefficients have zero bracket. -/
@[simp]
theorem lie_moduleQuotientInclusion (k : ℕ)
    (a b : (d.shiftedFiltration ℳ p).quotient k) :
    ⁅moduleQuotientInclusion d ℳ p ℒ k a, moduleQuotientInclusion d ℳ p ℒ k b⁆ = 0 := by
  obtain ⟨a, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective a
  obtain ⟨b, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective b
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, moduleQuotientInclusion_mk,
    moduleQuotientInclusion_mk,
    ← LieSubmodule.Quotient.mk_bracket, lie_moduleInclusion]
  exact ((positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) (k + 1)).mkQ.map_zero

end Mei.ModuleProbe
