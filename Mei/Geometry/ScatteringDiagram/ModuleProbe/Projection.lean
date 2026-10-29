/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Completion

/-!
# Recovering base labels from module probes

Projection from the semidirect Lie algebra to its base descends through every
degree truncation and hence to the completed BCH groups. It splits the existing
charge-zero inclusion. At extended order `k + 1`, its kernel is precisely the
embedded relative-order-`k` coefficient module; the completed kernel consists
precisely of completed coefficient labels. Thus forgetting the probe coefficient
retains the base label without requiring a faithful coefficient action.
The kernel equivalence extracts coefficients, with their finite logarithmic
projections and the base-conjugation action.

We use Mathlib's `LieAlgebra.SemiDirectSum.projr`, the degree-ideal splitting in
`ModuleProbe.mem_degreeIdeal_succ`, and the finite and completed coefficient
inclusions. The kernel equivalence uses Mathlib's `MonoidHom.ofInjective`;
its conjugation formula uses `base_conj_completedModuleBCHInclusion`.
The use of this semidirect extension to recover coefficient transport
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ : Type*} {M L : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ) [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]

private theorem right_mem_degreeIdeal (k : ℕ) {x : ProbeLie d ℳ p ℒ}
    (hx : x ∈ (positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) k) :
    x.right ∈ d.degreeIdeal ℒ k := by
  cases k with
  | zero => simp
  | succ k => exact ((mem_degreeIdeal_succ d ℳ p ℒ k x).mp hx).1

/-- Forget the coefficient summand in a finite probe, at the same cutoff. -/
def baseQuotientProjection (k : ℕ) :
    (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) k →ₗ⁅R⁆ d.truncatedLie ℒ k :=
  ((positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) k).mapQ (d.degreeIdeal ℒ k)
    (LieAlgebra.SemiDirectSum.projr _) (fun _ hx => right_mem_degreeIdeal d ℳ p ℒ k hx)

/-- Projection of a representative is its original base component. -/
@[simp]
theorem baseQuotientProjection_mk (k : ℕ) (x : ProbeLie d ℳ p ℒ) :
    baseQuotientProjection d ℳ p ℒ k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x.right := by
  exact ((positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) k).mapQ_apply
    (d.degreeIdeal ℒ k) (LieAlgebra.SemiDirectSum.projr _) _ x

/-- Base projection retracts the finite charge-zero inclusion. -/
@[simp]
theorem baseQuotientProjection_base (k : ℕ) (x : d.truncatedLie ℒ k) :
    baseQuotientProjection d ℳ p ℒ k
      ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp) x) = x := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  simp [LieIdeal.mkQ_apply, baseInclusion]

/-- Forgetting coefficients commutes with every probe truncation. -/
@[simp]
theorem truncationMap_baseQuotientProjection {k l : ℕ} (h : k ≤ l)
    (x : (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) l) :
    d.truncationMap ℒ h (baseQuotientProjection d ℳ p ℒ l x) =
      baseQuotientProjection d ℳ p ℒ k
        ((positiveDegrees d p).truncationMap (grading d ℳ p ℒ) h x) := by
  obtain ⟨x, rfl⟩ := ((positiveDegrees d p).degreeIdeal (grading d ℳ p ℒ) l).surjective_mkQ x
  simp [LieIdeal.mkQ_apply]

/-- The coefficient summand projects to zero in the base. -/
@[simp]
theorem baseQuotientProjection_module (k : ℕ)
    (a : (d.shiftedFiltration ℳ p).quotient k) :
    baseQuotientProjection d ℳ p ℒ (k + 1) (moduleQuotientInclusion d ℳ p ℒ k a) = 0 := by
  obtain ⟨a, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective a
  simp [LieSubmodule.Quotient.mk, moduleInclusion]

/-- A finite probe with zero base component is recovered from its coefficient
projection. No condition on the coefficient action is required. -/
theorem moduleQuotientInclusion_projection_of_base_eq_zero (k : ℕ)
    (x : (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1))
    (hx : baseQuotientProjection d ℳ p ℒ (k + 1) x = 0) :
    moduleQuotientInclusion d ℳ p ℒ k (moduleQuotientProjection d ℳ p ℒ k x) = x := by
  obtain ⟨x, rfl⟩ := ((positiveDegrees d p).degreeIdeal
    (grading d ℳ p ℒ) (k + 1)).surjective_mkQ x
  have hr : x.right ∈ d.degreeIdeal ℒ (k + 1) := by
    apply (d.degreeIdeal ℒ (k + 1)).mkQ_eq_zero.mp
    simpa only [LieIdeal.mkQ_apply, baseQuotientProjection_mk] using hx
  rw [LieIdeal.mkQ_apply, moduleQuotientProjection_mk, moduleQuotientInclusion_mk,
    LinearEquiv.symm_apply_apply]
  apply (Submodule.Quotient.eq _).mpr
  apply (mem_degreeIdeal_succ d ℳ p ℒ k _).mpr
  constructor
  · have he : (moduleInclusion d ℳ p ℒ x.left - x).right = -x.right := by
      rw [← LieAlgebra.SemiDirectSum.projr_mk, map_sub,
        LieAlgebra.SemiDirectSum.projr_inl_apply, LieAlgebra.SemiDirectSum.projr_mk, zero_sub]
    rw [he]
    exact (d.degreeIdeal ℒ (k + 1)).neg_mem hr
  · simp [moduleInclusion]

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- A finite BCH label projects to the identity exactly when it is a coefficient
label. The coefficient is uniquely determined. -/
theorem baseBCHProjection_eq_one_iff (k : ℕ)
    (g : BCHGroup ((positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1))) :
    (baseQuotientProjection d ℳ p ℒ (k + 1)).bchGroupMap g = 1 ↔
      ∃! a, moduleBCHInclusion d ℳ p ℒ k a = g := by
  rw [(moduleBCHInclusion_injective d ℳ p ℒ k).existsUnique_iff_exists]
  constructor
  · intro hg
    have hz : baseQuotientProjection d ℳ p ℒ (k + 1) (BCHGroup.log g) = 0 := by
      simpa only [LieHom.log_bchGroupMap, BCHGroup.log_one] using congrArg BCHGroup.log hg
    have he : moduleBCHInclusion d ℳ p ℒ k
        (Multiplicative.ofAdd (moduleQuotientProjection d ℳ p ℒ k (BCHGroup.log g))) = g := by
      rw [moduleBCHInclusion_apply, toAdd_ofAdd,
        moduleQuotientInclusion_projection_of_base_eq_zero d ℳ p ℒ k _ hz,
        BCHGroup.exp_log]
    exact ⟨_, he⟩
  · rintro ⟨a, rfl⟩
    simp

private def baseProjectionComponent (k : ℕ) :
    (positiveDegrees d p).completedBCHGroup (grading d ℳ p ℒ) →* d.truncatedGroup ℒ k :=
  (baseQuotientProjection d ℳ p ℒ k).bchGroupMap.comp (CompletedGroup.projection k)

private theorem baseProjectionComponent_compatible (k l : ℕ) (h : k ≤ l) :
    ((d.groupTower ℒ).map (CategoryTheory.homOfLE h).op).hom.comp
      (baseProjectionComponent d ℳ p ℒ l) = baseProjectionComponent d ℳ p ℒ k := by
  ext g
  -- The tower arrows conceal the concrete BCH quotient types.
  change (d.truncationMap ℒ h).bchGroupMap
    ((baseQuotientProjection d ℳ p ℒ l).bchGroupMap (CompletedGroup.projection l g)) =
      (baseQuotientProjection d ℳ p ℒ k).bchGroupMap (CompletedGroup.projection k g)
  have hs : (d.truncationMap ℒ h).comp (baseQuotientProjection d ℳ p ℒ l) =
      (baseQuotientProjection d ℳ p ℒ k).comp
        ((positiveDegrees d p).truncationMap (grading d ℳ p ℒ) h) := by
    apply LieHom.ext
    intro x
    exact truncationMap_baseQuotientProjection d ℳ p ℒ h x
  have he := DFunLike.congr_fun (congrArg LieHom.bchGroupMap hs)
    (CompletedGroup.projection l g)
  simp only [LieHom.bchGroupMap_comp] at he
  have hp : ((positiveDegrees d p).truncationMap (grading d ℳ p ℒ) h).bchGroupMap
      (CompletedGroup.projection l g) = CompletedGroup.projection k g :=
    CompletedGroup.map_projection k l h g
  exact he.trans (congrArg (baseQuotientProjection d ℳ p ℒ k).bchGroupMap hp)

/-- Forget the completed coefficient label, retaining the completed base label. -/
def completedBaseProjection :
    (positiveDegrees d p).completedBCHGroup (grading d ℳ p ℒ) →* d.completedBCHGroup ℒ :=
  CompletedGroup.lift (baseProjectionComponent d ℳ p ℒ)
    (baseProjectionComponent_compatible d ℳ p ℒ)

/-- Completed base projection is computed at the same finite order. -/
@[simp]
theorem projection_completedBaseProjection (k : ℕ)
    (g : (positiveDegrees d p).completedBCHGroup (grading d ℳ p ℒ)) :
    CompletedGroup.projection k (completedBaseProjection d ℳ p ℒ g) =
      (baseQuotientProjection d ℳ p ℒ k).bchGroupMap (CompletedGroup.projection k g) := by
  exact CompletedGroup.projection_lift _ _ k g

/-- Projection recovers every completed charge-zero label. -/
@[simp]
theorem completedBaseProjection_base (g : d.completedBCHGroup ℒ) :
    completedBaseProjection d ℳ p ℒ ((baseGradedLieHom d ℳ p ℒ).completedMap g) = g := by
  apply CompletedGroup.ext
  intro k
  rw [projection_completedBaseProjection,
    (baseGradedLieHom d ℳ p ℒ).projection_completedMap_of_le k (a := k) (by simp)]
  have hs : (baseQuotientProjection d ℳ p ℒ k).comp
      ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp)) = LieHom.id := by
    apply LieHom.ext
    intro x
    exact baseQuotientProjection_base d ℳ p ℒ k x
  have he := congrArg LieHom.bchGroupMap hs
  rw [LieHom.bchGroupMap_comp, LieHom.bchGroupMap_id] at he
  exact DFunLike.congr_fun he (CompletedGroup.projection k g)

/-- The completed charge-zero inclusion loses no base labels. -/
theorem completedMap_base_injective :
    Function.Injective (baseGradedLieHom d ℳ p ℒ).completedMap :=
  Function.LeftInverse.injective (completedBaseProjection_base d ℳ p ℒ)

/-- Original probe exponentials project to the exponential of their base component. -/
@[simp]
theorem completedBaseProjection_expToCompletion (x : ProbeLie d ℳ p ℒ) :
    completedBaseProjection d ℳ p ℒ
      ((positiveDegrees d p).expToCompletion (grading d ℳ p ℒ) x) =
        d.expToCompletion ℒ x.right := by
  apply CompletedGroup.ext
  intro k
  -- The tower and explicit quotient give the same exponential on representatives.
  simp only [projection_completedBaseProjection, PositiveDegrees.projection_expToCompletion,
    LieHom.bchGroupMap_exp, LieIdeal.mkQ_apply, baseQuotientProjection_mk]
  rfl

/-- Completed coefficient labels lie in the kernel of base projection. -/
@[simp]
theorem completedBaseProjection_module
    (a : Multiplicative (d.shiftedFiltration ℳ p).completion) :
    completedBaseProjection d ℳ p ℒ (completedModuleBCHInclusion d ℳ p ℒ a) = 1 := by
  apply CompletedGroup.ext
  intro k
  cases k with
  | zero =>
    exact @Subsingleton.elim (d.truncatedGroup ℒ 0) _ _ _
  | succ k =>
    rw [projection_completedBaseProjection, projection_completedModuleBCHInclusion, map_one]
    -- The right-hand identity is supplied by the categorical tower object.
    exact (baseBCHProjection_eq_one_iff d ℳ p ℒ k _).mpr
      ⟨_, rfl, fun b hb => moduleBCHInclusion_injective d ℳ p ℒ k hb⟩

/-- A completed probe label has trivial base precisely when it is the label of a
unique completed shifted coefficient. This identifies the entire kernel, including
coefficients with infinitely many nonzero homogeneous components. -/
theorem completedBaseProjection_eq_one_iff
    (g : (positiveDegrees d p).completedBCHGroup (grading d ℳ p ℒ)) :
    completedBaseProjection d ℳ p ℒ g = 1 ↔
      ∃! a, completedModuleBCHInclusion d ℳ p ℒ a = g := by
  rw [(completedModuleBCHInclusion_injective d ℳ p ℒ).existsUnique_iff_exists]
  constructor
  · intro hg
    -- Recover a finite coefficient from each logarithm in the finite kernel.
    have hz (k : ℕ) : baseQuotientProjection d ℳ p ℒ (k + 1)
        (BCHGroup.log (L := (positiveDegrees d p).truncatedLie
          (grading d ℳ p ℒ) (k + 1)) (CompletedGroup.projection (k + 1) g)) = 0 := by
      have hp : (baseQuotientProjection d ℳ p ℒ (k + 1)).bchGroupMap
          (CompletedGroup.projection (k + 1) g) = 1 := by
        rw [← projection_completedBaseProjection, hg, map_one]
        rfl
      obtain ⟨a, ha, _⟩ := (baseBCHProjection_eq_one_iff d ℳ p ℒ k _).mp hp
      rw [← ha, moduleBCHInclusion_apply, BCHGroup.log_exp, baseQuotientProjection_module]
    let a₀ (k : ℕ) := moduleQuotientProjection d ℳ p ℒ k
      (BCHGroup.log (L := (positiveDegrees d p).truncatedLie
        (grading d ℳ p ℒ) (k + 1)) (CompletedGroup.projection (k + 1) g))
    -- Truncation compatibility glues these coefficients into one completed element.
    have ha : (fun k : ℕᵒᵖ => a₀ k.unop) ∈ (d.shiftedFiltration ℳ p).completionSubmodule := by
      apply (ModuleFiltration.mem_completionSubmodule_iff _ _).mpr
      intro k l h
      have hp : ((positiveDegrees d p).truncationMap (grading d ℳ p ℒ)
          (Nat.add_le_add_right h 1)).bchGroupMap (CompletedGroup.projection (l + 1) g) =
            CompletedGroup.projection (k + 1) g :=
        CompletedGroup.map_projection (k + 1) (l + 1) (Nat.add_le_add_right h 1) g
      have hl := (((positiveDegrees d p).truncationMap (grading d ℳ p ℒ)
        (Nat.add_le_add_right h 1)).log_bchGroupMap
          (CompletedGroup.projection (l + 1) g)).symm.trans
        (congrArg (BCHGroup.log (L := (positiveDegrees d p).truncatedLie
          (grading d ℳ p ℒ) (k + 1))) hp)
      exact (transition_moduleQuotientProjection d ℳ p ℒ h _).trans
        (congrArg (moduleQuotientProjection d ℳ p ℒ k) hl)
    refine ⟨Multiplicative.ofAdd ⟨_, ha⟩, ?_⟩
    apply CompletedGroup.ext
    intro k
    cases k with
    | zero =>
      exact @Subsingleton.elim
        ((positiveDegrees d p).truncatedGroup (grading d ℳ p ℒ) 0) _ _ _
    | succ k =>
      rw [projection_completedModuleBCHInclusion, toAdd_ofAdd,
        ModuleFiltration.projection_mk, moduleBCHInclusion_apply, toAdd_ofAdd]
      exact (congrArg BCHGroup.exp
        (moduleQuotientInclusion_projection_of_base_eq_zero d ℳ p ℒ k _ (hz k))).trans
          (BCHGroup.exp_log _)
  · rintro ⟨a, rfl⟩
    exact completedBaseProjection_module d ℳ p ℒ a

local notation "G" => PositiveDegrees.completedBCHGroup (positiveDegrees d p) (grading d ℳ p ℒ)
local notation "C" => ModuleFiltration.completion (d.shiftedFiltration ℳ p)
local notation "π" => completedBaseProjection d ℳ p ℒ
local notation "ι" => completedModuleBCHInclusion d ℳ p ℒ

/-- The completed coefficient inclusion has exactly the kernel of base projection
as its range. -/
theorem range_completedModuleBCHInclusion : (ι).range = (π).ker := by
  ext g
  rw [MonoidHom.mem_range, MonoidHom.mem_ker,
    completedBaseProjection_eq_one_iff,
    (completedModuleBCHInclusion_injective d ℳ p ℒ).existsUnique_iff_exists]

/-- The unique completed coefficient of a label with trivial base. Products of
labels correspond to addition in the coefficient module. -/
def completedKernelEquiv : (π).ker ≃* Multiplicative C :=
  (MulEquiv.subgroupCongr (range_completedModuleBCHInclusion d ℳ p ℒ).symm).trans
    (MonoidHom.ofInjective (completedModuleBCHInclusion_injective d ℳ p ℒ)).symm

/-- Exponentiating the extracted coefficient recovers the original label. -/
@[simp]
theorem completedModuleBCHInclusion_completedKernelEquiv (g : (π).ker) :
    ι (completedKernelEquiv d ℳ p ℒ g) = g.val := by
  exact MonoidHom.apply_ofInjective_symm
    (completedModuleBCHInclusion_injective d ℳ p ℒ) _

/-- Extracting an included coefficient recovers that coefficient. -/
@[simp]
theorem completedKernelEquiv_inclusion (a : Multiplicative C) :
    completedKernelEquiv d ℳ p ℒ ⟨ι a, by simp⟩ = a := by
  apply completedModuleBCHInclusion_injective d ℳ p ℒ
  simp

/-- The inverse equivalence is the original completed coefficient inclusion. -/
@[simp]
theorem coe_completedKernelEquiv_symm (a : Multiplicative C) :
    ((completedKernelEquiv d ℳ p ℒ).symm a : G) = ι a := by
  exact (completedModuleBCHInclusion_completedKernelEquiv d ℳ p ℒ
    ((completedKernelEquiv d ℳ p ℒ).symm a)).symm.trans
      (congrArg ι ((completedKernelEquiv d ℳ p ℒ).apply_symm_apply a))

/-- Relative order `k` of the extracted coefficient is the coefficient projection
of the logarithm at extended order `k + 1`. -/
@[simp]
theorem projection_completedKernelEquiv (g : (π).ker) (k : ℕ) :
    (d.shiftedFiltration ℳ p).projection k
        (completedKernelEquiv d ℳ p ℒ g).toAdd =
      moduleQuotientProjection d ℳ p ℒ k
        (BCHGroup.log (L := (positiveDegrees d p).truncatedLie
          (grading d ℳ p ℒ) (k + 1)) (CompletedGroup.projection (k + 1) g.val)) := by
  have he := congrArg (CompletedGroup.projection (k + 1))
    (completedModuleBCHInclusion_completedKernelEquiv d ℳ p ℒ g)
  rw [projection_completedModuleBCHInclusion, moduleBCHInclusion_apply,
    toAdd_ofAdd] at he
  rw [← he, BCHGroup.log_exp, moduleQuotientProjection_inclusion]

/-- Extracting a conjugated vertical label gives the existing completed BCH
action on its coefficient. -/
theorem completedKernelEquiv_base_conj (b : d.completedBCHGroup ℒ) (g : (π).ker) :
    (completedKernelEquiv d ℳ p ℒ
      ⟨(baseGradedLieHom d ℳ p ℒ).completedMap b * g.val *
        ((baseGradedLieHom d ℳ p ℒ).completedMap b)⁻¹, by
          simp only [MonoidHom.mem_ker, map_mul, map_inv,
            completedBaseProjection_base, MonoidHom.mem_ker.mp g.property,
            mul_one, mul_inv_cancel]⟩).toAdd =
      (d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ b
        (completedKernelEquiv d ℳ p ℒ g).toAdd := by
  apply Multiplicative.ofAdd.injective
  apply completedModuleBCHInclusion_injective d ℳ p ℒ
  simp only [ofAdd_toAdd, completedModuleBCHInclusion_completedKernelEquiv]
  rw [← base_conj_completedModuleBCHInclusion,
    completedModuleBCHInclusion_completedKernelEquiv]

end Mei.ModuleProbe
