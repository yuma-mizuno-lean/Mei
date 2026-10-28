/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Lie

/-!
# The homogeneous decomposition of a module probe

The original Lie algebra occupies charge zero. The shifted module occupies charge one,
with its ambient degree restored from the relative shifted grading. All other pieces vanish.
The two original direct-sum decompositions give the decomposition of the semidirect sum.
-/

public section

open scoped DirectSum
noncomputable section
namespace Mei.ModuleProbe
variable {R M Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

/-- The charge-zero and charge-one homogeneous pieces of the module probe. -/
def grading (a : Γ × ℤ × ℤ) : Submodule R (ProbeLie d ℳ p ℒ) :=
  if a.2.1 = 0 ∧ a.2.2 = 0 then (ℒ a.1).map (baseInclusion d ℳ p ℒ).toLinearMap
  else if a.2.1 = 1 ∧ a.2.2 = 0 then
    (shiftedGrading ℳ d.monoid p (a.1 - p)).map
      ((moduleInclusion d ℳ p ℒ).toLinearMap.comp
        (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap)
  else ⊥

/-- The defining charge cases of the probe grading. -/
theorem grading_def (a : Γ × ℤ × ℤ) : grading d ℳ p ℒ a =
    if a.2.1 = 0 ∧ a.2.2 = 0 then (ℒ a.1).map (baseInclusion d ℳ p ℒ).toLinearMap
    else if a.2.1 = 1 ∧ a.2.2 = 0 then
      (shiftedGrading ℳ d.monoid p (a.1 - p)).map
        ((moduleInclusion d ℳ p ℒ).toLinearMap.comp
          (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap)
    else ⊥ := by rfl

/-- Charge zero recovers the original homogeneous component. -/
@[simp]
theorem grading_base (q : Γ) : grading d ℳ p ℒ (q, 0, 0) =
    (ℒ q).map (baseInclusion d ℳ p ℒ).toLinearMap := by
  simp only [grading, and_self, ↓reduceIte]

/-- Charge one carries the shifted component at its ambient degree. -/
@[simp]
theorem grading_module (q : Γ) : grading d ℳ p ℒ (q, 1, 0) =
    (shiftedGrading ℳ d.monoid p (q - p)).map
      ((moduleInclusion d ℳ p ℒ).toLinearMap.comp
        (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap) := by
  simp only [grading, one_ne_zero, false_and, ↓reduceIte, and_self]

/-- A charge-zero element has no coefficient part and has homogeneous base part. -/
@[simp↓]
theorem mem_grading_base (q : Γ) (x : ProbeLie d ℳ p ℒ) :
    x ∈ grading d ℳ p ℒ (q, 0, 0) ↔ x.left = 0 ∧ x.right ∈ ℒ q := by
  rw [grading_base]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · rintro ⟨hl, hr⟩
    refine Submodule.mem_map.mpr ⟨x.right, hr, ?_⟩
    apply LieAlgebra.SemiDirectSum.ext <;> simp [hl]

/-- A charge-one element has no base part and has homogeneous shifted coefficient part. -/
@[simp↓]
theorem mem_grading_module (q : Γ) (x : ProbeLie d ℳ p ℒ) :
    x ∈ grading d ℳ p ℒ (q, 1, 0) ↔ x.right = 0 ∧
      moduleCoefficientsEquiv d ℳ p x.left ∈ shiftedGrading ℳ d.monoid p (q - p) := by
  rw [grading_module]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · rintro ⟨hr, ha⟩
    refine Submodule.mem_map.mpr ⟨moduleCoefficientsEquiv d ℳ p x.left, ha, ?_⟩
    apply LieAlgebra.SemiDirectSum.ext <;> simp [hr]

/-- Only charges zero and one occur in the module probe. -/
@[simp]
theorem grading_charge_eq_bot (q : Γ) (c l : ℤ) (hc₀ : c ≠ 0) (hc₁ : c ≠ 1) :
    grading d ℳ p ℒ (q, c, l) = ⊥ := by
  simp only [grading, hc₀, hc₁, false_and, ↓reduceIte]

/-- The module probe has zero degree in the final coordinate. -/
@[simp]
theorem grading_normal_eq_bot (q : Γ) (c l : ℤ) (hl : l ≠ 0) :
    grading d ℳ p ℒ (q, c, l) = ⊥ := by
  simp only [grading, hl, and_false, ↓reduceIte]

variable [DirectSum.Decomposition ℳ]

private def baseToPiece (n : Γ) : ℒ n →ₗ[R] grading d ℳ p ℒ (n, 0, 0) :=
  (LinearEquiv.ofEq _ _ (grading_base d ℳ p ℒ n).symm).toLinearMap.comp
    ((baseInclusion d ℳ p ℒ).toLinearMap.submoduleMap (ℒ n))

private def moduleToPiece (n : Γ) :
    shiftedGrading ℳ d.monoid p n →ₗ[R] grading d ℳ p ℒ (p + n, 1, 0) :=
  (LinearEquiv.ofEq _ _ (by rw [grading_module, add_sub_cancel_left])).symm.toLinearMap.comp
    (((moduleInclusion d ℳ p ℒ).toLinearMap.comp
      (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap).submoduleMap
        (shiftedGrading ℳ d.monoid p n))

private def probeDecompose : ProbeLie d ℳ p ℒ →ₗ[R]
    ⨁ a, grading d ℳ p ℒ a :=
  (DirectSum.toModule R Γ _ (fun n => (DirectSum.lof R _ _ (n, 0, 0)).comp
    (baseToPiece d ℳ p ℒ n))).comp
      ((DirectSum.decomposeLinearEquiv ℒ).toLinearMap.comp
        (LieAlgebra.SemiDirectSum.projr _).toLinearMap) +
  (DirectSum.toModule R Γ _ (fun n => (DirectSum.lof R _ _ (p + n, 1, 0)).comp
    (moduleToPiece d ℳ p ℒ n))).comp
      ((DirectSum.decomposeLinearEquiv (shiftedGrading ℳ d.monoid p)).toLinearMap.comp
        ((moduleCoefficientsEquiv d ℳ p).toLinearMap.comp
          (LieAlgebra.SemiDirectSum.projl _)))

private theorem probeDecompose_base (n : Γ) (x : ℒ n) :
    probeDecompose d ℳ p ℒ (baseInclusion d ℳ p ℒ x) =
      DirectSum.lof R _ _ (n, 0, 0) (baseToPiece d ℳ p ℒ n x) := by
  simp [probeDecompose, baseInclusion, DirectSum.decomposeLinearEquiv_apply_coe]

private theorem probeDecompose_module (n : Γ)
    (x : shiftedGrading ℳ d.monoid p n) :
    probeDecompose d ℳ p ℒ
      (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm x.val)) =
      DirectSum.lof R _ _ (p + n, 1, 0) (moduleToPiece d ℳ p ℒ n x) := by
  simp [probeDecompose, moduleInclusion, DirectSum.decomposeLinearEquiv_apply_coe]

private theorem probeDecompose_of_mem (a : Γ × ℤ × ℤ)
    (x : grading d ℳ p ℒ a) :
    probeDecompose d ℳ p ℒ x = DirectSum.lof R _ _ a x := by
  rcases a with ⟨q, c, l⟩
  rcases x with ⟨x, hx⟩
  by_cases h0 : c = 0 ∧ l = 0
  · rcases h0 with ⟨rfl, rfl⟩
    simp only [grading, and_self, ↓reduceIte] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact probeDecompose_base d ℳ p ℒ q ⟨y, hy⟩
  · by_cases h1 : c = 1 ∧ l = 0
    · rcases h1 with ⟨rfl, rfl⟩
      simp only [grading, one_ne_zero, false_and, ↓reduceIte, and_self] at hx
      rcases hx with ⟨y, hy, rfl⟩
      generalize hn : q - p = n at hy
      have hq : q = p + n := by rw [← hn]; abel
      subst q
      convert probeDecompose_module d ℳ p ℒ n ⟨y, hy⟩ using 1
      apply congrArg
      apply Subtype.ext
      rfl
    · simp only [grading, h0, h1, ↓reduceIte, Submodule.mem_bot] at hx
      subst x
      -- Both sides are linear maps evaluated at the zero element of the zero piece.
      change probeDecompose d ℳ p ℒ 0 = DirectSum.lof R _ _ (q, c, l) 0
      simp only [map_zero]

private theorem coe_comp_probeDecompose :
    (DirectSum.coeLinearMap (grading d ℳ p ℒ)).comp
      (probeDecompose d ℳ p ℒ) = LinearMap.id := by
  let C := DirectSum.coeLinearMap (grading d ℳ p ℒ)
  let D := probeDecompose d ℳ p ℒ
  have hb : (C.comp D).comp (baseInclusion d ℳ p ℒ).toLinearMap =
      (baseInclusion d ℳ p ℒ).toLinearMap := by
    apply DirectSum.decompose_lhom_ext ℒ
    intro n
    apply LinearMap.ext
    intro x
    -- Expose evaluation of the composed maps on a homogeneous base element.
    change C (D (baseInclusion d ℳ p ℒ x)) = baseInclusion d ℳ p ℒ x
    rw [probeDecompose_base]
    exact DirectSum.coeLinearMap_lof _ _ _
  have hm : (C.comp D).comp ((moduleInclusion d ℳ p ℒ).toLinearMap.comp
      (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap) =
      (moduleInclusion d ℳ p ℒ).toLinearMap.comp
        (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap := by
    apply DirectSum.decompose_lhom_ext (shiftedGrading ℳ d.monoid p)
    intro n
    apply LinearMap.ext
    intro x
    -- Expose evaluation after the coefficient equivalence and homogeneous inclusion.
    change C (D (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm x.val))) =
      moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm x.val)
    rw [probeDecompose_module]
    exact DirectSum.coeLinearMap_lof _ _ _
  apply LinearMap.ext
  intro x
  have hx : x = moduleInclusion d ℳ p ℒ x.left + baseInclusion d ℳ p ℒ x.right := by
    ext <;> simp [moduleInclusion, baseInclusion, LieAlgebra.SemiDirectSum.add_eq_mk]
  -- Express the linear-map identity pointwise using the local names C and D.
  change C (D x) = x
  rw [hx, map_add, map_add]
  apply congrArg₂ (· + ·)
  · simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LieHom.coe_toLinearMap] using
      DFunLike.congr_fun hm ((moduleCoefficientsEquiv d ℳ p) x.left)
  · exact DFunLike.congr_fun hb x.right

private theorem probeDecompose_comp_coe :
    (probeDecompose d ℳ p ℒ).comp
      (DirectSum.coeLinearMap (grading d ℳ p ℒ)) = LinearMap.id := by
  apply DirectSum.linearMap_ext R
  intro a
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply] using
    probeDecompose_of_mem d ℳ p ℒ a x

/-- The two original decompositions identify the probe with the sum of its homogeneous pieces. -/
theorem isInternal_grading : DirectSum.IsInternal (grading d ℳ p ℒ) := by
  let := DirectSum.Decomposition.ofLinearMap _ (probeDecompose d ℳ p ℒ)
    (coe_comp_probeDecompose d ℳ p ℒ) (probeDecompose_comp_coe d ℳ p ℒ)
  exact DirectSum.Decomposition.isInternal _

/-- The original and shifted decompositions combine to decompose the module probe. -/
instance instDecompositionGrading : DirectSum.Decomposition (grading d ℳ p ℒ) :=
  (isInternal_grading d ℳ p ℒ).chooseDecomposition

/-- The charge-zero component of any probe is the corresponding component of its base part. -/
@[simp]
theorem coe_decompose_grading_base (x : ProbeLie d ℳ p ℒ) (q : Γ) :
    (DirectSum.decompose (grading d ℳ p ℒ) x (q, 0, 0) : ProbeLie d ℳ p ℒ) =
      baseInclusion d ℳ p ℒ (DirectSum.decompose ℒ x.right q) := by
  induction x using DirectSum.Decomposition.inductionOn (grading d ℳ p ℒ) with
  | zero =>
    simp only [← LieAlgebra.SemiDirectSum.projr_mk, map_zero, DirectSum.decompose_zero,
      DirectSum.zero_apply, ZeroMemClass.coe_zero]
  | add x y hx hy =>
    have hright : (x + y).right = x.right + y.right :=
      map_add (LieAlgebra.SemiDirectSum.projr _) x y
    simpa only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      hright, map_add] using congrArg₂ (· + ·) hx hy
  | @homogeneous a x =>
    rcases a with ⟨r, c, l⟩
    by_cases h0 : c = 0 ∧ l = 0
    · rcases h0 with ⟨rfl, rfl⟩
      obtain ⟨hl, hr⟩ := (mem_grading_base d ℳ p ℒ r x).mp x.property
      by_cases hq : r = q
      · subst r
        rw [DirectSum.decompose_of_mem_same _ x.property,
          DirectSum.decompose_of_mem_same _ hr]
        apply LieAlgebra.SemiDirectSum.ext <;> simp [hl]
      · rw [DirectSum.decompose_of_mem_ne _ x.property (by simpa using hq),
          DirectSum.decompose_of_mem_ne _ hr hq, map_zero]
    · by_cases h1 : c = 1 ∧ l = 0
      · rcases h1 with ⟨rfl, rfl⟩
        obtain ⟨hr, -⟩ := (mem_grading_module d ℳ p ℒ r x).mp x.property
        rw [DirectSum.decompose_of_mem_ne _ x.property (by simp)]
        simp [hr]
      · have hx : (x : ProbeLie d ℳ p ℒ) = 0 := by
          simpa only [grading, h0, h1, ↓reduceIte, Submodule.mem_bot] using x.property
        rw [hx]
        simp only [← LieAlgebra.SemiDirectSum.projr_mk, map_zero, DirectSum.decompose_zero,
          DirectSum.zero_apply, ZeroMemClass.coe_zero]

/-- The charge-one component of any probe is its shifted coefficient component. -/
@[simp]
theorem coe_decompose_grading_module (x : ProbeLie d ℳ p ℒ) (q : Γ) :
    (DirectSum.decompose (grading d ℳ p ℒ) x (q, 1, 0) : ProbeLie d ℳ p ℒ) =
      moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm
        (DirectSum.decompose (shiftedGrading ℳ d.monoid p)
          (moduleCoefficientsEquiv d ℳ p x.left) (q - p))) := by
  induction x using DirectSum.Decomposition.inductionOn (grading d ℳ p ℒ) with
  | zero =>
    simp only [← LieAlgebra.SemiDirectSum.projl_mk, map_zero, DirectSum.decompose_zero,
      DirectSum.zero_apply, ZeroMemClass.coe_zero]
  | add x y hx hy =>
    have hleft : (x + y).left = x.left + y.left :=
      map_add (LieAlgebra.SemiDirectSum.projl _) x y
    simpa only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      hleft, map_add] using congrArg₂ (· + ·) hx hy
  | @homogeneous a x =>
    rcases a with ⟨r, c, l⟩
    by_cases h0 : c = 0 ∧ l = 0
    · rcases h0 with ⟨rfl, rfl⟩
      obtain ⟨hl, -⟩ := (mem_grading_base d ℳ p ℒ r x).mp x.property
      rw [DirectSum.decompose_of_mem_ne _ x.property (by simp)]
      simp [hl]
    · by_cases h1 : c = 1 ∧ l = 0
      · rcases h1 with ⟨rfl, rfl⟩
        obtain ⟨hr, hl⟩ := (mem_grading_module d ℳ p ℒ r x).mp x.property
        by_cases hq : r = q
        · subst r
          rw [DirectSum.decompose_of_mem_same _ x.property,
            DirectSum.decompose_of_mem_same _ hl]
          apply LieAlgebra.SemiDirectSum.ext <;> simp [hr]
        · rw [DirectSum.decompose_of_mem_ne _ x.property (by simpa using hq),
            DirectSum.decompose_of_mem_ne _ hl (sub_left_inj.ne.mpr hq),
            map_zero, map_zero]
      · have hx : (x : ProbeLie d ℳ p ℒ) = 0 := by
          simpa only [grading, h0, h1, ↓reduceIte, Submodule.mem_bot] using x.property
        rw [hx]
        simp only [← LieAlgebra.SemiDirectSum.projl_mk, map_zero, DirectSum.decompose_zero,
          DirectSum.zero_apply, ZeroMemClass.coe_zero]

/-- All components with charge different from zero and one vanish. -/
@[simp]
theorem coe_decompose_grading_charge (x : ProbeLie d ℳ p ℒ) (q : Γ) (c l : ℤ)
    (hc₀ : c ≠ 0) (hc₁ : c ≠ 1) :
    (DirectSum.decompose (grading d ℳ p ℒ) x (q, c, l) : ProbeLie d ℳ p ℒ) = 0 := by
  have h := (DirectSum.decompose (grading d ℳ p ℒ) x (q, c, l)).property
  simpa only [grading_charge_eq_bot d ℳ p ℒ q c l hc₀ hc₁, Submodule.mem_bot] using h

/-- All components with nonzero final coordinate vanish. -/
@[simp]
theorem coe_decompose_grading_normal (x : ProbeLie d ℳ p ℒ) (q : Γ) (c l : ℤ)
    (hl : l ≠ 0) :
    (DirectSum.decompose (grading d ℳ p ℒ) x (q, c, l) : ProbeLie d ℳ p ℒ) = 0 := by
  have h := (DirectSum.decompose (grading d ℳ p ℒ) x (q, c, l)).property
  simpa only [grading_normal_eq_bot d ℳ p ℒ q c l hl, Submodule.mem_bot] using h

end Mei.ModuleProbe
