/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Initial
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Projection

/-!
# Classification of module-probe wall labels

Every nonidentity wall label of a module probe has either a lifted base ray and
base normal, or an allowed charge-one ray and a nonzero multiple of the probe
normal. In the latter case the label is the exponential of a unique homogeneous
shifted coefficient. Its first visible cutoff is the relative degree plus one,
and its base projection is trivial. These results apply to arbitrary walls of a
probe completion, without a pure-logarithm hypothesis on its construction.

The classification uses `DirectedWallSpaces.exists_mem_wall_ne_zero_of_mem_wallGroup`
and the defining probe wall spaces. Coefficient extraction uses
`ModuleProbe.moduleRayGroupEquiv` and the completed base projection. The
semidirect probe interpretation follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]

/-- A nonidentity probe wall label is supported either on a lifted base ray with
base normal or on an allowed charge-one ray with a nonzero probe normal. -/
theorem wallGroup_cases_of_ne_one {w : SupportedRay (positiveDegrees d p)}
    {m : (Λ × ℤ × ℤ) →+ ℤ}
    {g : (positiveDegrees d p).completedBCHGroup (grading d ℳ p ℒ)}
    (hg : g ∈ (wallSpaces d ℳ p ℒ H).wallGroup w m) (hne : g ≠ 1) :
    (∃ (v : SupportedRay d) (m₀ : Λ →+ ℤ),
      w = baseRay d p v ∧ m = baseNormal m₀) ∨
    (∃ (q : Γ) (hq : q - p ∈ d.monoid) (c : ℤ),
      c ≠ 0 ∧ w = moduleRay d p q hq ∧ m = c • probeNormal) := by
  obtain ⟨n, hn, x, hx, hx0⟩ :=
    (wallSpaces d ℳ p ℒ H).exists_mem_wall_ne_zero_of_mem_wallGroup hg hne
  rw [wallSpaces_wall] at hx
  rcases (mem_wallSubmodule_iff d ℳ p ℒ H n m x).mp hx with
    hx | ⟨n, m₀, y, rfl, rfl, _, rfl⟩ | ⟨q, c, rfl, hc, rfl, _⟩
  · exact (hx0 hx).elim
  · obtain ⟨v, hv⟩ := exists_baseRay_eq_of_mem_rayDegrees d p w hn
    exact Or.inl ⟨v, m₀, hv, rfl⟩
  · have hq : q - p ∈ d.monoid := by
      simpa using (SupportedRay.mem_rayDegrees.mp hn).1
    exact Or.inr ⟨q, hq, c, hc, eq_moduleRay_of_mem_rayDegrees d p w hq hn, rfl⟩

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (W : DirectedWall (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H))
  (q : Γ) (hq : q - p ∈ d.monoid) (hw : W.ray = moduleRay d p q hq)

/-- The homogeneous shifted coefficient of a charge-one wall label. This is
independent of the sign or integral scale chosen for the wall normal. -/
def wallCoefficient : shiftedGrading ℳ d.monoid p (q - p) :=
  ((moduleRayGroupEquiv d ℳ p ℒ q hq).symm
    ⟨W.label, hw ▸ (wallSpaces d ℳ p ℒ H).wallGroup_le_completedRaySubgroup
      W.ray W.normal W.label_mem⟩).toAdd

/-- Reconstruct a charge-one wall label by exponentiating its homogeneous
coefficient in the abelian ideal of the probe. -/
theorem label_eq_expToCompletion_wallCoefficient :
    W.label = (positiveDegrees d p).expToCompletion (grading d ℳ p ℒ)
      (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm
        (wallCoefficient d ℳ p ℒ H h h' W q hq hw).val)) := by
  have he := congrArg Subtype.val ((moduleRayGroupEquiv d ℳ p ℒ q hq).apply_symm_apply
    ⟨W.label, hw ▸ (wallSpaces d ℳ p ℒ H).wallGroup_le_completedRaySubgroup
      W.ray W.normal W.label_mem⟩)
  simpa only [coe_moduleRayGroupEquiv, wallCoefficient] using he.symm

/-- The coefficient is characterized by its exponential wall label. In
particular, there is no choice of coefficient left by the reconstruction formula. -/
theorem wallCoefficient_eq_iff (a : shiftedGrading ℳ d.monoid p (q - p)) :
    wallCoefficient d ℳ p ℒ H h h' W q hq hw = a ↔
      W.label = (positiveDegrees d p).expToCompletion (grading d ℳ p ℒ)
        (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a.val)) := by
  constructor
  · rintro rfl
    exact label_eq_expToCompletion_wallCoefficient d ℳ p ℒ H h h' W q hq hw
  · intro ha
    apply Multiplicative.ofAdd.injective
    apply (moduleRayGroupEquiv d ℳ p ℒ q hq).injective
    apply Subtype.ext
    simpa only [coe_moduleRayGroupEquiv, toAdd_ofAdd] using
      (label_eq_expToCompletion_wallCoefficient d ℳ p ℒ H h h' W q hq hw).symm.trans ha

/-- A charge-one wall contributes the identity exactly when its coefficient vanishes. -/
@[simp]
theorem wallCoefficient_eq_zero_iff :
    wallCoefficient d ℳ p ℒ H h h' W q hq hw = 0 ↔ W.label = 1 := by
  rw [wallCoefficient_eq_iff]
  simp only [ZeroMemClass.coe_zero, map_zero, PositiveDegrees.expToCompletion_zero]

/-- A finite cutoff sees precisely the nonzero charge-one coefficients whose
relative degree is at most one less than that cutoff. -/
theorem projection_label_eq_one_iff (k : ℕ) :
    CompletedGroup.projection k W.label = 1 ↔
      wallCoefficient d ℳ p ℒ H h h' W q hq hw = 0 ∨
        (k : ℤ) < d.degree (q - p) + 1 := by
  let a := wallCoefficient d ℳ p ℒ H h h' W q hq hw
  have hx := (moduleGradingEquiv d ℳ p ℒ q a).property
  rw [coe_moduleGradingEquiv] at hx
  have hz : moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a.val) = 0 ↔
      a = 0 := by
    rw [map_eq_zero_iff _ (LieAlgebra.SemiDirectSum.inl_injective _),
      LinearEquiv.map_eq_zero_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [label_eq_expToCompletion_wallCoefficient d ℳ p ℒ H h h' W q hq hw,
    (positiveDegrees d p).projection_expToCompletion_eq_one_iff (grading d ℳ p ℒ) hx k,
    hz, positiveDegrees_degree]
  simp only [a, map_sub, mul_one]
  have hd : d.degree q + (1 - d.degree p) = d.degree q - d.degree p + 1 := by ring
  rw [hd]

/-- Extracting the coefficient from the initial probe wall recovers its given
homogeneous input, including a zero input or one with zero spatial velocity. -/
@[simp]
theorem coe_wallCoefficient_probeWall (a : ℳ p) :
    ((wallCoefficient d ℳ p ℒ H h h' (probeWall d ℳ p ℒ H h h' a)
      p (by simp) (probeWall_ray d ℳ p ℒ H h h' a)).val : M) = a.val := by
  let a₀ : shiftedGrading ℳ d.monoid p (p - p) :=
    ⟨⟨a, le_shiftedSubmodule ℳ d.monoid p (n := 0) (zero_mem _) (by simp)⟩,
      (mem_shiftedGrading ℳ d.monoid p).mpr (by simp)⟩
  have he : wallCoefficient d ℳ p ℒ H h h' (probeWall d ℳ p ℒ H h h' a)
      p (by simp) (probeWall_ray d ℳ p ℒ H h h' a) = a₀ := by
    apply (wallCoefficient_eq_iff d ℳ p ℒ H h h' _ p _ _ a₀).mpr
    exact probeWall_label d ℳ p ℒ H h h' a
  exact congrArg (fun b : shiftedGrading ℳ d.monoid p (p - p) => (b.val : M)) he

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Every wall whose normal is not a lifted base normal disappears under base
projection. This also covers identity labels on otherwise unrestricted rays. -/
theorem completedBaseProjection_label_eq_one_of_normal_notMem_range
    (hm : W.normal ∉ Set.range (baseNormal (Λ := Λ))) :
    completedBaseProjection d ℳ p ℒ W.label = 1 := by
  by_cases he : W.label = 1
  · simp [he]
  rcases wallGroup_cases_of_ne_one d ℳ p ℒ H W.label_mem he with
    ⟨v, m, _, hm'⟩ | ⟨q, hq, c, _, hw, _⟩
  · exact (hm ⟨m, hm'.symm⟩).elim
  · rw [label_eq_expToCompletion_wallCoefficient d ℳ p ℒ H h h' W q hq hw,
      completedBaseProjection_expToCompletion]
    simp [moduleInclusion]

end Mei.ModuleProbe
