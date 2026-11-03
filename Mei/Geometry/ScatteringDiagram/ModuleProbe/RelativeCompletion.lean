/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.ChargeZero
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Quotient
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat.Relative

/-!
# Completion of a module probe over a fixed consistent cylinder

Let `D` be a consistent diagram on the base. Its cylinder in the module probe lies over `D`
in the base quotient, and the probe wall is a full hyperplane whose label the projection
kills. The relative completion of `DirectedDiagram.exists_isRelativeOutgoingCompletion`
therefore applies, with no condition on the supports of `D`: it adds outgoing walls with
pure birth logarithms in the module summand to the cylinder and the probe wall, keeping
the cylinder walls as the leading summands of the index type. The charge-zero part of the
result is equivalent to the cylinder over `D`.

We use `ModuleProbe.baseProjection`, `ModuleProbe.baseSection`, `ModuleProbe.cylinderDiagram`
and `ModuleProbe.initialDiagram`. The construction follows Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3 and Theorem 2.6
(arXiv:1503.06183v5).
-/

public section
noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)

/-- Completed labels of the base quotient pull back along the section injectively. -/
theorem completedMap_baseSection_injective :
    Function.Injective (baseSection d ℳ p ℒ).completedMap := by
  apply Function.LeftInverse.injective (g := (baseProjection d ℳ p ℒ).completedMap)
  intro g
  rw [← MonoidHom.comp_apply, ← GradedLieHom.completedMap_compId,
    baseProjection_compId_baseSection, GradedLieHom.completedMap_id, MonoidHom.id_apply]

/-- The base projection kills the label of the probe wall. -/
@[simp]
theorem completedMap_baseProjection_probeWall_label (a : ℳ p) :
    (baseProjection d ℳ p ℒ).completedMap (probeWall d ℳ p ℒ H h h' a).label = 1 := by
  apply completedMap_baseSection_injective d ℳ p ℒ
  rw [map_one, ← MonoidHom.comp_apply, ← GradedLieHom.completedMap_compId,
    baseSection_compId_baseProjection, completedMap_chargeZeroGradedLieHom,
    completedBaseProjection_probeWall_label, map_one]

/-- The cylinder over a base diagram, read in the base quotient. -/
def cylinderQuotientDiagram {ι : Type*} (D : DirectedDiagram (d := d) h H ι) :
    DirectedDiagram (d := positiveDegrees d p) (h.prod h') (baseWallSpaces d ℳ p ℒ H) ι :=
  (cylinderDiagram d ℳ p ℒ H h h' D).map (baseProjection d ℳ p ℒ)
    fun _ _ _ hx => baseProjection_mem_baseWallSpaces d ℳ p ℒ H hx

/-- Each wall of the quotient cylinder is the projection of the corresponding cylinder wall. -/
@[simp]
theorem cylinderQuotientDiagram_wall {ι : Type*} (D : DirectedDiagram (d := d) h H ι) (b : ι) :
    (cylinderQuotientDiagram d ℳ p ℒ H h h' D).wall b =
      ((cylinderDiagram d ℳ p ℒ H h h' D).wall b).map (baseProjection d ℳ p ℒ)
        (fun _ _ _ hx => baseProjection_mem_baseWallSpaces d ℳ p ℒ H hx) :=
  DirectedDiagram.map_wall _ _ _ _

/-- Projecting a probe diagram to the base quotient and lifting it along the section forgets
the module summand of every label. -/
theorem map_baseProjection_map_baseSection {ι : Type*}
    (F : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι) :
    (F.map (baseProjection d ℳ p ℒ)
        (fun _ _ _ hx => baseProjection_mem_baseWallSpaces d ℳ p ℒ H hx)).map
        (baseSection d ℳ p ℒ) (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy) =
      F.map (chargeZeroGradedLieHom d ℳ p ℒ) (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H) := by
  apply DirectedDiagram.ext
  funext b
  simp [baseSection_compId_baseProjection]

/-- Forgetting the module summand fixes the cylinder over a base diagram. -/
theorem cylinderDiagram_map_chargeZeroGradedLieHom {ι : Type*}
    (D : DirectedDiagram (d := d) h H ι) :
    (cylinderDiagram d ℳ p ℒ H h h' D).map (chargeZeroGradedLieHom d ℳ p ℒ)
        (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H) = cylinderDiagram d ℳ p ℒ H h h' D := by
  apply DirectedDiagram.ext
  funext b
  simp

/-- Lifting the quotient of a cylinder along the section recovers the cylinder. -/
theorem cylinderQuotientDiagram_map_baseSection {ι : Type*}
    (D : DirectedDiagram (d := d) h H ι) :
    (cylinderQuotientDiagram d ℳ p ℒ H h h' D).map (baseSection d ℳ p ℒ)
        (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy) =
      cylinderDiagram d ℳ p ℒ H h h' D :=
  (map_baseProjection_map_baseSection d ℳ p ℒ H h h' _).trans
    (cylinderDiagram_map_chargeZeroGradedLieHom d ℳ p ℒ H h h' D)

/-- The cylinder over a consistent base diagram is consistent in the base quotient. -/
theorem cylinderQuotientDiagram_consistent {ι : Type*}
    {D : DirectedDiagram (d := d) h H ι} (hD : D.Consistent) :
    (cylinderQuotientDiagram d ℳ p ℒ H h h' D).Consistent :=
  ((cylinderDiagram_consistent_iff d ℳ p ℒ H h h' D).mpr hD).map _ _ _

/-- A consistent base diagram and the probe wall form a relative completion problem:
the supports of the base diagram are arbitrary. -/
theorem isRelativeCompletionInput_cylinderQuotientDiagram {ι : Type*}
    {D : DirectedDiagram (d := d) h H ι} (hD : D.Consistent) (a : ℳ p) :
    DirectedDiagram.IsRelativeCompletionInput (baseProjection d ℳ p ℒ)
      (cylinderQuotientDiagram d ℳ p ℒ H h h' D) (probeDiagram d ℳ p ℒ H h h' a) where
  consistent := cylinderQuotientDiagram_consistent d ℳ p ℒ H h h' hD
  exists_support_eq_hyperplane _ := ⟨0, by ext x; simp⟩
  completedMap_label_eq_one _ := by
    simp

/-- A relative outgoing completion of the cylinder quotient and the probe wall is an outgoing
completion of the initial diagram of the probe. -/
theorem _root_.Mei.DirectedDiagram.IsRelativeOutgoingCompletion.isOutgoingCompletion_initialDiagram
    {ι η : Type*} {D : DirectedDiagram (d := d) h H ι} {a : ℳ p}
    {F : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H)
      ((ι ⊕ Unit) ⊕ η)}
    (hF : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
      (baseSection d ℳ p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
      (cylinderQuotientDiagram d ℳ p ℒ H h h' D) (probeDiagram d ℳ p ℒ H h h' a) F) :
    DirectedDiagram.IsOutgoingCompletion (initialDiagram d ℳ p ℒ H h h' D a).wall F := by
  have := hF.isOutgoingCompletion
  rw [initialDiagram_eq_append_probeDiagram]
  rwa [cylinderQuotientDiagram_map_baseSection] at this

/-- A consistent base diagram and a coefficient at degree `p` have a relative outgoing
completion of the probe that keeps the cylinder fixed and adds only outgoing walls with pure
birth logarithms in the module summand. Its projection to the base quotient is equivalent
to the cylinder quotient, and its charge-zero part is the cylinder over the base diagram. -/
theorem exists_isRelativeOutgoingCompletion_probe [Module.Free ℤ Γ] {ι : Type*}
    {D : DirectedDiagram (d := d) h H ι} (hD : D.Consistent) (a : ℳ p) :
    ∃ (η : Type) (_ : Countable η)
      (F : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H)
        ((ι ⊕ Unit) ⊕ η)),
      DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
        (baseSection d ℳ p ℒ)
        (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
        (cylinderQuotientDiagram d ℳ p ℒ H h h' D) (probeDiagram d ℳ p ℒ H h h' a) F ∧
      (F.map (baseProjection d ℳ p ℒ)
        (fun _ _ _ hx => baseProjection_mem_baseWallSpaces d ℳ p ℒ H hx)).Equivalent
        (cylinderQuotientDiagram d ℳ p ℒ H h h' D) ∧
      (F.map (chargeZeroGradedLieHom d ℳ p ℒ)
        (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
        (cylinderDiagram d ℳ p ℒ H h h' D) := by
  obtain ⟨η, hη, F, hF, hFq⟩ := DirectedDiagram.exists_isRelativeOutgoingCompletion
    (fun x => baseProjection_baseSection d ℳ p ℒ x)
    (isRelativeCompletionInput_cylinderQuotientDiagram d ℳ p ℒ H h h' hD a)
  refine ⟨η, hη, F, hF, hFq, ?_⟩
  have hm := hFq.map (baseSection d ℳ p ℒ)
    (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
  rwa [map_baseProjection_map_baseSection, cylinderQuotientDiagram_map_baseSection] at hm

end Mei.ModuleProbe
