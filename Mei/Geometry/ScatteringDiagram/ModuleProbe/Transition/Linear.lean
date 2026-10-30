/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Transition
public import Mei.Geometry.ScatteringDiagram.Coefficient.Linear
public import Mei.Topology.Sheaves.DenseBasisTransport.Linear.Intertwiner

/-!
# Linear cutoff transport of actual probe sections

The finite BCH action is linear on each shifted coefficient quotient. Thus the
existing cutoff maps of probe local systems are linear maps on their actual
sections. We bundle their transport data as coefficient intertwiners, so their
composition is controlled by the general whole-section composition law.

The constructed probe section is preserved by these linear cutoff maps. This
connects the functorial transport API to the finite probe sections that must
form a compatible inverse system before passing to completed theta sections.
Identification of the probe section with the weighted broken-line sum remains
separate.
-/

public noncomputable section

open Set CategoryTheory TopologicalSpace Opposite Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V : Type*} {M L : Type u} {κ : Type*}
  [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Λ]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H κ)

local notation "F" => d.shiftedFiltration ℳ p

attribute [local instance] coefficientMulAction

/-- The concrete cutoff transport, bundled with its linear coefficient map. -/
def coefficientTransitionIntertwiner {k l : ℕ} (hkl : k ≤ l)
    (νk : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hνk : ∀ Q, (νk Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νl : (B.adaptedComplex l).walls → V →ₗ[ℝ] ℝ)
    (hνl : ∀ Q, (νl Q).ker = (affineSpan ℝ (Q : Set V)).direction) :
    ((B.adaptedDiagram l νl hνl).coefficientTransport ((F).quotient l)).SemilinearIntertwiner
      ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k)) (RingHom.id R)
      (B.adaptedComplex_isSubdivision hkl).regularInclusion
      (B.adaptedComplex_isSubdivision hkl).isOpenEmbedding_regularInclusion where
  mapPoint := (B.adaptedComplex_isSubdivision hkl).coefficientPointMap
  mapPoint_val := (B.adaptedComplex_isSubdivision hkl).coefficientPointMap_val
  mapCoefficients := (F).transition hkl
  map_basis U hU := by
    have hU' : U ∈ (B.adaptedComplex l).coefficientCharts := by simpa using hU
    simpa using (B.adaptedComplex_isSubdivision hkl).coefficientChart_regularOpenImage hU'
  map_transport U hU x y hx hy a :=
    transition_coefficientTransport d ℳ p ℒ H h B hkl νk hνk νl hνl U
      (by simpa using hU) x y hx hy a

/-- The concrete intertwiner uses the original quotient transition on coefficients. -/
@[simp]
theorem coefficientTransitionIntertwiner_mapCoefficients {k l : ℕ} (hkl : k ≤ l)
    (νk : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hνk : ∀ Q, (νk Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νl : (B.adaptedComplex l).walls → V →ₗ[ℝ] ℝ)
    (hνl : ∀ Q, (νl Q).ker = (affineSpan ℝ (Q : Set V)).direction) :
    (coefficientTransitionIntertwiner d ℳ p ℒ H h B hkl νk hνk νl hνl).mapCoefficients =
      (F).transition hkl := by rfl

/-- The linear map has exactly the original cutoff morphism as its underlying function. -/
theorem coefficientTransitionIntertwiner_sections {k l : ℕ} (hkl : k ≤ l)
    (νk : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hνk : ∀ Q, (νk Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νl : (B.adaptedComplex l).walls → V →ₗ[ℝ] ℝ)
    (hνl : ∀ Q, (νl Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (U : Opens (B.adaptedComplex l).regularSpace)
    (s : ((B.adaptedDiagram l νl hνl).coefficientLocalSystem ((F).quotient l)).presheaf.obj
      (op U)) :
    (coefficientTransitionIntertwiner d ℳ p ℒ H h B hkl νk hνk νl hνl).sections U s =
      (coefficientLocalTransition d ℳ p ℒ H h B hkl νk hνk νl hνl).hom.app (op U) s := by
  let Tl := (B.adaptedDiagram l νl hνl).coefficientTransport ((F).quotient l)
  let Tk := (B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k)
  let σ := B.adaptedComplex_isSubdivision hkl
  apply Tl.section_ext_image Tk σ.regularInclusion σ.isOpenEmbedding_regularInclusion
    σ.coefficientPointMap σ.coefficientPointMap_val le_rfl
  intro x hx
  have hxU : x.val ∈ U := σ.isOpenEmbedding_regularInclusion.injective.mem_set_image.mp
    (σ.coefficientPointMap_val x ▸ hx)
  have hv := (coefficientTransitionIntertwiner d ℳ p ℒ H h B hkl νk hνk νl hνl).value_sections
    U s x hxU
  exact hv.trans (value_coefficientLocalTransition d ℳ p ℒ H h B
    hkl νk hνk νl hνl s x hxU).symm


variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  [IsWallAnnihilating H ℳ]
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)

/-- The linear cutoff map preserves the actual probe coefficient section. -/
theorem coefficientTransitionIntertwiner_section {k l : ℕ} (hkl : k ≤ l)
    (νk : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hνk : ∀ Q, (νk Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νl : (B.adaptedComplex l).walls → V →ₗ[ℝ] ℝ)
    (hνl : ∀ Q, (νl Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (hD : D.LevelConsistent (l + 1))
    (hBl : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
        (cylinderDiagram d ℳ p ℒ H h h' B) l) :
    (coefficientTransitionIntertwiner d ℳ p ℒ H h B hkl νk hνk νl hνl).sections ⊤
      (coefficientLocalSection d ℳ p ℒ H h h' D B l νl hνl hD hBl) =
      ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k)).restrictionLinearMap
        R le_top (coefficientLocalSection d ℳ p ℒ H h h' D B k νk hνk
          (hD.mono (Nat.add_le_add_right hkl 1)) (hBl.mono hkl)) := by
  rw [coefficientTransitionIntertwiner_sections, DenseBasisTransport.restrictionLinearMap_apply]
  exact coefficientLocalTransition_section d ℳ p ℒ H h B hkl νk hνk νl hνl h' D hD hBl

/-- Factoring a cutoff into two coefficient changes preserves the same actual
probe section, on the whole composite open image. This uses the general
whole-section composition law, including points missing from the fine coefficient domain. -/
theorem coefficientTransitionIntertwiner_comp_section {k l m : ℕ}
    (hkl : k ≤ l) (hlm : l ≤ m)
    (νk : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hνk : ∀ Q, (νk Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νl : (B.adaptedComplex l).walls → V →ₗ[ℝ] ℝ)
    (hνl : ∀ Q, (νl Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νm : (B.adaptedComplex m).walls → V →ₗ[ℝ] ℝ)
    (hνm : ∀ Q, (νm Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (hD : D.LevelConsistent (m + 1))
    (hBm : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
        (cylinderDiagram d ℳ p ℒ H h h' B) m) :
    ((coefficientTransitionIntertwiner d ℳ p ℒ H h B hkl νk hνk νl hνl).comp
      (coefficientTransitionIntertwiner d ℳ p ℒ H h B hlm νl hνl νm hνm)).sections ⊤
      (coefficientLocalSection d ℳ p ℒ H h h' D B m νm hνm hD hBm) =
      ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k)).restrictionLinearMap
        R le_top (coefficientLocalSection d ℳ p ℒ H h h' D B k νk hνk
          (hD.mono (Nat.add_le_add_right (hkl.trans hlm) 1))
          (hBm.mono (hkl.trans hlm))) := by
  rw [DenseBasisTransport.SemilinearIntertwiner.sections_comp]
  simp only [LinearMap.comp_apply]
  rw [coefficientTransitionIntertwiner_section d ℳ p ℒ H h B h' D hlm
    νl hνl νm hνm hD hBm]
  rw [DenseBasisTransport.SemilinearIntertwiner.sections_restrict]
  rw [coefficientTransitionIntertwiner_section d ℳ p ℒ H h B h' D hkl
    νk hνk νl hνl (hD.mono (Nat.add_le_add_right hlm 1)) (hBm.mono hlm)]
  apply DenseBasisTransport.section_ext
  intro x hx
  -- Default transparency identifies the concrete coefficient sheaf with its transport sheaf.
  erw [DenseBasisTransport.value_restrictionLinearMap,
    DenseBasisTransport.value_restrictionLinearMap,
    DenseBasisTransport.value_restrictionLinearMap,
    DenseBasisTransport.value_restrictionLinearMap]

end Mei.ModuleProbe
