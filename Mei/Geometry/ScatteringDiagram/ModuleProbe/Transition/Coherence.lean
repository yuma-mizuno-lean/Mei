/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Transition

/-!
# Coherence of the cutoff sheaf maps

The cutoff morphisms act as identity and compose on sections over every open
domain. Their target domains are compared by the canonical equalities of regular
open images under identity and composite inclusions. These are equalities of
actual sections of the existing coefficient sheaf, not merely equations at
generic endpoints.

The proofs combine `value_coefficientLocalTransition`, relative dense-point
extensionality, and the identity and composition laws for module quotient maps.
No consistency or probe-diagram hypothesis is needed.
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

/-- The identity cutoff map is the identity on every section, with its target
domain expressed as the image under the identity regular-locus inclusion. -/
theorem coefficientLocalTransition_refl (k : ℕ)
    (ν : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ Q, (ν Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (U : Opens (B.adaptedComplex k).regularSpace)
    (s : ((B.adaptedDiagram k ν hν).coefficientLocalSystem ((F).quotient k)).presheaf.obj
      (op U)) :
    (coefficientLocalTransition d ℳ p ℒ H h B (le_refl k) ν hν ν hν).hom.app (op U) s =
      ((B.adaptedDiagram k ν hν).coefficientLocalSystem ((F).quotient k)).presheaf.map
        (homOfLE (show (B.adaptedComplex_isSubdivision (le_refl k)).regularOpenImage U ≤ U
          from (FinitePolyhedralComplex.IsSubdivision.regularOpenImage_refl U).le)).op s := by
  let T := (B.adaptedDiagram k ν hν).coefficientTransport ((F).quotient k)
  let σ := B.adaptedComplex_isSubdivision (le_refl k)
  apply T.section_ext_image T σ.regularInclusion σ.isOpenEmbedding_regularInclusion
    σ.coefficientPointMap (fun _ => rfl) le_rfl
  intro x hx
  have hxU : x.val ∈ U := by
    obtain ⟨y, hy, he⟩ := hx
    exact σ.isOpenEmbedding_regularInclusion.injective he ▸ hy
  rw [value_coefficientLocalTransition d ℳ p ℒ H h B (le_refl k) ν hν ν hν s x hxU,
    DenseBasisTransport.value_restrict]
  simp only [ModuleFiltration.transition_refl, LinearMap.id_apply]
  rfl

/-- Lowering the cutoff in two steps equals lowering it directly on every open
domain. The iterated target section is restricted along the canonical equality
of the direct and iterated open images. -/
theorem coefficientLocalTransition_comp {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m)
    (νk : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hνk : ∀ Q, (νk Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νl : (B.adaptedComplex l).walls → V →ₗ[ℝ] ℝ)
    (hνl : ∀ Q, (νl Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νm : (B.adaptedComplex m).walls → V →ₗ[ℝ] ℝ)
    (hνm : ∀ Q, (νm Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (U : Opens (B.adaptedComplex m).regularSpace)
    (s : ((B.adaptedDiagram m νm hνm).coefficientLocalSystem ((F).quotient m)).presheaf.obj
      (op U)) :
    (coefficientLocalTransition d ℳ p ℒ H h B (hkl.trans hlm) νk hνk νm hνm).hom.app
      (op U) s =
      ((B.adaptedDiagram k νk hνk).coefficientLocalSystem ((F).quotient k)).presheaf.map
        (homOfLE (show
          (B.adaptedComplex_isSubdivision (hkl.trans hlm)).regularOpenImage U ≤
            (B.adaptedComplex_isSubdivision hkl).regularOpenImage
              ((B.adaptedComplex_isSubdivision hlm).regularOpenImage U)
          from ((B.adaptedComplex_isSubdivision hlm).regularOpenImage_trans
            (B.adaptedComplex_isSubdivision hkl) U).le)).op
        ((coefficientLocalTransition d ℳ p ℒ H h B hkl νk hνk νl hνl).hom.app
          (op ((B.adaptedComplex_isSubdivision hlm).regularOpenImage U))
          ((coefficientLocalTransition d ℳ p ℒ H h B hlm νl hνl νm hνm).hom.app
            (op U) s)) := by
  let Tm := (B.adaptedDiagram m νm hνm).coefficientTransport ((F).quotient m)
  let Tk := (B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k)
  let σmk := B.adaptedComplex_isSubdivision (hkl.trans hlm)
  let σml := B.adaptedComplex_isSubdivision hlm
  let σlk := B.adaptedComplex_isSubdivision hkl
  apply Tm.section_ext_image Tk σmk.regularInclusion σmk.isOpenEmbedding_regularInclusion
    σmk.coefficientPointMap (fun _ => rfl) le_rfl
  intro x hx
  have hxU : x.val ∈ U := by
    obtain ⟨y, hy, he⟩ := hx
    exact σmk.isOpenEmbedding_regularInclusion.injective he ▸ hy
  rw [value_coefficientLocalTransition d ℳ p ℒ H h B (hkl.trans hlm)
    νk hνk νm hνm s x hxU]
  dsimp only [Tk]
  erw [DenseBasisTransport.value_restrict]
  have hq : σmk.coefficientPointMap x =
      σlk.coefficientPointMap (σml.coefficientPointMap x) := rfl
  simp only [hq]
  erw [value_coefficientLocalTransition d ℳ p ℒ H h B hkl νk hνk νl hνl _
      (σml.coefficientPointMap x) (by exact ⟨x.val, hxU, rfl⟩),
    value_coefficientLocalTransition d ℳ p ℒ H h B hlm νl hνl νm hνm s x hxU]
  exact (DFunLike.congr_fun ((F).transition_comp hkl hlm) (Tm.value s x hxU)).symm

end Mei.ModuleProbe
