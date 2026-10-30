/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.LocalSystem
public import Mei.Geometry.Convex.PolyhedralComplex.RegularSubdivision
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Realization.Truncation
public import Mei.Topology.Sheaves.DenseBasisTransport.Morphism

/-!
# Cutoff maps for probe coefficient sections

Lowering the coefficient order intertwines the actual transport on the adapted
complexes. The fine regular locus embeds openly into the coarse regular locus;
the target sections are restricted to this open image.
-/

-- The transport comparison combines `truncation_pathProduct_adaptedDiagram` with
-- `ModuleFiltration.transition_truncatedBCHAction`.

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
  {k l : ℕ} (hkl : k ≤ l)
  (νk : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
  (hνk : ∀ Q, (νk Q).ker = (affineSpan ℝ (Q : Set V)).direction)
  (νl : (B.adaptedComplex l).walls → V →ₗ[ℝ] ℝ)
  (hνl : ∀ Q, (νl Q).ker = (affineSpan ℝ (Q : Set V)).direction)

local notation "F" => d.shiftedFiltration ℳ p
local notation "A" => d.shiftedLieFiltration ℒ ℳ p

attribute [local instance] coefficientMulAction

/-- Coefficient truncation intertwines fine and coarse chart transport along the
same ambient segment. No consistency or probe diagram is required. -/
theorem transition_coefficientTransport
    (U : Opens (B.adaptedComplex l).regularSpace)
    (hU : U ∈ (B.adaptedComplex l).coefficientCharts)
    (x y : (B.adaptedComplex l).coefficientPoints)
    (hx : x.val ∈ U) (hy : y.val ∈ U) (a : (F).quotient l) :
    (F).transition hkl
      (((B.adaptedDiagram l νl hνl).coefficientTransport ((F).quotient l)).transport
        U (by simpa using hU) x y hx hy a) =
      ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k)).transport
        ((B.adaptedComplex_isSubdivision hkl).regularOpenImage U)
        (by simpa using (B.adaptedComplex_isSubdivision hkl).coefficientChart_regularOpenImage hU)
        ((B.adaptedComplex_isSubdivision hkl).coefficientPointMap x)
        ((B.adaptedComplex_isSubdivision hkl).coefficientPointMap y)
        ((B.adaptedComplex_isSubdivision hkl).coefficientPointMap_mem_regularOpenImage U x hx)
        ((B.adaptedComplex_isSubdivision hkl).coefficientPointMap_mem_regularOpenImage U y hy)
        ((F).transition hkl a) := by
  let s := B.adaptedComplex_isSubdivision hkl
  let γ := (B.adaptedComplex l).coefficientSegment U hU x y hx hy
  let δ := (B.adaptedComplex k).coefficientSegment (s.regularOpenImage U)
    (s.coefficientChart_regularOpenImage hU) (s.coefficientPointMap x) (s.coefficientPointMap y)
    (s.coefficientPointMap_mem_regularOpenImage U x hx)
    (s.coefficientPointMap_mem_regularOpenImage U y hy)
  have hp := B.truncation_pathProduct_adaptedDiagram hkl νk hνk νl hνl
    γ.toPath δ.toPath (by
      simp only [Quiver.Path.vertices_toPath, List.map_cons, List.map_nil,
        FinitePolyhedralComplex.IsSubdivision.coefficientPointMap_val]
      rw [s.regularInclusion_val, s.regularInclusion_val])
  rw [FiniteWallDiagram.coefficientTransport_transport,
    FiniteWallDiagram.coefficientTransport_transport,
    FiniteWallDiagram.coefficientPathTransport_apply,
    FiniteWallDiagram.coefficientPathTransport_apply]
  -- The coefficient action is induced from the truncated BCH representation by
  -- `MulAction.compHom`; expose that representation to apply its truncation law.
  change (F).transition hkl
    ((A).truncatedBCHAction d ℒ l ((B.adaptedDiagram l νl hνl).pathProduct γ.toPath) a) =
    (A).truncatedBCHAction d ℒ k ((B.adaptedDiagram k νk hνk).pathProduct δ.toPath)
      ((F).transition hkl a)
  rw [(A).transition_truncatedBCHAction, hp]

/-- Lower the coefficient order as a morphism of the existing coefficient
sheaves. The coarse sheaf is restricted to the fine regular locus. -/
def coefficientLocalTransition :
    (B.adaptedDiagram l νl hνl).coefficientLocalSystem ((F).quotient l) ⟶
      ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k)).imageRestriction
        (B.adaptedComplex_isSubdivision hkl).regularInclusion
        (B.adaptedComplex_isSubdivision hkl).isOpenEmbedding_regularInclusion :=
  ((B.adaptedDiagram l νl hνl).coefficientTransport ((F).quotient l)).mapOfIntertwining
    ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k))
    (B.adaptedComplex_isSubdivision hkl).regularInclusion
    (B.adaptedComplex_isSubdivision hkl).isOpenEmbedding_regularInclusion
    (B.adaptedComplex_isSubdivision hkl).coefficientPointMap
    (B.adaptedComplex_isSubdivision hkl).coefficientPointMap_val
    ((F).transition hkl)
    (fun U hU => by
      have hU' : U ∈ (B.adaptedComplex l).coefficientCharts := by simpa using hU
      simpa using (B.adaptedComplex_isSubdivision hkl).coefficientChart_regularOpenImage
        hU')
    (fun U hU x y hx hy a => transition_coefficientTransport
      d ℳ p ℒ H h B hkl νk hνk νl hνl U (by simpa using hU) x y hx hy a)

/-- On every fine coefficient point and every open domain, the cutoff morphism
is the original coefficient quotient transition. -/
@[simp]
theorem value_coefficientLocalTransition {U : Opens (B.adaptedComplex l).regularSpace}
    (s : ((B.adaptedDiagram l νl hνl).coefficientLocalSystem ((F).quotient l)).presheaf.obj
      (op U)) (x : (B.adaptedComplex l).coefficientPoints) (hx : x.val ∈ U) :
    ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k)).value
      ((coefficientLocalTransition d ℳ p ℒ H h B hkl νk hνk νl hνl).hom.app (op U) s)
      ((B.adaptedComplex_isSubdivision hkl).coefficientPointMap x)
      ((B.adaptedComplex_isSubdivision hkl).coefficientPointMap_mem_regularOpenImage U x hx) =
        (F).transition hkl
          (((B.adaptedDiagram l νl hνl).coefficientTransport ((F).quotient l)).value s x hx) := by
  exact ((B.adaptedDiagram l νl hνl).coefficientTransport ((F).quotient l)).value_mapOfIntertwining
    ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k))
    (B.adaptedComplex_isSubdivision hkl).regularInclusion
    (B.adaptedComplex_isSubdivision hkl).isOpenEmbedding_regularInclusion
    (B.adaptedComplex_isSubdivision hkl).coefficientPointMap
    (B.adaptedComplex_isSubdivision hkl).coefficientPointMap_val
    ((F).transition hkl)
    (fun U hU => by
      have hU' : U ∈ (B.adaptedComplex l).coefficientCharts := by simpa using hU
      simpa using (B.adaptedComplex_isSubdivision hkl).coefficientChart_regularOpenImage
        hU')
    (fun U hU x y hx hy a => transition_coefficientTransport
      d ℳ p ℒ H h B hkl νk hνk νl hνl U (by simpa using hU) x y hx hy a) s x hx

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  [IsWallAnnihilating H ℳ]
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (hD : D.LevelConsistent (l + 1))
  (hBl : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
    (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) l)

/-- The cutoff sheaf morphism sends the fine probe section to the restriction
of the coarse probe section. No genericity or extra base consistency is assumed. -/
theorem coefficientLocalTransition_section :
    (coefficientLocalTransition d ℳ p ℒ H h B hkl νk hνk νl hνl).hom.app
      (op (⊤ : Opens (B.adaptedComplex l).regularSpace))
      (coefficientLocalSection d ℳ p ℒ H h h' D B l νl hνl hD hBl) =
      ((B.adaptedDiagram k νk hνk).coefficientLocalSystem ((F).quotient k)).presheaf.map
        (homOfLE (show (B.adaptedComplex_isSubdivision hkl).regularOpenImage ⊤ ≤ ⊤
          from le_top)).op
        (coefficientLocalSection d ℳ p ℒ H h h' D B k νk hνk
          (hD.mono (Nat.add_le_add_right hkl 1)) (hBl.mono hkl)) := by
  have hBk := hBl.mono hkl
  have hBcl : B.LevelConsistent l :=
    (cylinderDiagram_levelConsistent_iff d ℳ p ℒ H h h' B l).mp
      (hBl.consistent ((hD.mono (Nat.le_succ l)).map D (chargeZeroGradedLieHom d ℳ p ℒ)
        (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)))
  have hBck : B.LevelConsistent k := hBcl.mono hkl
  apply ((B.adaptedDiagram l νl hνl).coefficientTransport ((F).quotient l)).section_ext_image
    ((B.adaptedDiagram k νk hνk).coefficientTransport ((F).quotient k))
    (B.adaptedComplex_isSubdivision hkl).regularInclusion
    (B.adaptedComplex_isSubdivision hkl).isOpenEmbedding_regularInclusion
    (B.adaptedComplex_isSubdivision hkl).coefficientPointMap
    (B.adaptedComplex_isSubdivision hkl).coefficientPointMap_val le_rfl
  intro x hx
  rw [value_coefficientLocalTransition d ℳ p ℒ H h B hkl νk hνk νl hνl _ x (by trivial),
    DenseBasisTransport.value_restrict,
    value_coefficientLocalSection_eq_extendedCoefficientField
      d ℳ p ℒ H h h' D B l νl hνl hD hBl hBcl x,
    value_coefficientLocalSection_eq_extendedCoefficientField
      d ℳ p ℒ H h h' D B k νk hνk (hD.mono (Nat.add_le_add_right hkl 1)) hBk hBck]
  have he := transition_extendedCoefficientField d ℳ p ℒ H h h' D B hkl hBck hBcl
    hD hBl ((B.adaptedPathPrefunctor l).obj ⟨x.val.val, x.property⟩)
  convert he using 1
  congr 1
  apply WallComplement.ext
  simp only [B.adaptedPathPrefunctor_obj_val, WallComplement.restrictPrefunctor_obj_val,
    FinitePolyhedralComplex.IsSubdivision.coefficientPointMap_val]
  exact (B.adaptedComplex_isSubdivision hkl).regularInclusion_val x.val

end Mei.ModuleProbe
