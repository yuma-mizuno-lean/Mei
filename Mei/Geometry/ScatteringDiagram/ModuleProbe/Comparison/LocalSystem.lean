/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.LocalSystem
public import Mei.Geometry.Convex.PolyhedralComplex.GenericPoints

/-!
# Actual weighted ray sums as ambient local-system sections

At finite order, the actual decorated-ray evaluation satisfies chart transport
on a dense generic coefficient locus. Consequently it extends uniquely to the
existing coefficient local system on the full regular locus of the adapted
complex, including regular wall points where an off-wall coefficient is not
itself specified. The generic locus simultaneously avoids a finite family of
exceptional arrangements, and its density is proved geometrically.

The transport equation is derived from the independent probe/ray comparison and
probe transport, rather than assumed of the ray evaluation. The extension does
not assert values on singular strata or on regular points omitted by the chosen
adapted complex. The comparison follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

open TauCeti (WallComplement)

public noncomputable section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

open Set TopologicalSpace Opposite Mei.Convex TauCeti.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')

attribute [local instance] coefficientMulAction

local notation "F" => d.shiftedFiltration ℳ p
local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B

/-- Actual weighted ray values on a dense generic locus obey every adapted
coefficient-chart transport and determine a unique ambient local-system section.
The whole incoming source is used, and no ray transport equation is assumed. -/
theorem existsUnique_weightedRayLocalSection
    (hinitial : ∀ c, D.wall (.inl c) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall c)
    (K : ℕ) (ν : (B.adaptedComplex K).walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ Q, (ν Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (hBc : B.LevelConsistent K) (hD : D.LevelConsistent (K + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) K)
    (hout : ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ D.active (K + 1) →
      (p + n.val, 1) ∈ (D.wall (.inr c)).ray.rayDegrees →
        (D.wall (.inr c)).Outgoing)
    (b : (d.shiftedQuotientGrading ℳ p K).piece 0)
    (hb : d.shiftedQuotientComponent ℳ p p K (by simp only [sub_self, map_zero]; omega)
      b = a) :
    ∃ A : d.cutoff K → ExceptionalArrangement V,
      let T := (B.adaptedDiagram K ν hν).coefficientTransport ((F).quotient K)
      let ray (x : (B.adaptedComplex K).arrangementCoefficientPoints A) :=
        cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl _) b univ x.val.val.val
      (∀ x : (B.adaptedComplex K).arrangementCoefficientPoints A,
        field K hBc ((B.adaptedPathPrefunctor K).obj
          ⟨x.val.val.val, x.val.property⟩) = ray x) ∧
      (∀ (U : Opens (B.adaptedComplex K).regularSpace)
        (hU : U ∈ (B.adaptedComplex K).coefficientCharts)
        (x y : (B.adaptedComplex K).arrangementCoefficientPoints A)
        (hx : x.val.val ∈ U) (hy : y.val.val ∈ U),
        T.transport U (by simpa only [T, FiniteWallDiagram.coefficientTransport_basis] using hU)
          x.val y.val hx hy (ray x) = ray y) ∧
      ∃! s : ((B.adaptedDiagram K ν hν).coefficientLocalSystem ((F).quotient K)).presheaf.obj
        (op (⊤ : Opens (B.adaptedComplex K).regularSpace)),
        ∀ x : (B.adaptedComplex K).arrangementCoefficientPoints A,
          T.value s x.val (by trivial) = ray x := by
  obtain ⟨A, hA⟩ := exists_extendedCoefficientField_eq_cutoffWallEventEvaluation
    d ℳ p ℒ H h h' D₀ a D B hinitial K hBc hD hB hout b hb
  let C := B.adaptedComplex K
  let T := (B.adaptedDiagram K ν hν).coefficientTransport ((F).quotient K)
  let ray (x : C.arrangementCoefficientPoints A) :=
    cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl _) b univ x.val.val.val
  let toBase (x : C.arrangementCoefficientPoints A) :=
    (B.adaptedPathPrefunctor K).obj ⟨x.val.val.val, x.val.property⟩
  have heq (x : C.arrangementCoefficientPoints A) : field K hBc (toBase x) = ray x := by
    obtain ⟨hQ, hvalue⟩ := hA x.val.val.val x.property
    have hx : toBase x = ⟨x.val.val.val, hQ⟩ := by
      apply WallComplement.ext
      simp only [toBase, B.adaptedPathPrefunctor_obj_val]
    exact (congrArg (field K hBc) hx).trans hvalue
  have hparallel (U : Opens C.regularSpace) (hU : U ∈ C.coefficientCharts)
      (x y : C.arrangementCoefficientPoints A) (hx : x.val.val ∈ U) (hy : y.val.val ∈ U) :
      T.transport U (by simpa only [T, FiniteWallDiagram.coefficientTransport_basis] using hU)
          x.val y.val hx hy (ray x) = ray y := by
    let γ := C.coefficientSegment U hU x.val y.val hx hy
    have hp := extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B K hBc
      (toBase x) (toBase y)
    rw [B.levelTransport_eq_levelPathProduct hBc
      ((B.adaptedPathPrefunctor K).mapPath γ.toPath),
      B.levelPathProduct_eq_adaptedDiagram ν hν γ.toPath] at hp
    dsimp only [T]
    rw [FiniteWallDiagram.coefficientTransport_transport,
      FiniteWallDiagram.coefficientPathTransport_apply, ← heq x, ← heq y]
    exact hp.symm
  refine ⟨A, heq, hparallel, ?_⟩
  apply DenseBasisTransport.existsUnique_section_of_dense T
    (fun x : C.arrangementCoefficientPoints A => x.val)
    (C.denseRange_arrangementCoefficientPoints A) ray
  intro U hU x y hx hy
  exact hparallel U
    (by simpa only [T, FiniteWallDiagram.coefficientTransport_basis] using hU) x y hx hy

end Mei.ModuleProbe
