/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison.Stable
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Cylinder.Equivalence
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension.Equivalence
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.RelativeCompletion
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Stable

/-!
# Independence of ray sums from the wall presentation

Two equivalent consistent base diagrams may present the same scattering diagram by
different wall families, for instance after subdividing supports or merging coincident
walls. Their probe fields, extracted from one probe completion, agree at every endpoint
allowed for both presentations, at each finite cutoff and in the completion: base transport
is the same along common ambient paths.

The actual weighted sums of decorated rays through the two presentations, with the whole
space as incoming source, then agree at every endpoint where both sums are locally constant.
The comparison goes through the independently constructed relative completion of the probe
and its probe field, and never compares the broken lines of the two presentations. The
wall families, their encounter itineraries and their decorated types differ between the
presentations; only the total sums are compared.

The probe construction follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

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
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (B : DirectedDiagram (d := d) h H κ) (B' : DirectedDiagram (d := d) h H κ')

local notation "F" => d.shiftedFiltration ℳ p

/-- Equivalent base presentations give equal finite probe coefficients at every endpoint
allowed for both, since both are the same base transport of one generic probe coefficient.
Neither endpoint needs to be generic for the probe arrangement. -/
theorem extendedCoefficientField_eq_of_levelEquivalent_base (k : ℕ)
    (hBB' : B.LevelEquivalent B' k) (hBc : B.LevelConsistent k) (hBc' : B'.LevelConsistent k)
    (hD : D.LevelConsistent (k + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (x : WallComplement (fun c : B.active k => (B.wall c).support))
    (x' : WallComplement (fun c : B'.active k => (B'.wall c).support)) (hx : x.val = x'.val) :
    extendedCoefficientField d ℳ p ℒ H h h' D B k hBc x =
      extendedCoefficientField d ℳ p ℒ H h h' D B' k hBc' x' := by
  let := h.finiteDimensional
  have hB' := hB.trans (hBB'.cylinderDiagram d ℳ p ℒ H h h')
  have hopen (C : DirectedDiagram (d := d) h H κ) :
      IsOpen {z : V | ∀ c : C.active k, z ∉ (C.wall c).support} := by
    simpa only [ofPred_forall, compl_def] using isOpen_iInter_of_finite
      (fun c : C.active k => (C.wall c).isConvexPolyhedron.isClosed.isOpen_compl)
  have hopen' : IsOpen {z : V | ∀ c : B'.active k, z ∉ (B'.wall c).support} := by
    simpa only [ofPred_forall, compl_def] using isOpen_iInter_of_finite
      (fun c : B'.active k => (B'.wall c).isConvexPolyhedron.isClosed.isOpen_compl)
  have hx'' : x.val ∈ {z : V | ∀ c : B'.active k, z ∉ (B'.wall c).support} := by
    rw [hx]
    exact x'.notMem
  obtain ⟨z, hz, hT⟩ :=
    (coefficientArrangement d ℳ p ℒ H h h' D k).dense_isGeneric.inter_open_nonempty
      _ ((hopen B).inter hopen') ⟨x.val, x.notMem, hx''⟩
  rw [extendedCoefficientField_eq_action d ℳ p ℒ H h h' D B k hBc hD hB x ⟨z, hz.1⟩ hT,
    extendedCoefficientField_eq_action d ℳ p ℒ H h h' D B' k hBc' hD hB' x' ⟨z, hz.2⟩ hT,
    hBB'.levelTransport_eq hBc hBc' (x := ⟨z, hz.1⟩) (x' := ⟨z, hz.2⟩) rfl hx]

/-- Equivalent base presentations give equal completed probe coefficients at every
all-order endpoint allowed for both presentations. -/
theorem completedExtendedCoefficientField_eq_of_equivalent_base (hBB' : B.Equivalent B')
    (hD : D.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    (x : B.Point) (x' : B'.Point) (hx : x.val = x'.val) :
    completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x =
      completedExtendedCoefficientField d ℳ p ℒ H h h' D B' hD (hBB'.consistent hBc)
        (hB.trans (hBB'.cylinderDiagram d ℳ p ℒ H h h')) x' := by
  apply (F).completion_ext
  intro k
  rw [projection_completedExtendedCoefficientField, projection_completedExtendedCoefficientField]
  exact extendedCoefficientField_eq_of_levelEquivalent_base d ℳ p ℒ H h h' D B B' k
    ((DirectedDiagram.equivalent_iff _ _).mp hBB' k) ((B.consistent_iff.mp hBc) k)
    ((B'.consistent_iff.mp (hBB'.consistent hBc)) k) ((D.consistent_iff.mp hD) (k + 1))
    ((DirectedDiagram.equivalent_iff _ _).mp hB k) _ _ hx

variable [Module.Free ℤ Γ]

/-- The weighted sums of actual decorated rays are independent of the wall presentation.
For equivalent presentations `B` and `B'` of a consistent diagram, and an incoming
homogeneous coefficient `b`, the total sums over all rays through the walls of `B` and
through the walls of `B'`, with the whole space as incoming source, agree at every endpoint
allowed for both presentations where each sum is locally constant. -/
theorem cutoffWallEventEvaluation_eq_of_equivalent (hB : B.Consistent) (hBB' : B.Equivalent B')
    (K : ℕ) (b : (d.shiftedQuotientGrading ℳ p K).piece 0) {x : V}
    (hx : x ∈ stableWallEventLocus d ℳ p ℒ H h B K b)
    (hx' : x ∈ stableWallEventLocus d ℳ p ℒ H h B' K b) :
    cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ x =
      cutoffWallEventEvaluation d ℳ p ℒ H h B' K K (Nat.le_refl K) b univ x := by
  have h₀ : TauCeti.Toric.IsIntegralLattice (Int.castAddHom ℝ) :=
    TauCeti.Toric.isIntegralLattice_of_basis (Module.Basis.singleton Unit ℤ)
      (Module.Basis.singleton Unit ℝ) (fun _ => by simp)
  obtain ⟨η, -, P, hP, -, -⟩ := exists_isRelativeOutgoingCompletion_probe d ℳ p ℒ H h h₀ hB
    (d.shiftedQuotientComponent ℳ p p K (by simp) b)
  rw [mem_stableWallEventLocus] at hx hx'
  have hcomp := hP.isOutgoingCompletion_initialDiagram
  have hPc := (P.consistent_iff.mp hcomp.consistent) (K + 1)
  have hBc := (B.consistent_iff.mp hB) K
  have hBc' := (B'.consistent_iff.mp (hBB'.consistent hB)) K
  have hBK := (DirectedDiagram.equivalent_iff _ _).mp
    (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
      d ℳ p ℒ H h h₀ B _ P hP) K
  have hBK' := hBK.trans
    (((DirectedDiagram.equivalent_iff _ _).mp hBB' K).cylinderDiagram d ℳ p ℒ H h h₀)
  have hout : ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ P.active (K + 1) →
      (p + n.val, 1) ∈ (P.wall (.inr c)).ray.rayDegrees → (P.wall (.inr c)).Outgoing :=
    fun _ c _ _ => hcomp.outgoing_inr c
  rw [← extendedCoefficientField_eq_cutoffWallEventEvaluation_of_eventually_eq d ℳ p ℒ H h h₀ B
      _ P B hcomp.wall_inl K hBc hPc hBK hout b rfl ⟨x, hx.1⟩ hx.2,
    ← extendedCoefficientField_eq_cutoffWallEventEvaluation_of_eventually_eq d ℳ p ℒ H h h₀ B
      _ P B' hcomp.wall_inl K hBc' hPc hBK' hout b rfl ⟨x, hx'.1⟩ hx'.2]
  exact extendedCoefficientField_eq_of_levelEquivalent_base d ℳ p ℒ H h h₀ P B B' K
    ((DirectedDiagram.equivalent_iff _ _).mp hBB' K) hBc hBc' hPc hBK _ _ rfl

end Mei.ModuleProbe
