/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.RelativeCompletion
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Cylinder.Equivalence

/-!
# Independence of extended probe fields from the diagram representative

Equivalent probe diagrams give the same endpoint coefficients even at allowed
base endpoints that lie on the exceptional probe arrangements. The same argument
compares equivalent base presentations: a common generic anchor has equal base
transport. The finite-order comparison passes to the completed shifted module without
separatedness or an all-order generic anchor.

These comparisons express the representative independence of the probe field in
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ κ' : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
local notation "A" => d.shiftedLieFiltration ℒ ℳ p

/-- Equivalent finite probe diagrams have equal extended coefficients at every
allowed base endpoint. Neither endpoint needs to be generic for a probe
arrangement, and the two arrangements need not agree. -/
theorem extendedCoefficientField_eq_of_levelEquivalent {ι' : Type*}
    (D' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) ι') (k : ℕ) (hBc : B.LevelConsistent k)
    (hD : D.LevelConsistent (k + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (hDD' : D.LevelEquivalent D' (k + 1))
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    extendedCoefficientField d ℳ p ℒ H h h' D B k hBc x =
      extendedCoefficientField d ℳ p ℒ H h h' D' B k hBc x := by
  let T := (coefficientArrangement d ℳ p ℒ H h h' D k).union
    (coefficientArrangement d ℳ p ℒ H h h' D' k)
  obtain ⟨z', hzT⟩ := exists_generic_allowed (d := d) (ℒ := ℒ) (H := H)
    (h := h) (B := B) k T x
  obtain ⟨hzD, hzD'⟩ := ExceptionalArrangement.isGeneric_union.mp hzT
  have hB' := ((hDD'.mono (Nat.le_succ k)).map (chargeZeroGradedLieHom d ℳ p ℒ)
    (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).symm.trans hB
  rw [extendedCoefficientField_eq_action d ℳ p ℒ H h h' D B k hBc hD hB x z' hzD,
    extendedCoefficientField_eq_action d ℳ p ℒ H h h' D' B k hBc
      (hDD'.consistent hD) hB' x z' hzD',
    coefficientField_eq_of_levelEquivalent d ℳ p ℒ H h h' D D' k hDD' z'.val hzD hzD']

/-- Equivalent probe presentations define the same completed coefficient at every
all-order allowed base endpoint. Only finite common generic anchors are used. -/
theorem completedExtendedCoefficientField_eq_of_equivalent {ι' : Type*}
    (D' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) ι') (hD : D.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B)) (hDD' : D.Equivalent D') (x : B.Point) :
    completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x =
      completedExtendedCoefficientField d ℳ p ℒ H h h' D' B (hDD'.consistent hD) hBc
        ((hDD'.map (chargeZeroGradedLieHom d ℳ p ℒ)
          (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).symm.trans hB) x := by
  apply (F).completion_ext
  intro k
  rw [projection_completedExtendedCoefficientField, projection_completedExtendedCoefficientField]
  exact extendedCoefficientField_eq_of_levelEquivalent d ℳ p ℒ H h h' D B D' k
    ((B.consistent_iff.mp hBc) k) ((D.consistent_iff.mp hD) (k + 1))
    ((DirectedDiagram.equivalent_iff _ _).mp hB k)
    ((DirectedDiagram.equivalent_iff _ _).mp hDD' (k + 1)) _

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
  have hx'' : x.val ∈ {z : V | ∀ c : B'.active k, z ∉ (B'.wall c).support} := by
    rw [hx]
    exact x'.notMem
  obtain ⟨z, hz, hT⟩ :=
    (coefficientArrangement d ℳ p ℒ H h h' D k).dense_isGeneric.inter_open_nonempty
      _ ((B.isOpen_setOf_forall_notMem_support k).inter
        (B'.isOpen_setOf_forall_notMem_support k)) ⟨x.val, x.notMem, hx''⟩
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

/-- Every relative probe completion has the prescribed cylinder as its
charge-zero part. This comparison follows from the relative-completion witness;
it need not be supplied separately when extracting the completed field. -/
theorem map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
    {η : Type*} (a : ℳ p)
    (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) ((κ ⊕ Unit) ⊕ η))
    (hP : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
      (baseSection d ℳ p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
      (cylinderQuotientDiagram d ℳ p ℒ H h h' B) (probeDiagram d ℳ p ℒ H h h' a) P) :
    (P.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
        (cylinderDiagram d ℳ p ℒ H h h' B) := by
  have hp := hP.map_equivalent
    (hπ := fun _ _ _ hx => baseProjection_mem_baseWallSpaces d ℳ p ℒ H hx)
    (fun x => baseProjection_baseSection d ℳ p ℒ x)
    (fun _ => by simp)
  have hs := hp.map (baseSection d ℳ p ℒ)
    (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
  rwa [map_baseProjection_map_baseSection, cylinderQuotientDiagram_map_baseSection] at hs

/-- Relative completions of the same probe input give the same completed field,
including at endpoints nongeneric for either probe representative. The relative
completion witnesses provide both consistency and the charge-zero comparisons. -/
theorem completedExtendedCoefficientField_eq_of_isRelativeOutgoingCompletion
    {η η' : Type*} (a : ℳ p) (hBc : B.Consistent)
    (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) ((κ ⊕ Unit) ⊕ η))
    (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) ((κ ⊕ Unit) ⊕ η'))
    (hP : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
      (baseSection d ℳ p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
      (cylinderQuotientDiagram d ℳ p ℒ H h h' B) (probeDiagram d ℳ p ℒ H h h' a) P)
    (hP' : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
      (baseSection d ℳ p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
      (cylinderQuotientDiagram d ℳ p ℒ H h h' B) (probeDiagram d ℳ p ℒ H h h' a) P')
    (x : B.Point) :
    completedExtendedCoefficientField d ℳ p ℒ H h h' P B hP.isOutgoingCompletion.consistent hBc
      (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
        d ℳ p ℒ H h h' B a P hP) x =
      completedExtendedCoefficientField d ℳ p ℒ H h h' P' B hP'.isOutgoingCompletion.consistent
        hBc (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
          d ℳ p ℒ H h h' B a P' hP') x := by
  have hPP' := hP.equivalent_of_equivalent hP'
    (DirectedDiagram.Equivalent.refl _) (DirectedDiagram.Equivalent.refl _)
  exact completedExtendedCoefficientField_eq_of_equivalent d ℳ p ℒ H h h' P B P'
    hP.isOutgoingCompletion.consistent hBc
    (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
      d ℳ p ℒ H h h' B a P hP) hPP' x

end Mei.ModuleProbe
