/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventBackwardPart

/-!
# The canonical event inventory as endpoint-step block data

`Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion` provides the common
backward-ray operator `endpointStep` on generic endpoint functions, together
with its degree increase, its nilpotence and the uniqueness of the recursion
`x = source + endpointStep x`. Its block data are arbitrary; this module
supplies them from an actual simultaneous wall event.

For a label `g` at coefficient order `k`, `labelBlock` is the coefficient of the
raising part of the propagation between two retained relative degrees `m` and
`n`: it transports a homogeneous coefficient of ambient degree `p + m` through
`shiftedInclusion`, applies the raising part, and reads the ambient degree
`p + n` component. The two degree facts of
`Mei.Algebra.Lie.Graded.Shifted.Support` then say exactly that this coefficient
is supported on `Precedes`: it vanishes when the degrees agree, and when their
difference is not an allowed degree. A nonzero block therefore forces
`Precedes` and strictly raises the relative degree: this is the finite-level
endpoint-projection raising statement that the `endpointStep` guard of the
endpoint recursion needs.

The specialization to a simultaneous event of a directed diagram is
`eventBlock`, which is the block data of the endpoint recursion carried by the
canonical event inventory. The remaining step of that identification is the
component-sum formula for the raising part, which is not proved here. The degree
bookkeeping follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  (B : DirectedDiagram (d := d) h H ι)

local notation "A" => d.shiftedLieFiltration ℒ ℳ p

section Label

omit [Algebra ℚ R] in
/-- Included homogeneous coefficients have zero retained component in every other
ambient degree. -/
private theorem component_inclusion_of_ne (k : ℕ) {n m : d.cutoff k}
    (hne : p + m.val ≠ p + n.val) (x : ℳ (p + m.val)) :
    d.shiftedQuotientComponent ℳ p (p + n.val) k
      (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)
      (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p
        ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x)) = 0 :=
  d.shiftedQuotientComponent_mk_shiftedInclusion_of_ne (q := p + n.val) (k := k)
    (h := by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)
    (n := ⟨m.val, (d.mem_cutoff.mp m.property).1⟩) (hnq := hne) (x := x)

/-- The raising part of a truncated BCH action annihilates every included
homogeneous coefficient at a degree that is not strictly lower. Both exclusions
are the two degree facts of the associated graded: the unchanged component is
fixed, and a surviving component requires a positive monoid shift. -/
private theorem component_raisingPart_inclusion_eq_zero (k : ℕ)
    (g : d.truncatedGroup ℒ k) {n m : d.cutoff k}
    (hnm : ¬ d.Precedes m.val n.val) (x : ℳ (p + m.val)) :
    d.shiftedQuotientComponent ℳ p (p + n.val) k
      (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)
      (Mei.ModuleFiltration.raisingPart
        ((A).truncatedBCHAction d ℒ k g : Module.End R ((A).quotient k))
        (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p
          ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x))) = 0 := by
  rcases not_and_or.mp hnm with hmn | hmon
  · -- equal relative degrees: the raising part cancels on the unchanged component
    obtain rfl : m = n := Subtype.ext (not_not.mp hmn)
    rw [Mei.ModuleFiltration.raisingPart_apply, map_sub, sub_eq_zero]
    trans (⟨x, x.property⟩ : ℳ (p + m.val))
    · rw [LinearEquiv.coe_coe,
        d.shiftedQuotientComponent_truncatedBCHAction_of_mem_same ℒ ℳ p
        (r := p + m.val)
        (by rw [add_sub_cancel_left]; exact (d.mem_cutoff.mp m.property).1) k g
        (shiftedInclusion ℳ d.monoid p ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x)
        (by simpa only [coe_shiftedInclusion] using x.property)
        (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp m.property).2)]
      exact Subtype.ext (by simp only [coe_shiftedInclusion])
    · rw [d.shiftedQuotientComponent_mk, coe_shiftedInclusion]
      exact Subtype.ext (DirectSum.decompose_of_mem_same ℳ x.property).symm
  · -- a non-allowed degree difference: the component of the action vanishes
    have hc : p + m.val ≠ p + n.val := by
      intro he
      apply hmon
      have h0 : n.val - m.val = 0 := by
        rw [← add_sub_add_left_eq_sub, he, sub_self]
      rw [h0]
      exact d.monoid.zero_mem
    rw [Mei.ModuleFiltration.raisingPart_apply, map_sub,
      component_inclusion_of_ne (d := d) (ℳ := ℳ) (p := p) k hc x, sub_zero]
    by_contra hne
    apply hmon
    have hsub := d.sub_mem_monoid_of_shiftedQuotientComponent_truncatedBCHAction_ne_zero
      (ℒ := ℒ) (ℳ := ℳ) (p := p) (r := p + m.val) (q := p + n.val)
      (by rw [add_sub_cancel_left]; exact (d.mem_cutoff.mp m.property).1) k g
      (shiftedInclusion ℳ d.monoid p ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x)
      (by simpa only [coe_shiftedInclusion] using x.property)
      (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2) hne
    rwa [add_sub_add_left_eq_sub] at hsub

/-- The coefficient of the raising part of a truncated BCH action between two
retained relative degrees. It is the block of the common backward-ray operator
carried by this label. -/
def labelBlock (k : ℕ) (g : d.truncatedGroup ℒ k) (n m : d.cutoff k) :
    ℳ (p + m.val) →ₗ[R] ℳ (p + n.val) :=
  (d.shiftedQuotientComponent ℳ p (p + n.val) k
      (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)).comp
    ((Mei.ModuleFiltration.raisingPart
        ((A).truncatedBCHAction d ℒ k g : Module.End R ((A).quotient k))).comp
      (Submodule.mkQ ((A).submodule (k + 1)) |>.comp
        (shiftedInclusion ℳ d.monoid p ⟨m.val, (d.mem_cutoff.mp m.property).1⟩)))

omit [IsWallAnnihilating H ℳ] in
/-- A block outside the last-change relation vanishes. This is the endpoint-level
form of the degree increase: only strictly lower relative degrees are read. -/
theorem labelBlock_eq_zero_of_not_precedes (k : ℕ) (g : d.truncatedGroup ℒ k)
    {n m : d.cutoff k} (hnm : ¬ d.Precedes m.val n.val) :
    labelBlock d ℳ p ℒ k g n m = 0 := by
  refine LinearMap.ext fun x => ?_
  exact component_raisingPart_inclusion_eq_zero d ℳ p ℒ k g hnm x

omit [IsWallAnnihilating H ℳ] in
/-- A nonzero block forces the last-change relation: the output degree is strictly
higher. This is the finite-level endpoint-projection raising statement, read off the
canonical event inventory. -/
theorem precedes_of_labelBlock_ne_zero (k : ℕ) (g : d.truncatedGroup ℒ k)
    {n m : d.cutoff k} (h : labelBlock d ℳ p ℒ k g n m ≠ 0) :
    d.Precedes m.val n.val := by
  by_contra hnm
  exact h (labelBlock_eq_zero_of_not_precedes (d := d) (ℳ := ℳ) (p := p) (ℒ := ℒ) k g hnm)

omit [IsWallAnnihilating H ℳ] in
/-- A nonzero block strictly raises the relative degree. -/
theorem degree_lt_of_labelBlock_ne_zero (k : ℕ) (g : d.truncatedGroup ℒ k)
    {n m : d.cutoff k} (h : labelBlock d ℳ p ℒ k g n m ≠ 0) :
    d.degree m.val < d.degree n.val :=
  Mei.PositiveDegrees.degree_lt_of_precedes d
    (precedes_of_labelBlock_ne_zero d ℳ p ℒ k g h)

/-- The coefficient of a simultaneous wall event of a directed diagram between two
retained relative degrees, obtained from its truncated label. -/
def eventBlock (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K)) (n m : d.cutoff k) :
    ℳ (p + m.val) →ₗ[R] ℳ (p + n.val) :=
  labelBlock d ℳ p ℒ k
    ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b)) n m

omit [IsWallAnnihilating H ℳ] in
/-- The event block is the reaching part of the canonical event propagation read at
the two relative degrees. -/
theorem eventBlock_eq_labelBlock (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K))
    (n m : d.cutoff k) :
    eventBlock d ℳ p ℒ H h B k K hkK b n m =
      labelBlock d ℳ p ℒ k
        ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b)) n m := (rfl)

omit [IsWallAnnihilating H ℳ] in
/-- Event blocks outside the last-change relation vanish. -/
theorem eventBlock_eq_zero_of_not_precedes (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K)) {n m : d.cutoff k}
    (hnm : ¬ d.Precedes m.val n.val) :
    eventBlock d ℳ p ℒ H h B k K hkK b n m = 0 :=
  labelBlock_eq_zero_of_not_precedes (d := d) (ℳ := ℳ) (p := p) (ℒ := ℒ) k _ hnm

omit [IsWallAnnihilating H ℳ] in
/-- A nonzero event block strictly raises the relative degree. -/
theorem degree_lt_of_eventBlock_ne_zero (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K)) {n m : d.cutoff k}
    (h : eventBlock d ℳ p ℒ H h B k K hkK b n m ≠ 0) :
    d.degree m.val < d.degree n.val :=
  degree_lt_of_labelBlock_ne_zero (d := d) (ℳ := ℳ) (p := p) (ℒ := ℒ) k _ h

end Label

end Mei.ModuleProbe
