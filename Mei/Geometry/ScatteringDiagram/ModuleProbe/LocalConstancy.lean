/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Crossing
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalConstancy

/-!
# Local constancy of vertical probe coefficients

At a vertically transverse regular point, every incident active wall has normal
a nonzero multiple of the probe normal. Displacements within the probe slice are
therefore tangent to every incident wall. Near the point they preserve regularity,
vertical transversality and the extracted coefficient. In particular the vertical
coefficient is locally constant on the vertically transverse regular locus in
each fixed auxiliary-coordinate slice. Consistency is not needed for these local statements.
The real probe normal is the probe coordinate of the auxiliary factor.

We use the normal classification of `ModuleProbe.wallGroup_cases_of_ne_one`,
the local combined-label theorem and `ModuleProbe.verticalCoefficient`.
The coefficient-field interpretation follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)

local notation "v" => (0, j (0, 1))
local notation "S" => LinearMap.ker
  (TauCeti.Toric.IsIntegralLattice.realCharacter
    (TauCeti.Toric.IsIntegralLattice.prod h h') (probeNormal (Λ := Λ)))

/-- Near a vertically transverse regular germ, small displacements within the
probe slice preserve regularity, vertical transversality and the coefficient.
Both base coordinates and the auxiliary height may vary. -/
theorem eventually_verticalCoefficient_add_eq (k : ℕ) (θ : V × E)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
    (hv : ∀ a : D.active (k + 1), θ ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0) :
    ∀ᶠ w : S in 𝓝 0,
      ∃ hη : θ + (w : V × E) ∉ singularSupport
          (fun a : D.active (k + 1) => (D.wall a).support),
        (∀ a : D.active (k + 1), θ + (w : V × E) ∈ (D.wall a).support →
          (h.prod h').realCharacter (D.wall a).normal v ≠ 0) ∧
        verticalCoefficient d ℳ p ℒ H h h' D k (θ + (w : V × E)) hη =
          verticalCoefficient d ℳ p ℒ H h h' D k θ hθ := by
  have htangent (a : D.active (k + 1)) (ha : θ ∈ (D.wall a).support) :
      S ≤ (affineSpan ℝ (D.wall a).support).direction := by
    rw [(D.wall a).direction_support]
    rcases wallGroup_cases_of_ne_one d ℳ p ℒ H (D.wall a).label_mem
      (D.label_ne_one_of_mem_active a.property) with
      ⟨r, m, _, hm⟩ | ⟨q, hq, c, _, _, hm⟩
    · exact (hv a ha (by simp [hm])).elim
    · intro w hw
      simp only [LinearMap.mem_ker] at hw ⊢
      simp [hm, hw]
  filter_upwards [D.eventually_combinedLabel_add_eq (k + 1) θ hθ S htangent,
    eventually_mem_iff_of_submodule_le_direction
      (fun a : D.active (k + 1) => (D.wall a).support)
      (fun a => (D.wall a).isConvexPolyhedron.isClosed) θ hθ S htangent] with w hw hmem
  obtain ⟨hη, he⟩ := hw
  refine ⟨hη, fun a ha => hv a ((hmem a).mp ha), ?_⟩
  simp only [verticalCoefficient_def, he]

omit [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ] in
/-- The real probe normal reads the probe coordinate of the auxiliary factor; in
particular it vanishes on the base factor and on the height direction. -/
theorem realCharacter_probeNormal :
    (h.prod h').realCharacter (probeNormal (Λ := Λ)) =
      (h'.realCharacter (AddMonoidHom.snd ℤ ℤ)).comp (LinearMap.snd ℝ V E) := by
  symm
  apply (h.prod h').eq_realCharacter
  rintro ⟨a, b, c⟩
  simp

/-- On each fixed auxiliary-coordinate slice, the vertical coefficient is locally
constant on the vertically transverse regular locus. This includes regular points
off the module walls, whose coefficient is zero. -/
theorem isLocallyConstant_verticalCoefficient (k : ℕ) (η : E) :
    IsLocallyConstant (fun Q : {Q : V //
        (Q, η) ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support) ∧
        ∀ a : D.active (k + 1), (Q, η) ∈ (D.wall a).support →
          (h.prod h').realCharacter (D.wall a).normal v ≠ 0} =>
      verticalCoefficient d ℳ p ℒ H h h' D k (Q.val, η) Q.property.1) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro Q
  let displacement (x : V) : S := ⟨(x - Q.val, 0), by
    simp [LinearMap.mem_ker, realCharacter_probeNormal h h']⟩
  have hd : Continuous displacement := by
    fun_prop
  have hd0 : displacement Q.val = 0 := Subtype.ext (by simp [displacement])
  have ht : Tendsto (fun Q' : {Q' : V //
        (Q', η) ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support) ∧
        ∀ a : D.active (k + 1), (Q', η) ∈ (D.wall a).support →
          (h.prod h').realCharacter (D.wall a).normal v ≠ 0} => displacement Q'.val)
      (𝓝 Q) (𝓝 0) := by
    simpa only [Function.comp_def, hd0] using (hd.comp continuous_subtype_val).tendsto Q
  filter_upwards [ht.eventually (eventually_verticalCoefficient_add_eq
    d ℳ p ℒ H h h' D k (Q.val, η) Q.property.1 Q.property.2)] with Q' hQ'
  obtain ⟨hreg, _, he⟩ := hQ'
  simpa only [displacement, Prod.mk_add_mk, add_sub_cancel, add_zero] using he

end Mei.ModuleProbe
