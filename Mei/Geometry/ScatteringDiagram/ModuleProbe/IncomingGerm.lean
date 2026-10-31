/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension
public import Mei.Geometry.Convex.Polyhedron.Path.Germ
public import Mei.Geometry.Affine.IncomingGerm

/-!
# Probe values on generic incoming germs

Straight incoming germs and generic perturbations with the same incident normal
signs have identical probe coefficients. One arbitrarily small perturbation works
for finitely many directions at every regular base point, and for any prescribed
finite exceptional arrangement. The signed combined wall action transports this
generic incoming value to the opposite straight germ.

These are whole coefficient identities, so they also identify every homogeneous
input in the lower-degree crossing recursion, including coefficient degrees with
the same spatial direction. We combine the wall-free germ comparison with
`ModuleProbe.extendedCoefficientField_eq_transport`,
`ExceptionalArrangement.exists_norm_lt_forall_eventually_isGeneric`, and the
short-crossing realization of `DirectedDiagram.combinedLabel`. The incoming-germ
interpretation follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (B : DirectedDiagram (d := d) h H κ)

local notation "A" => d.shiftedLieFiltration ℒ ℳ p
local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B

/-- Incoming affine germs with matching strict incident normal signs have the
same whole extended probe coefficient. Their base point may be singular. -/
theorem eventually_exists_extendedCoefficientField_eq_of_mul_pos
    (k : ℕ) (hBc : B.LevelConsistent k) (θ v w : V)
    (hsign : ∀ c : B.active k, θ ∈ (B.wall c).support →
      0 < h.realCharacter (B.wall c).normal v * h.realCharacter (B.wall c).normal w) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∃ x y : WallComplement (fun c : B.active k => (B.wall c).support),
        x.val = θ + ε • v ∧ y.val = θ + ε • w ∧ field k hBc y = field k hBc x := by
  filter_upwards [eventually_exists_crossings_eq_empty_of_mul_pos
    (fun c : B.active k => (B.wall c).isConvexPolyhedron.isClosed)
    (fun c => h.realCharacter (B.wall c).normal)
    (fun c => (B.wall c).direction_support.le) θ v w hsign] with ε hε
  obtain ⟨x, y, hx, hy, hmiss⟩ := hε
  let e : x ⟶ y := ⟨.of_crossings_eq_empty
    (fun c => (B.wall c).isConvexPolyhedron.isClosed) hmiss⟩
  refine ⟨x, y, hx, hy, ?_⟩
  rw [extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B k hBc x y,
    B.levelTransport_eq_levelPathProduct hBc e.toPath,
    B.levelPathProduct_eq_one_of_crossings_eq_empty k e hmiss, map_one]
  simp

/-- One arbitrarily small perturbation makes the incoming germs of finitely
many directions generic for any finite exceptional refinement. At every regular
transverse base point their values equal the straight incoming values, and the
combined signed crossing transports them to the opposite straight germs.
The perturbation is independent of the base point; the eventual bound may vary. -/
theorem exists_norm_lt_forall_eventually_extendedCoefficientField_eq
    (k : ℕ) (hBc : B.LevelConsistent k) (T : ExceptionalArrangement V)
    {η : Type*} [Finite η] (v : η → V) {s : ℝ} (hs : 0 < s) :
    ∃ r : V, ‖r‖ < s ∧
      (∀ a (c : B.active k), h.realCharacter (B.wall c).normal (v a) ≠ 0 →
        0 < h.realCharacter (B.wall c).normal (v a + r) *
          h.realCharacter (B.wall c).normal (v a)) ∧
      ∀ θ a (hθ : θ ∉ singularSupport (fun c : B.active k => (B.wall c).support)),
        (∀ c : B.active k, θ ∈ (B.wall c).support →
          h.realCharacter (B.wall c).normal (v a) ≠ 0) →
        ∀ᶠ ε : ℝ in 𝓝[>] 0,
          ∃ x y z : WallComplement (fun c : B.active k => (B.wall c).support),
            x.val = θ + ε • v a ∧ y.val = θ + ε • (v a + r) ∧
            z.val = θ - ε • v a ∧ T.IsGeneric y.val ∧
            field k hBc y = field k hBc x ∧
            field k hBc z = (A).truncatedBCHAction d ℒ k
              (B.combinedLabel k θ (-v a) hθ) (field k hBc y) := by
  let := h.finiteDimensional
  obtain ⟨r, hr, hsign, -, hgeneric⟩ :=
    T.exists_norm_lt_forall_eventually_isGeneric v
      (fun c : B.active k => (h.realCharacter (B.wall c).normal).toContinuousLinearMap) hs
  simp only [LinearMap.coe_toContinuousLinearMap'] at hsign
  refine ⟨r, hr, hsign, fun θ a hθ hv => ?_⟩
  have hsame := eventually_exists_extendedCoefficientField_eq_of_mul_pos
    d ℳ p ℒ H h h' D B k hBc θ (v a) (v a + r)
      (fun c hc => by simpa only [mul_comm] using hsign a c (hv c hc))
  have hcross := B.eventually_exists_levelPathProduct_eq_combinedLabel k θ (-v a) hθ
    (fun c hc => by simpa only [map_neg, neg_ne_zero] using hv c hc)
  filter_upwards [hsame, hgeneric θ, hcross] with ε heq hgen hε
  obtain ⟨x, y, hx, hy, hxy⟩ := heq
  obtain ⟨x', z, e, hx', hz, he⟩ := hε
  have hxx : x' = x := by
    apply WallComplement.ext
    simpa only [hx, smul_neg, sub_neg_eq_add] using hx'
  subst x'
  refine ⟨x, y, z, hx, hy, by simpa only [smul_neg, sub_eq_add_neg] using hz,
    by simpa only [hy, vadd_eq_add, add_comm] using hgen a, hxy, ?_⟩
  rw [extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B k hBc x z,
    B.levelTransport_eq_levelPathProduct hBc e.toPath, he, hxy]

end Mei.ModuleProbe
