/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Classification
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Germ

/-!
# Coefficients of vertical probe crossings

At a regular point transverse to the upward probe direction, every incident
active wall is a module wall. Its combined crossing label lies in the kernel
of base projection and therefore determines a unique shifted coefficient.
With positive probe coorientation this coefficient has negative exponential
as the upward path product. Arbitrarily short segments realize that product.
The coefficients commute with truncation and agree for equivalent diagrams.

The construction uses `ModuleProbe.completedBaseProjection_label_eq_one_of_normal_notMem_range`,
`ModuleProbe.baseBCHProjection_eq_one_iff`, and the regular-germ isolation and
comparison theorems in `DirectedDiagram.LocalCrossing` and `DirectedDiagram.Germ`.
The geometric interpretation follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
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
local notation "F" => d.shiftedFiltration ℳ p
local notation "π" => baseQuotientProjection d ℳ p ℒ
local notation "ιM" => moduleBCHInclusion d ℳ p ℒ

/-- A vertical transverse germ has trivial base crossing label. Transversality
excludes lifted base normals, which vanish on the upward probe direction. -/
@[simp]
theorem baseBCHProjection_combinedLabel_vertical_eq_one (k : ℕ) (θ : V × E)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
    (hv : ∀ a : D.active (k + 1), θ ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0) :
    (π (k + 1)).bchGroupMap (D.combinedLabel (k + 1) θ v hθ) = 1 := by
  classical
  let S := (Set.toFinite {a : D.active (k + 1) | θ ∈ (D.wall a).support}).toFinset
  let f : ((positiveDegrees d p).groupTower (grading d ℳ p ℒ)).obj (Opposite.op (k + 1)) →*
      (d.groupTower ℒ).obj (Opposite.op (k + 1)) := (π (k + 1)).bchGroupMap
  -- Products of projected labels use the categorical tower's group instances.
  change f (D.combinedLabel (k + 1) θ v hθ) = 1
  rw [D.combinedLabel_eq_prod (k + 1) θ v hθ S.toList S.nodup_toList (by simp [S])]
  rw [map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  have hm : (D.wall a).normal ∉ Set.range (baseNormal (Λ := Λ)) := by
    rintro ⟨m, hm⟩
    apply hv a (by simpa [S] using ha)
    rw [← hm]
    have he := (h.prod h').realCharacter_apply (baseNormal m) (0, 0, 1)
    simpa using he
  have hp := congrArg (CompletedGroup.projection (k + 1))
    (completedBaseProjection_label_eq_one_of_normal_notMem_range d ℳ p ℒ H h h'
      (D.wall a) hm)
  rw [projection_completedBaseProjection, map_one] at hp
  have hpa : f (CompletedGroup.projection (k + 1) (D.wall a).label) = 1 := hp
  simp only [Function.comp_apply, map_zpow, hpa, one_zpow]

/-- The coefficient with positive probe coorientation, extracted from the
logarithm of the inverse upward crossing label at extended order `k + 1`.
At a vertically transverse germ it is characterized by its negative exponential. -/
def verticalCoefficient (k : ℕ) (θ : V × E)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support)) :
    (F).quotient k :=
  -moduleQuotientProjection d ℳ p ℒ k (BCHGroup.log (D.combinedLabel (k + 1) θ v hθ))

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- The coefficient is the negative coefficient projection of the upward logarithm. -/
theorem verticalCoefficient_def (k : ℕ) (θ : V × E)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support)) :
    verticalCoefficient d ℳ p ℒ H h h' D k θ hθ =
      -moduleQuotientProjection d ℳ p ℒ k
        (BCHGroup.log (D.combinedLabel (k + 1) θ v hθ)) := (rfl)

/-- Exponentiating the negative coefficient recovers the entire upward crossing
label, including all simultaneous indexed module walls. -/
@[simp↓] -- Reconstruct before simplifying the negated coefficient inside the inclusion.
theorem moduleBCHInclusion_neg_verticalCoefficient (k : ℕ) (θ : V × E)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
    (hv : ∀ a : D.active (k + 1), θ ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0) :
    ιM k (Multiplicative.ofAdd (-verticalCoefficient d ℳ p ℒ H h h' D k θ hθ)) =
      D.combinedLabel (k + 1) θ v hθ := by
  obtain ⟨a, ha, _⟩ := (baseBCHProjection_eq_one_iff d ℳ p ℒ k _).mp
    (baseBCHProjection_combinedLabel_vertical_eq_one d ℳ p ℒ H h h' D k θ hθ hv)
  simp only [verticalCoefficient_def, neg_neg, ← ha, moduleBCHInclusion_apply,
    toAdd_ofAdd, BCHGroup.log_exp, moduleQuotientProjection_inclusion]

/-- The vertical coefficient is uniquely characterized by the negative
exponential giving the upward crossing label. -/
theorem verticalCoefficient_eq_iff (k : ℕ) (θ : V × E)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
    (hv : ∀ a : D.active (k + 1), θ ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0) (a : (F).quotient k) :
    verticalCoefficient d ℳ p ℒ H h h' D k θ hθ = a ↔
      ιM k (Multiplicative.ofAdd (-a)) = D.combinedLabel (k + 1) θ v hθ := by
  rw [← moduleBCHInclusion_neg_verticalCoefficient d ℳ p ℒ H h h' D k θ hθ hv,
    (moduleBCHInclusion_injective d ℳ p ℒ k).eq_iff,
    Multiplicative.ofAdd.injective.eq_iff, neg_inj, eq_comm]

/-- Sufficiently short upward segments through a vertical transverse regular
point all compute the negative exponential of the same coefficient. -/
theorem eventually_exists_levelPathProduct_eq_moduleBCHInclusion_neg_verticalCoefficient
    (k : ℕ) (θ : V × E)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
    (hv : ∀ a : D.active (k + 1), θ ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement (fun b : D.active (k + 1) => (D.wall b).support)) (e : x ⟶ y),
        x.val = θ - a • v ∧ y.val = θ + a • v ∧
        D.levelPathProduct (k + 1) e.toPath =
          ιM k (Multiplicative.ofAdd (-verticalCoefficient d ℳ p ℒ H h h' D k θ hθ)) := by
  rw [moduleBCHInclusion_neg_verticalCoefficient d ℳ p ℒ H h h' D k θ hθ hv]
  exact D.eventually_exists_levelPathProduct_eq_combinedLabel (k + 1) θ v hθ hv

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- Truncation preserves the extracted vertical coefficient. Regularity is
required for both wall families; no transversality is needed for this identity. -/
@[simp]
theorem transition_verticalCoefficient {k l : ℕ} (hkl : k ≤ l) (θ : V × E)
    (hl : θ ∉ singularSupport (fun a : D.active (l + 1) => (D.wall a).support))
    (hk : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support)) :
    (F).transition hkl (verticalCoefficient d ℳ p ℒ H h h' D l θ hl) =
      verticalCoefficient d ℳ p ℒ H h h' D k θ hk := by
  rw [verticalCoefficient_def, verticalCoefficient_def, map_neg,
    transition_moduleQuotientProjection]
  congr 2
  rw [← LieHom.log_bchGroupMap, D.truncation_combinedLabel (Nat.add_le_add_right hkl 1)]

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- Equivalent diagrams give the same coefficient at every common vertically
transverse regular germ, independently of their indexed wall presentations. -/
theorem verticalCoefficient_eq_of_levelEquivalent {κ : Type*}
    (D' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) κ) {k : ℕ} (hDD' : D.LevelEquivalent D' (k + 1))
    (θ : V × E)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
    (hθ' : θ ∉ singularSupport (fun a : D'.active (k + 1) => (D'.wall a).support))
    (hv : ∀ a : D.active (k + 1), θ ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0)
    (hv' : ∀ a : D'.active (k + 1), θ ∈ (D'.wall a).support →
      (h.prod h').realCharacter (D'.wall a).normal v ≠ 0) :
    verticalCoefficient d ℳ p ℒ H h h' D k θ hθ =
      verticalCoefficient d ℳ p ℒ H h h' D' k θ hθ' := by
  simp only [verticalCoefficient_def, hDD'.combinedLabel_eq θ v hθ hθ' hv hv']

end Mei.ModuleProbe
