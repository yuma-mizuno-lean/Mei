/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallSpace
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Truncation
public import Mei.Algebra.Lie.Graded.Shifted.Map

/-!
# Coefficient maps of module probes

A homogeneous equivariant linear map of coefficient modules induces a graded Lie
map of their semidirect probes. It fixes the base Lie algebra and preserves the
charge-one coefficient summand, including coefficients killed by the map.

-/

public noncomputable section

namespace Mei.ModuleProbe

variable {R M N Γ L : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Γ] [DecidableEq Γ] [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M] [LieRingModule L N] [LieModule R L N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [SetLike.GradedBracket ℒ 𝓝]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝓝 q).comap f)
  (hequiv : ∀ (x : L) (a : M), f ⁅x, a⁆ = ⁅x, f a⁆)

/-- The map on the abelian shifted coefficient summands. -/
def coefficientMap : ModuleCoefficients d ℳ p →ₗ[R] ModuleCoefficients d 𝓝 p :=
  (moduleCoefficientsEquiv d 𝓝 p).symm.toLinearMap.comp
    ((PositiveDegrees.shiftedCoefficientMap d ℳ 𝓝 p f hf).comp
      (moduleCoefficientsEquiv d ℳ p).toLinearMap)

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- Forgetting the zero bracket recovers the restricted linear coefficient map. -/
@[simp]
theorem moduleCoefficientsEquiv_coefficientMap (a : ModuleCoefficients d ℳ p) :
    moduleCoefficientsEquiv d 𝓝 p (coefficientMap d ℳ 𝓝 p f hf a) =
      PositiveDegrees.shiftedCoefficientMap d ℳ 𝓝 p f hf (moduleCoefficientsEquiv d ℳ p a) := by
  simp [coefficientMap]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  [LieModule R L M] [LieModule R L N] in
include hequiv in
/-- The canonical shifted coefficient map intertwines the restricted Lie actions. -/
theorem shiftedCoefficientMap_lie (x : L) (a : d.shiftedLieSubmodule ℒ ℳ p) :
    (show d.shiftedLieSubmodule ℒ 𝓝 p from
      d.shiftedCoefficientMap ℳ 𝓝 p f hf (⁅x, a⁆ : d.shiftedLieSubmodule ℒ ℳ p)) =
      ⁅x, (show d.shiftedLieSubmodule ℒ 𝓝 p from d.shiftedCoefficientMap ℳ 𝓝 p f hf a)⁆ := by
  let ψ : d.shiftedLieSubmodule ℒ ℳ p →ₗ[R] d.shiftedLieSubmodule ℒ 𝓝 p :=
    d.shiftedCoefficientMap ℳ 𝓝 p f hf
  have hψ (a : d.shiftedLieSubmodule ℒ ℳ p) : (ψ a : N) = f a :=
    d.coe_shiftedCoefficientMap ℳ 𝓝 p f hf a
  have heq : ψ ⁅x, a⁆ = ⁅x, ψ a⁆ := by
    apply Subtype.ext
    simp only [hψ, LieSubmodule.coe_bracket, hequiv]
  exact heq

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
include hequiv in
/-- Equivariance survives restriction to the shifted coefficient summands. -/
theorem coefficientMap_actionDerivationHom (x : L) (a : ModuleCoefficients d ℳ p) :
    coefficientMap d ℳ 𝓝 p f hf (actionDerivationHom d ℳ p ℒ x a) =
      actionDerivationHom d 𝓝 p ℒ x (coefficientMap d ℳ 𝓝 p f hf a) := by
  apply (moduleCoefficientsEquiv d 𝓝 p).injective
  simp only [moduleCoefficientsEquiv_coefficientMap, moduleCoefficientsEquiv_actionDerivationHom]
  exact shiftedCoefficientMap_lie d ℳ 𝓝 p ℒ f hf hequiv x _

/-- A coefficient map fixes the base summand and maps the coefficient summand. -/
def coefficientLieHom : ProbeLie d ℳ p ℒ →ₗ⁅R⁆ ProbeLie d 𝓝 p ℒ where
  toFun x := ⟨coefficientMap d ℳ 𝓝 p f hf x.left, x.right⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  map_lie' {x y} := by
    ext <;> simp [coefficientMap_actionDerivationHom d ℳ 𝓝 p ℒ f hf hequiv]

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The charge-one projection is the induced coefficient map. -/
@[simp]
theorem coefficientLieHom_left (x : ProbeLie d ℳ p ℒ) :
    (coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv x).left =
      coefficientMap d ℳ 𝓝 p f hf x.left := by
  -- The homomorphism is constructed with these two semidirect coordinates.
  rfl

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The base projection is unchanged by coefficient maps. -/
@[simp]
theorem coefficientLieHom_right (x : ProbeLie d ℳ p ℒ) :
    (coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv x).right = x.right := by
  -- The homomorphism is constructed with the original base coordinate.
  rfl

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The semidirect coefficient map fixes every charge-zero base input. -/
@[simp]
theorem coefficientLieHom_baseInclusion (x : L) :
    coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv ⟨0, x⟩ =
      baseInclusion d 𝓝 p ℒ x := by ext <;> simp

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The semidirect coefficient map restricts to the given coefficient map. -/
@[simp]
theorem coefficientLieHom_moduleInclusion (a : ModuleCoefficients d ℳ p) :
    coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv ⟨a, 0⟩ =
      moduleInclusion d 𝓝 p ℒ (coefficientMap d ℳ 𝓝 p f hf a) := by ext <;> simp

/-- The semidirect coefficient map preserves the reduced probe degree `(q,c)`. -/
def coefficientGradedLieHom : GradedLieHom (PositiveDegreeMap.id (positiveDegrees d p))
    (grading d ℳ p ℒ) (grading d 𝓝 p ℒ) where
  toLieHom := coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv
  map_mem {a x} hx := by
    rcases a with ⟨q, c⟩
    simp only [PositiveDegreeMap.id_apply]
    -- Unpack the graded homomorphism field to use the semidirect coordinate equations.
    change coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv x ∈ grading d 𝓝 p ℒ (q, c)
    by_cases h0 : c = 0
    · subst c
      rw [mem_grading_base] at hx ⊢
      simpa [hx.1] using hx.2
    · by_cases h1 : c = 1
      · subst c
        rw [mem_grading_module] at hx ⊢
        refine ⟨hx.1, ?_⟩
        rw [coefficientLieHom_left, moduleCoefficientsEquiv_coefficientMap]
        exact PositiveDegrees.shiftedCoefficientMap_mem_shiftedGrading d ℳ 𝓝 p f hf hx.2
      · rw [grading_charge_eq_bot d ℳ p ℒ q c h0 h1, Submodule.mem_bot] at hx
        rw [hx, map_zero]
        exact Submodule.zero_mem _

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The graded coefficient map has the underlying semidirect coefficient map. -/
@[simp]
theorem coefficientGradedLieHom_apply (x : ProbeLie d ℳ p ℒ) :
    coefficientGradedLieHom d ℳ 𝓝 p ℒ f hf hequiv x =
      coefficientLieHom d ℳ 𝓝 p ℒ f hf hequiv x := by rfl

omit [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- Coefficient changes preserve the probe wall spaces, with no injectivity assumption. -/
theorem coefficientGradedLieHom_mem_wall {Λ : Type*} [AddCommMonoid Λ]
    {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
    [IsWallAnnihilating H ℳ] [IsWallAnnihilating H 𝓝]
    (a : Γ × ℤ) (m : (Λ × ℤ) →+ ℤ) (x : ProbeLie d ℳ p ℒ)
    (hx : x ∈ (wallSpaces d ℳ p ℒ H).wall a m) :
    coefficientGradedLieHom d ℳ 𝓝 p ℒ f hf hequiv x ∈
      (wallSpaces d 𝓝 p ℒ H).wall a m := by
  rw [wallSpaces_wall, mem_wallSubmodule_iff] at hx ⊢
  rcases hx with rfl | ⟨q, m₀, y, rfl, rfl, hy, rfl⟩ | ⟨q, c, rfl, hc, rfl, hx⟩
  · exact Or.inl (map_zero _)
  · exact Or.inr (Or.inl ⟨q, m₀, y, rfl, rfl, hy,
      coefficientLieHom_baseInclusion d ℳ 𝓝 p ℒ f hf hequiv y⟩)
  · exact Or.inr (Or.inr ⟨q, c, rfl, hc, rfl,
      by simpa only [PositiveDegreeMap.id_apply, GradedLieHom.coe_toLieHom] using
        (coefficientGradedLieHom d ℳ 𝓝 p ℒ f hf hequiv).map_mem hx⟩)

/-- Extracting a finite coefficient commutes with arbitrary coefficient changes. -/
@[simp]
theorem moduleQuotientProjection_coefficientGradedLieHom (k : ℕ)
    (x : (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1)) :
    moduleQuotientProjection d 𝓝 p ℒ k
        ((coefficientGradedLieHom d ℳ 𝓝 p ℒ f hf hequiv).truncatedMap (k + 1) (by simp) x) =
      PositiveDegrees.quotientCoefficientMap d ℳ 𝓝 p f hf k
        (moduleQuotientProjection d ℳ p ℒ k x) := by
  obtain ⟨x, rfl⟩ := ((positiveDegrees d p).degreeIdeal
    (grading d ℳ p ℒ) (k + 1)).surjective_mkQ x
  rw [LieIdeal.mkQ_apply, GradedLieHom.truncatedMap_mk,
    moduleQuotientProjection_mk, moduleQuotientProjection_mk,
    PositiveDegrees.quotientCoefficientMap_mk]
  congr 1
  exact moduleCoefficientsEquiv_coefficientMap d ℳ 𝓝 p f hf x.left

end Mei.ModuleProbe
