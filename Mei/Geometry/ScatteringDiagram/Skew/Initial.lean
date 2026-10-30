/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Geometry.ScatteringDiagram.Skew.AdaptedBasis
public import Mei.Geometry.ScatteringDiagram.Skew.WallSpace.Graph
public import Mei.Geometry.ScatteringDiagram.Skew.WallSpace.Ray
public import Mei.Geometry.ScatteringDiagram.Skew.RayAction
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic

/-!
# Adapted polynomial incoming diagrams

An adapted integral basis and finitely many coefficients at each unfrozen index
define an actual incoming principal diagram. The wall at `i` is the entire
hyperplane of the primitive normal `κ(eᵢ)νᵢ`, and its label has wall function
`1 + ∑ₛ aᵢₛ T^(s+1)`. Its logarithmic skew potential is the inverse Euler
derivative of the formal logarithm, normalized by `κ(eᵢ)`.

The diagram uses the principal graph grading, including for degenerate and zero
skew forms. It is finitely indexed, so it is a valid finitely active input to
outgoing scattering. Coefficients range over any commutative rational algebra;
taking the coefficients to be the independent generators of a multivariable
polynomial algebra gives the universal polynomial input. Zero coefficients and
empty coefficient lists are allowed and give identity labels.

We use `DirectedWall.ofLinearHyperplane`, the graph wall-group comparison,
`SkewLieAlgebra.rayExp`, and the principal ray-action formula. The polynomial
inputs and normalization follow Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, §1 and Appendix B (arXiv:1411.1394v2), and Burcroff–Lee–Mou,
*Positivity of generalized cluster scattering diagrams*, §8 (arXiv:2503.03719v1).
-/

public noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open PowerSeries

variable {N R ι V : Type*} [AddCommGroup N]
  {D : SkewLatticeDatum N} (B : D.AdaptedBasis ι)

section Function

variable [Semiring R] (ℓ : B.unfrozenIndex → ℕ) (a : ∀ i, Fin (ℓ i) → R)

/-- The polynomial ray function at an unfrozen index, with constant term one.
Index `s : Fin (ℓ i)` represents the coefficient of `T^(s+1)`. -/
def polynomialWallFunction (i : B.unfrozenIndex) : PowerSeries R :=
  1 + ∑ s : Fin (ℓ i), monomial (s.val + 1) (a i s)

/-- The polynomial ray function is the stated finite sum of monomials. -/
theorem polynomialWallFunction_def (i : B.unfrozenIndex) :
    B.polynomialWallFunction ℓ a i =
      1 + ∑ s : Fin (ℓ i), monomial (s.val + 1) (a i s) := (rfl)

/-- Every input polynomial has constant coefficient one. -/
@[simp]
theorem constantCoeff_polynomialWallFunction (i : B.unfrozenIndex) :
    constantCoeff (B.polynomialWallFunction ℓ a i) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp only [polynomialWallFunction, map_add, map_sum, coeff_zero_one,
    coeff_monomial, Nat.zero_ne_add_one,
    ↓reduceIte, Finset.sum_const_zero, add_zero]

/-- Positive coefficients are the specified input coefficients within the
polynomial's bound, and zero above it. -/
@[simp]
theorem coeff_polynomialWallFunction_succ (i : B.unfrozenIndex) (k : ℕ) :
    coeff (k + 1) (B.polynomialWallFunction ℓ a i) =
      if hk : k < ℓ i then a i ⟨k, hk⟩ else 0 := by
  classical
  by_cases hk : k < ℓ i
  · have he : ∀ s : Fin (ℓ i), k = s.val ↔ (⟨k, hk⟩ : Fin (ℓ i)) = s := by
      intro s
      constructor
      · intro hs
        apply Fin.ext
        exact hs
      · intro hs
        exact congrArg Fin.val hs
    simp [polynomialWallFunction, coeff_monomial, hk, he]
  · have he : ∀ s : Fin (ℓ i), k ≠ s.val := by
      intro s hs
      exact hk (hs ▸ s.isLt)
    simp [polynomialWallFunction, coeff_monomial, hk, he]

end Function

variable [Module.Free ℤ N] [CommRing R] [Algebra ℚ R]
  (ℓ : B.unfrozenIndex → ℕ) (a : ∀ i, Fin (ℓ i) → R)
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]

local notation "𝒅" => B.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) 𝒅
local notation "e" => D.principalPositiveDegrees 𝒅
local notation "𝓗" => D.principalGraphWallSpaces (R := R) 𝒅

/-- The normalized polynomial label, on the principal graph grading.
Its logarithm is `κ(eᵢ) ∑ⱼ [Tʲ](Euler⁻¹(log fᵢ)) X_(jeᵢ)`. -/
def polynomialWallLabel (i : B.unfrozenIndex) :
    (𝓗).wallGroup ((B.unfrozenBasis.positiveDegreesRay i).graph
      D.principalCharacter.toAddMonoidHom)
      (D.principalNormal (B.unfrozenBasis i)).toAddMonoidHom := by
  let w := B.unfrozenBasis.positiveDegreesRay i
  have hn : B.unfrozenBasis i ∈ (𝒅).monoid := by
    rw [Module.Basis.positiveDegrees_monoid_eq_closure]
    exact AddSubmonoid.subset_closure (Set.mem_range_self i)
  have hr : B.unfrozenBasis i ∈ w.rayDegrees := by
    simpa only [w, Module.Basis.positiveDegreesRay_generator] using
      (SupportedRay.generator_mem_rayDegrees_iff w).mpr
        (by simpa only [w, Module.Basis.positiveDegreesRay_generator] using hn)
  let f := algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex (B.unfrozenBasis i)) •
    eulerDerivInv (logOf (B.polynomialWallFunction ℓ a i))
  let g := SkewLieAlgebra.rayExp (d := 𝒅) (D.coefficientForm R) (D.isAlt_coefficientForm R)
    hn (B.unfrozenBasis.ne_zero i) f
  refine ⟨(𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom g, ?_⟩
  rw [← D.map_principalGraphWallGroup]
  refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
  simpa only [w, Module.Basis.positiveDegreesRay_generator] using
    D.rayExp_mem_principalWallGroup (R := R) 𝒅 hr f

/-- Forgetting the wall-group subtype recovers graph regrading of the normalized
skew exponential. This formula determines the input label at every order. -/
theorem coe_polynomialWallLabel (i : B.unfrozenIndex) :
    (B.polynomialWallLabel ℓ a i : (e).completedBCHGroup (D.principalGrading (R := R) 𝒅)) =
      (𝒅).graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom
        (SkewLieAlgebra.rayExp (d := 𝒅) (D.coefficientForm R) (D.isAlt_coefficientForm R)
          (by
            rw [Module.Basis.positiveDegrees_monoid_eq_closure]
            exact AddSubmonoid.subset_closure (Set.mem_range_self i))
          (B.unfrozenBasis.ne_zero i)
          (algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex (B.unfrozenBasis i)) •
            eulerDerivInv (logOf (B.polynomialWallFunction ℓ a i)))) := by
  rfl

section Action

open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
  [Fact ((D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees).monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) e Q
local notation "ℳ" => tropicalVertexGrading (R := R) e (AddMonoidHom.id Lpr)

/-- The label of the polynomial input acts by the polynomial ray function
raised to the primitive normal pairing. Powers are in units, allowing either
crossing sign and arbitrary integer monomial weights. -/
theorem completedBCHAction_polynomialWallLabel (i : B.unfrozenIndex)
    (q : Q) (hq : q.val = D.principalEmbedding (B.unfrozenBasis i))
    (u : (F).completionIdeal 1) (hu : u.val = (F).toCompletion (single q 1))
    (f : (F).completionˣ)
    (hf : (f : (F).completion) = (F).completedAeval u (B.polynomialWallFunction ℓ a i))
    (p : Q) (c : R) :
    (F).completedBCHAction (R := R)
      (L := tropicalVertexLieAlgebra (R := R) e (AddMonoidHom.id Lpr)) e ℳ
        ((D.principalGraphGradedLieHom 𝒅).completedMap (B.polynomialWallLabel ℓ a i))
        ((F).toCompletion (single p c)) =
      ((f ^ D.principalNormal (B.unfrozenBasis i) p.val : (F).completionˣ) : (F).completion) *
        (F).toCompletion (single p c) := by
  have hmap := DFunLike.congr_fun (D.completedMap_principalGradedLieHom (R := R) 𝒅)
    (SkewLieAlgebra.rayExp (d := 𝒅) (D.coefficientForm R) (D.isAlt_coefficientForm R)
      (by
        rw [Module.Basis.positiveDegrees_monoid_eq_closure]
        exact AddSubmonoid.subset_closure (Set.mem_range_self i))
      (B.unfrozenBasis.ne_zero i)
      (algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex (B.unfrozenBasis i)) •
        eulerDerivInv (logOf (B.polynomialWallFunction ℓ a i))))
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hmap
  have hlabel := (congrArg (D.principalGraphGradedLieHom (R := R) 𝒅).completedMap
    (B.coe_polynomialWallLabel (R := R) ℓ a i)).trans hmap.symm
  refine (congrArg (fun z => (F).completedBCHAction (R := R) e ℳ z
    ((F).toCompletion (single p c))) hlabel).trans ?_
  simpa only [Int.cast_one, one_mul] using
    D.completedBCHAction_completedMap_rayExp_eulerDerivInv_logOf 𝒅
      (by
        rw [Module.Basis.positiveDegrees_monoid_eq_closure]
        exact AddSubmonoid.subset_closure (Set.mem_range_self i))
      (B.unfrozenBasis.ne_zero i) 1 Q (B.polynomialWallFunction ℓ a i)
      (B.constantCoeff_polynomialWallFunction ℓ a i) q hq u hu f hf p c

end Action

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ D.sublattice × D.unfrozen) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The adapted polynomial input on the principal lattice: one full incoming
hyperplane per unfrozen index, with its normalized polynomial ray label. -/
def adaptedPolynomialInput : DirectedDiagram (V := V) (d := e) h (𝓗) B.unfrozenIndex :=
  DirectedDiagram.ofFinite (h := h) (H := 𝓗) fun i =>
    DirectedWall.ofLinearHyperplane (V := V) h (𝓗)
      (D.principalNormal (B.unfrozenBasis i)).toAddMonoidHom
      (by
        intro hz
        exact (B.unfrozenBasis.ne_zero i) ((D.principalNormal_eq_zero_iff _).mp
          (LinearMap.toAddMonoidHom_injective hz)))
      ((B.unfrozenBasis.positiveDegreesRay i).graph D.principalCharacter.toAddMonoidHom)
      (by
        apply Int.cast_injective (α := ℚ)
        simp only [SupportedRay.graph_generator, Module.Basis.positiveDegreesRay_generator,
          AddMonoidHom.id_apply, LinearMap.toAddMonoidHom_coe]
        rw [← D.principalEmbedding_apply, D.cast_principalNormal_principalEmbedding]
        simp)
      (B.polynomialWallLabel ℓ a i)

/-- The coorientation is the primitive integral principal normal. -/
@[simp]
theorem adaptedPolynomialInput_normal (i : B.unfrozenIndex) :
    ((B.adaptedPolynomialInput (V := V) ℓ a h).wall i).normal =
      (D.principalNormal (B.unfrozenBasis i)).toAddMonoidHom := by
  simp [adaptedPolynomialInput]

/-- The wall's associated degree ray is the principal ray through `r(eᵢ)`. -/
@[simp]
theorem adaptedPolynomialInput_ray (i : B.unfrozenIndex) :
    ((B.adaptedPolynomialInput (V := V) ℓ a h).wall i).ray =
      (B.unfrozenBasis.positiveDegreesRay i).graph D.principalCharacter.toAddMonoidHom := by
  simp [adaptedPolynomialInput]

/-- The support is the full principal cylinder hyperplane. -/
@[simp]
theorem adaptedPolynomialInput_support (i : B.unfrozenIndex) :
    ((B.adaptedPolynomialInput (V := V) ℓ a h).wall i).support =
      (h.realCharacter (D.principalNormal (B.unfrozenBasis i)).toAddMonoidHom).ker := by
  simp [adaptedPolynomialInput]

/-- The input wall carries the constructed normalized polynomial label. -/
@[simp]
theorem adaptedPolynomialInput_label (i : B.unfrozenIndex) :
    ((B.adaptedPolynomialInput (V := V) ℓ a h).wall i).label = B.polynomialWallLabel ℓ a i := by
  simp [adaptedPolynomialInput]

/-- All initial walls are incoming, even when their degrees are radical. -/
@[simp]
theorem adaptedPolynomialInput_incoming (i : B.unfrozenIndex) :
    ((B.adaptedPolynomialInput (V := V) ℓ a h).wall i).Incoming := by
  simp [adaptedPolynomialInput]

/-- The input satisfies the full-hyperplane hypothesis of outgoing scattering. -/
theorem adaptedPolynomialInput_full (i : B.unfrozenIndex) :
    ∃ c : ℝ, ((B.adaptedPolynomialInput (V := V) ℓ a h).wall i).support =
      {x | h.realCharacter ((B.adaptedPolynomialInput (V := V) ℓ a h).wall i).normal x = c} := by
  refine ⟨0, ?_⟩
  simp only [B.adaptedPolynomialInput_support, B.adaptedPolynomialInput_normal]
  rfl

end Mei.SkewLatticeDatum.AdaptedBasis
