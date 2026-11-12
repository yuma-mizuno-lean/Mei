/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Positive

/-!
# Principal adapted polynomial inputs in the tropical vertex group

The fixed-degree principal realization `principalGraphGradedLieHom` sends the principal graph wall
spaces into the tropical vertex wall spaces of the principal lattice `L_pr = M° × N_uf`, with
identity spatial map (`SkewLatticeDatum.principalGraphGradedLieHom_mem_wall`). Hence it maps
principal diagrams to tropical vertex diagrams (`DirectedDiagram.map`), and their outgoing
scattering classes correspondingly (`DirectedDiagram.map_scat`).

For an adapted basis `(eᵢ)` and the adapted polynomial input with wall functions
`fᵢ = 1 + ∑_{s<ℓᵢ} aᵢₛ T^(s+1)`, the image of the label at the unfrozen index `i` is the tangent
label `exp(log fᵢ(z^{r(eᵢ)}) ∂_{κ(eᵢ)νᵢ})` of the tropical vertex group
(`AdaptedBasis.principalGraphGradedLieHom_completedMap_polynomialWallLabel`): its logarithm is the
completed logarithm of `fᵢ` evaluated at the principal monomial `z^{r(eᵢ)}`, in the coefficient
algebra of the degrees tangent to the primitive normal `κ(eᵢ)νᵢ`. This holds for every form,
including degenerate and zero forms.

If the form vanishes on `N_uf`, for instance for the zero form, the adapted polynomial input is
consistent; so is its tropical vertex image, whose outgoing scattering class is therefore its
own class (`AdaptedBasis.map_scat_adaptedPolynomialInput_of_forall_form_eq_zero`).

The principal realization and the adapted polynomial inputs are those of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and Appendix B
(arXiv:1411.1394v2). The label formula is
`SkewLatticeDatum.principalGradedLieHom_completedMap_rayExp_eulerDerivInv_logOf`.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open _root_.AddMonoidAlgebra PowerSeries

variable {N R V : Type*} {ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N}
  (B : D.AdaptedBasis ι) [Module.Free ℤ N] [CommRing R] [Algebra ℚ R]
  (ℓ : B.unfrozenIndex → ℕ) (a : ∀ i, Fin (ℓ i) → R)
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]

local notation "𝒅" => B.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "e" => D.principalPositiveDegrees 𝒅
local notation "ρ" => AddMonoidHom.id Lpr
local notation "ℳ" => tropicalVertexGrading (R := R) e ρ

section Label

-- The lattice is spelled out: local notations are not expanded hygienically in `variable`
-- binders.
variable {χ : Module.Dual ℤ D.sublattice × D.unfrozen →+ R}

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) e
  (tropicalTangentMonoid e ρ χ)

/-- The principal image of the label of the adapted polynomial input at the unfrozen index `i`
is the tangent label `exp(log fᵢ(z^{r(eᵢ)}) ∂_{κ(eᵢ)νᵢ})`, for every form. Here `χ` is any
character equal to the cast of the primitive normal `κ(eᵢ)νᵢ`, `q` is the principal exponent
`r(eᵢ)` as a degree tangent to it and `u` is the completed monomial `z^{r(eᵢ)}`. -/
theorem principalGraphGradedLieHom_completedMap_polynomialWallLabel (i : B.unfrozenIndex)
    (hχ : χ = (Int.castAddHom R).comp (D.principalNormal (B.unfrozenBasis i)).toAddMonoidHom)
    (q : tropicalTangentMonoid e ρ χ) (hq : q.val = D.principalEmbedding (B.unfrozenBasis i))
    (u : (G).completionIdeal 1) (hu : u.val = (G).toCompletion (single q 1)) :
    (D.principalGraphGradedLieHom 𝒅).completedMap (B.polynomialWallLabel ℓ a i) =
      (e).completedBCHExp ℳ (completedTropicalTangentField e ρ χ
        ((G).completedLog ⟨(G).completedAeval u (B.polynomialWallFunction ℓ a i),
          (G).completedAeval_sub_one_mem_first u _
            (B.constantCoeff_polynomialWallFunction ℓ a i)⟩)) := by
  -- Proof plan: undo the graph regrading of the label, then apply the principal formula for
  -- normalized ray labels with integer scale `1`.
  have hn := B.unfrozenBasis_mem_positiveDegrees_monoid i
  have hmap := DFunLike.congr_fun (D.completedMap_principalGradedLieHom (R := R) 𝒅)
    (SkewLieAlgebra.rayExp (D.coefficientForm R) (D.isAlt_coefficientForm R) hn
      (B.unfrozenBasis.ne_zero i)
      (algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex (B.unfrozenBasis i)) •
        eulerDerivInv (logOf (B.polynomialWallFunction ℓ a i))))
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hmap
  refine ((congrArg (D.principalGraphGradedLieHom (R := R) 𝒅).completedMap
    (B.coe_polynomialWallLabel (R := R) ℓ a i)).trans hmap.symm).trans ?_
  have hs : D.sublattice.toAddSubgroup.rayIndex (B.unfrozenBasis i) =
      ((1 : ℤ) : ℚ) * D.sublattice.toAddSubgroup.rayIndex (B.unfrozenBasis i) := by
    rw [Int.cast_one, one_mul]
  refine (congrArg (fun r => (D.principalGradedLieHom (R := R) 𝒅).completedMap
    (SkewLieAlgebra.rayExp (D.coefficientForm R) (D.isAlt_coefficientForm R) hn
      (B.unfrozenBasis.ne_zero i)
      (algebraMap ℚ R r • eulerDerivInv (logOf (B.polynomialWallFunction ℓ a i))))) hs).trans ?_
  exact D.principalGradedLieHom_completedMap_rayExp_eulerDerivInv_logOf 𝒅 hn
    (B.unfrozenBasis.ne_zero i) 1 (hχ.trans (by rw [one_smul])) _
    (B.constantCoeff_polynomialWallFunction ℓ a i) q hq u hu

end Label

section Abelian

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : Module.Dual ℤ D.sublattice × D.unfrozen →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- If the form vanishes on the unfrozen sublattice, for instance for the zero form, the tropical
vertex image of the adapted polynomial input is consistent. -/
theorem consistent_map_adaptedPolynomialInput_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0) :
    ((B.adaptedPolynomialInput ℓ a h).map (D.principalGraphGradedLieHom 𝒅)
      fun _ _ _ => D.principalGraphGradedLieHom_mem_wall 𝒅).Consistent :=
  (B.adaptedPolynomialInput_consistent_of_forall_form_eq_zero ℓ a hform h).map _ _ _

/-- If the form vanishes on the unfrozen sublattice, for instance for the zero form, the
tropical vertex image of the outgoing scattering class of the adapted polynomial input is the
class of the image of the input itself: the input walls commute in both Lie algebras and no
outgoing walls are added. -/
theorem map_scat_adaptedPolynomialInput_of_forall_form_eq_zero
    [Module.Free ℤ (Module.Dual ℤ D.sublattice × D.unfrozen)]
    (hform : ∀ n m : D.unfrozen, D.form n m = 0) :
    DirectedDiagram.Class.map (D.principalGraphGradedLieHom 𝒅)
        (fun _ _ _ => D.principalGraphGradedLieHom_mem_wall 𝒅)
        ((B.adaptedPolynomialInput ℓ a h).Scat (B.adaptedPolynomialInput_full ℓ a h)) =
      ((B.adaptedPolynomialInput ℓ a h).map (D.principalGraphGradedLieHom 𝒅)
        fun _ _ _ => D.principalGraphGradedLieHom_mem_wall 𝒅).toClass := by
  rw [B.scat_adaptedPolynomialInput_of_forall_form_eq_zero ℓ a h hform,
    DirectedDiagram.Class.map_toClass]

end Abelian

end Mei.SkewLatticeDatum.AdaptedBasis
