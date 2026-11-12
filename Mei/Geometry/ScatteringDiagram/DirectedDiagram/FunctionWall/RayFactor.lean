/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RayFactor

/-!
# Function walls of ray presentations

Let a directed diagram be a ray presentation of labels `g_j` with integral normals `μ_j` on
supports `S_j` (`DirectedDiagram.IsRayFactorPresentation`): its wall `(j, w)` carries the ray
factor of `g_j` on a supported ray `w` tangent to `μ_j`.

Grouping the walls `(j, w)` by `j` is a function-wall grouping
(`DirectedDiagram.FunctionWallGrouping.ofRayFactors`) when the normals are primitive and, for
a spatial projection `π`, the generators of the nontrivial ray factors of each `g_j` project
to positive rational multiples of one direction `u_j`. If `g_j = exp(v ∂_{μ_j})` for a
completed tangent coefficient `v`, the completed label of the group `j` is `g_j`
(`DirectedDiagram.FunctionWallGrouping.label_ofRayFactors`). If moreover `v = log f` and the
coefficient monoid `Q` contains `±p` for a degree `p` with `μ_j(ρ p) = 1`, the image of `f` in
the completion of `R[Q]` is the wall function of the group `j`
(`DirectedDiagram.FunctionWallGrouping.isWallFunction_ofRayFactors`), by the wall-function
formula `completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog`.

The ray presentation of function walls follows Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public section

open TauCeti (PositiveDegrees SupportedRay)

noncomputable section

namespace Mei.DirectedDiagram

open _root_.AddMonoidAlgebra

variable {R Γ Λ V M ι : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [AddCommGroup Λ]
  [AddCommGroup M] [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ

namespace FunctionWallGrouping

-- The grading and wall spaces are spelled out: local notations are not expanded hygienically in
-- `variable` binders.
variable {μ : ι → Λ →+ ℤ}
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0})}
  {S : ι → Set V} {g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)}
  (hD : D.IsRayFactorPresentation S g)
  (hμ : ∀ j, TauCeti.IsPrimitive (μ j)) (π : Γ →+ M) (u : ι → M)
  (hu : ∀ j w, d.rayFactor (tropicalVertexGrading (R := R) d ρ) (g j) w ≠ 1 →
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • π w.generator = b • u j)

/-- The grouping of a ray presentation by label: the walls `(j, w)` form the function wall of
`g_j`. The normals `μ_j` must be primitive, and the generator of every nontrivial ray factor of
`g_j` must project under `π` to a positive rational multiple of `u_j`. -/
def ofRayFactors : D.FunctionWallGrouping π ι where
  group := Sigma.fst
  support_eq hj := by rw [hD.support, hD.support, hj]
  normal_eq hj := by rw [hD.normal, hD.normal, hj]
  projectedDirection_eq {x x'} hj hx hx' := by
    rw [hD.label] at hx hx'
    obtain ⟨a, b, ha, hb, he⟩ := hu _ _ hx
    obtain ⟨a', b', ha', hb', he'⟩ := hu _ _ hx'
    refine ⟨b' * a, b * a', Nat.mul_pos hb' ha, Nat.mul_pos hb ha', ?_⟩
    rw [hD.ray, hD.ray, mul_smul, he, mul_smul, he', ← hj, smul_comm b' b]
  isPrimitive_normal x := by
    rw [hD.normal]
    exact hμ x.1

/-- The wall `(j, w)` belongs to the group `j`. -/
@[simp]
theorem ofRayFactors_group (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    (ofRayFactors hD hμ π u hu).group x = x.1 := by
  simp [ofRayFactors]

/-- If `g_j` is the exponential `exp(v ∂_{μ_j})` of a completed tangent coefficient `v`, the
completed label of the group `j` is `g_j`. -/
theorem label_ofRayFactors [Module.Free ℤ Γ] (j : ι)
    (v : (TropicalVertexCoefficientAction.filtration (R := R) d
      (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (μ j)))).completion)
    (hv : g j = d.completedBCHExp ℒ
      (completedTropicalTangentField d ρ ((Int.castAddHom R).comp (μ j)) v)) :
    (ofRayFactors hD hμ π u hu).label j = g j := by
  classical
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ _
  refine (((ofRayFactors hD hμ π u hu).eq_label_iff j _).mpr fun k => ?_).symm
  let T : Finset {w : SupportedRay d // μ j (ρ w.generator) = 0} :=
    (d.finite_raysAtOrder k).toFinset.subtype _
  let e := Function.Embedding.sigmaMk
    (β := fun j => {w : SupportedRay d // μ j (ρ w.generator) = 0}) j
  have hs : ∀ x ∈ T.map e, (ofRayFactors hD hμ π u hu).group x = j := fun x hx => by
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hx
    simp [e]
  have hact : ∀ x ∈ D.active k, (ofRayFactors hD hμ π u hu).group x = j → x ∈ T.map e := by
    rintro ⟨j', w⟩ hx hj
    obtain rfl : j' = j := by simpa using hj
    refine Finset.mem_map.mpr ⟨w, Finset.mem_subtype.mpr
      ((d.finite_raysAtOrder k).mem_toFinset.mpr (not_not.mp fun hw => ?_)), rfl⟩
    refine (D.mem_active k _).mp hx ?_
    rw [hD.label]
    exact d.projection_eq_one_of_notMem_raysAtOrder _
      (d.rayFactor_mem_completedRaySubgroup _ _ _) k hw
  rw [hv, projection_completedBCHExp_completedTropicalTangentField_eq_noncommProd_tangentRayFactor
    d ρ (μ j) v k T fun w hw hw0 => by simpa [T] using hw]
  refine (Finset.noncommProd_congr rfl (fun w _ => ?_) _).trans
    ((Finset.noncommProd_map T e _ _).symm.trans
      ((ofRayFactors hD hμ π u hu).groupLabel_eq_noncommProd j k (T.map e) hs hact).symm)
  simp [e, hD.label, hv]

open scoped Mei.TropicalVertexCoefficientAction in
/-- If `g_j = exp(log(f) ∂_{μ_j})` for a completed tangent wall function `f` congruent to one,
and the coefficient monoid `Q` contains `±p` for a degree `p` with `μ_j(ρ p) = 1`, then every
unit with the image of `f` in the completion of `R[Q]` as value is the wall function of the
group `j`. -/
theorem isWallFunction_ofRayFactors [Module.Free ℤ Γ] (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]
    (j : ι) {f : (TropicalVertexCoefficientAction.filtration (R := R) d
      (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (μ j)))).completion}
    (hf : f - 1 ∈ (TropicalVertexCoefficientAction.filtration (R := R) d
      (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (μ j)))).completionIdeal 1)
    (hg : g j = d.completedBCHExp ℒ (completedTropicalTangentField d ρ
      ((Int.castAddHom R).comp (μ j))
      ((TropicalVertexCoefficientAction.filtration (R := R) d
        (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (μ j)))).completedLog ⟨f, hf⟩)))
    (F : (TropicalVertexCoefficientAction.filtration (R := R) d Q).completionˣ)
    (hF : (F : (TropicalVertexCoefficientAction.filtration (R := R) d Q).completion) =
      completedTropicalTangentInclusion d ρ ((Int.castAddHom R).comp (μ j)) Q f)
    {p : Γ} (hp : μ j (ρ p) = 1) (hpQ : p ∈ Q) (hnpQ : -p ∈ Q) :
    (ofRayFactors hD hμ π u hu).IsWallFunction
      ((TropicalVertexCoefficientAction.filtration (R := R) d Q).completedBCHAction d ℒ) j F := by
  refine ((ofRayFactors hD hμ π u hu).isWallFunction_iff _ j F).mpr fun x hx => ?_
  rw [ofRayFactors_group] at hx
  subst hx
  have hF' : (isUnit_completedTropicalTangentInclusion d ρ _ Q hf).unit = F :=
    Units.ext (by rw [IsUnit.unit_spec, hF])
  refine ⟨⟨⟨p, hpQ⟩, by rw [hD.normal]; exact hp, ?_⟩, fun q r => ?_⟩
  · exact TropicalVertexCoefficientAction.isUnit_toCompletion_single hpQ hnpQ
  · rw [label_ofRayFactors hD hμ π u hu x.1 _ hg, hD.normal, hg, ← hF']
    exact completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog d ρ Q
      (μ x.1) hf q r

end FunctionWallGrouping

end Mei.DirectedDiagram
