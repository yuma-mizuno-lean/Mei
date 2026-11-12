/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Scat
public import Mei.Algebra.Lie.Logarithmic.WallFunction.Map
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Basic

/-!
# Pushing polynomial function walls along degree maps

Let `T : (Γ, P, δ) → (Γ', P', δ')` be a positive degree map between degree lattices projecting
to tangent lattices `Λ` and `Λ'`, and let `t : Λ → Λ'` be a tangent map with `ρ' ∘ T = t ∘ ρ` on
allowed degrees. Given integral normals `ν_i` of `Λ'` with `ν_i ∘ t = μ_i`, a
`HyperplaneTermInput` on `Γ` with normals `μ_i` is carried to the input on `Γ'` with normals
`ν_i`, the same offsets and terms, and exponents `T n_α` (`HyperplaneTermInput.map`). For
`t = id` and `ν = μ` the hyperplanes are unchanged.

Consider pushforward data `P` over `T` between the tropical vertex wall spaces whose Lie map
sends each homogeneous field `z^n ∂_{μ_i}` to `z^{T n} ∂_{ν_i}`; for instance
`DirectedWall.Pushforward.ofTropicalDegreeMap` and `DirectedWall.Pushforward.ofFiniteAlphabetLift`
with `ν = μ`, or a finite-index pushforward on normals with comparison scalar one
(`Mei.HyperplaneTermInput.diagram_pushforward_ofFiniteIndex_equivalent`). The degree map sends
degrees tangent to `μ_i` to degrees tangent to `ν_i`
(`HyperplaneTermInput.map_tropicalTangentMonoid_le`, by
`Mei.map_tropicalTangentMonoid_intCast_le`), and the completed group map of `P` sends the
function-wall label of `1 + ∑_α c_α z^{n_α}` on a hyperplane to that of
`1 + ∑_α c_α z^{T n_α}` (`HyperplaneTermInput.completedMap_label`). This is the case
`c = r = 1` of
`GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_completedLog`. If
moreover `P` sends the normal `μ_i` to `ν_i` and its spatial map pulls `ν_i` back to `μ_i`, the
pushforward of the ray presentation is equivalent to the ray presentation of the image input
(`HyperplaneTermInput.diagram_pushforward_equivalent`): on every hyperplane both have the
logarithm of the same label as family logarithm. The rays of the pushed walls are the reindexed
rays `SupportedRay.map`, several of which may coincide; the equivalence regroups them into the
ray factors of the image label. Consequently the pushforward of the scattering class of the input
is the scattering class of the image input (`HyperplaneTermInput.pushforward_scat_diagram`).

The pushforward along tropical pairings follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap GradedLieHom)

noncomputable section

namespace Mei.HyperplaneTermInput

open DirectedWall DirectedDiagram

universe u

variable {R Γ Λ Γ' Λ' ι E : Type u} {V V' : Type*} [CommRing R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ'] [AddCommGroup Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (I : HyperplaneTermInput d ρ ι E) (T : PositiveDegreeMap d e) (t : Λ →+ Λ')
  (hT : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n)) (ν : ι → Λ' →+ ℤ)
  (hν : ∀ i, (ν i).comp t = I.normal i)

/-- For a degree map `T` and a tangent map `t` with `ρ' ∘ T = t ∘ ρ` on allowed degrees, and
normals `ν_i` with `ν_i ∘ t = μ_i`: the input with normals `ν_i`, the same offsets and terms, and
the exponents `T n_α`. -/
def map : HyperplaneTermInput e ρ' ι E where
  normal := ν
  normal_ne_zero i h0 := I.normal_ne_zero i (by rw [← hν i, h0, AddMonoidHom.zero_comp])
  offset := I.offset
  wallIndex := I.wallIndex
  exponent α := T (I.exponent α)
  exponent_mem α := T.map_mem (I.exponent_mem α)
  exponent_ne_zero α := T.map_ne_zero (I.exponent_mem α) (I.exponent_ne_zero α)
  normal_exponent α := by
    rw [hT _ (I.exponent_mem α), ← AddMonoidHom.comp_apply, hν]
    exact I.normal_exponent α

/-- The mapped input has the normals `ν_i`. -/
@[simp]
theorem map_normal : (I.map T t hT ν hν).normal = ν := by
  simp [map]

/-- The mapped input has the offsets of the input. -/
@[simp]
theorem map_offset : (I.map T t hT ν hν).offset = I.offset := by
  simp [map]

/-- The mapped input places each term on the hyperplane of the input. -/
@[simp]
theorem map_wallIndex : (I.map T t hT ν hν).wallIndex = I.wallIndex := by
  simp [map]

/-- The mapped input has the exponents `T n_α`. -/
@[simp]
theorem map_exponent (α : E) : (I.map T t hT ν hν).exponent α = T (I.exponent α) := by
  simp [map]

variable {I T t hT ν hν} in
/-- Inputs mapped along degree maps that agree on the exponents coincide. -/
theorem map_congr {T' : PositiveDegreeMap d e} {hT' : ∀ n ∈ d.monoid, ρ' (T' n) = t (ρ n)}
    (hTT' : ∀ α, T (I.exponent α) = T' (I.exponent α)) :
    I.map T t hT ν hν = I.map T' t hT' ν hν :=
  HyperplaneTermInput.ext (by simp) (by simp) (by simp) (funext fun α => by simp [hTT'])

variable [Fintype E] [DecidableEq ι] [DecidableEq Γ] [DecidableEq Γ'] [Algebra ℚ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {j : Λ →+ V} {j' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice j} {h' : TauCeti.Toric.IsIntegralLattice j'}
  (P : Pushforward d e h h' (tropicalVertexWallSpaces (R := R) d ρ)
    (tropicalVertexWallSpaces e ρ'))
  (hP : ∀ i {n : Γ} (x : tropicalVertexLieAlgebra (R := R) d ρ),
    LogarithmicVectorField.single ρ n ((Int.castAddHom R).comp (I.normal i)) = x.val →
      (P.lieHom x).val =
        LogarithmicVectorField.single ρ' (P.degreeMap n) ((Int.castAddHom R).comp (ν i)))
  (hPT : ∀ n ∈ d.monoid, ρ' (P.degreeMap n) = t (ρ n)) (c : E → R)

omit [Fintype E] [DecidableEq ι] [DecidableEq Γ] [DecidableEq Γ'] in
include hν hPT in
/-- If `ρ' ∘ T = t ∘ ρ` on allowed degrees for the degree map `T` of the pushforward data and
`ν_i ∘ t = μ_i`, then `T` sends degrees tangent to the normal `μ_i` to degrees tangent to
`ν_i`. -/
theorem map_tropicalTangentMonoid_le (i : ι) :
    (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (I.normal i))).map
        P.degreeMap.toAddMonoidHom ≤
      tropicalTangentMonoid e ρ' ((Int.castAddHom R).comp (ν i)) :=
  map_tropicalTangentMonoid_intCast_le P.degreeMap hPT (a := 1) fun x => by
    rw [← hν i, AddMonoidHom.comp_apply, one_mul]

include hP in
/-- Let pushforward data over a degree map `T` with `ρ' ∘ T = t ∘ ρ` on allowed degrees act by
`z^n ∂_{μ_i} ↦ z^{T n} ∂_{ν_i}`, where `ν_i ∘ t = μ_i`. Then they send the label of
`1 + ∑ c_α z^{n_α}` on the hyperplane `i` to the label of `1 + ∑ c_α z^{T n_α}` of the mapped
input. -/
theorem completedMap_label (i : ι) :
    P.lieHom.completedMap (I.label c i) = (I.map P.degreeMap t hPT ν hν).label c i := by
  have hf₀ : completedTropicalTangentMap P.degreeMap (I.map_tropicalTangentMonoid_le t ν hν P hPT i)
      ((TropicalVertexCoefficientAction.filtration (R := R) d
        (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp (I.normal i)))).toCompletion
        (1 + ∑ α : I.Term i, AddMonoidAlgebra.single (I.tangentExponent i α) (c α))) =
      (TropicalVertexCoefficientAction.filtration (R := R) e
        (tropicalTangentMonoid e ρ' ((Int.castAddHom R).comp (ν i)))).toCompletion
        (1 + ∑ α : I.Term i, AddMonoidAlgebra.single
          ((I.map P.degreeMap t hPT ν hν).tangentExponent i α) (c α)) ^ 1 := by
    rw [pow_one, completedTropicalTangentMap_toCompletion]
    congr 1
    simp only [map_add, map_one, map_sum, tropicalTangentMap_single]
    refine congrArg (1 + ·) (Finset.sum_congr rfl fun α _ => ?_)
    congr 1
    exact Subtype.ext <| (congrArg P.degreeMap (I.coe_tangentExponent (R := R) i α)).trans
      (((I.map P.degreeMap t hPT ν hν).coe_tangentExponent (R := R) i α).trans
        (I.map_exponent _ t hPT ν hν α)).symm
  exact (congrArg _ (I.label_def c i)).trans <|
    (GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_completedLog
      P.lieHom (I.map_tropicalTangentMonoid_le t ν hν P hPT i) (c := 1)
      (fun _ _ x hx => (hP i x hx).trans (one_smul R _).symm) (r := 1) (by simp) _ _
      hf₀).trans ((I.map P.degreeMap t hPT ν hν).label_def c i).symm

variable [Module.Free ℤ Γ] [Module.Free ℤ Γ'] (hPν : ∀ i, P.normalMap (I.normal i) = ν i)
  (hPA : ∀ i y, h'.realCharacter (ν i) (P.spatialMap y) = h.realCharacter (I.normal i) y)

omit [Fintype E] [DecidableEq ι] [DecidableEq Γ] [DecidableEq Γ'] [Module.Free ℤ Γ]
  [Module.Free ℤ Γ'] in
include hPA in
/-- If the spatial map pulls `ν_i` back to `μ_i`, it maps the hyperplane `{μ_i = a_i}` onto
`{ν_i = a_i}`. -/
theorem image_spatialMap_hyperplane (i : ι) :
    P.spatialMap '' {y | h.realCharacter (I.normal i) y = I.offset i} =
      {y | h'.realCharacter (ν i) y = I.offset i} := by
  ext y
  refine ⟨?_, fun hy => ⟨P.spatialMap.symm y, ?_, P.spatialMap.apply_symm_apply y⟩⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [Set.mem_ofPred_eq, hPA]
  · rwa [Set.mem_ofPred_eq, ← hPA, P.spatialMap.apply_symm_apply]

include hP hPν hPA in
/-- Let pushforward data over a degree map `T` with `ρ' ∘ T = t ∘ ρ` on allowed degrees act by
`z^n ∂_{μ_i} ↦ z^{T n} ∂_{ν_i}`, where `ν_i ∘ t = μ_i`, send the normals `μ_i` to `ν_i`, and have
spatial map pulling `ν_i` back to `μ_i`. Then the pushforward of the ray presentation is
equivalent to the ray presentation of the mapped input. -/
theorem diagram_pushforward_equivalent :
    ((I.diagram h c).pushforward P).Equivalent ((I.map P.degreeMap t hPT ν hν).diagram h' c) := by
  refine (DirectedDiagram.equivalent_iff _ _).mpr fun k =>
    DirectedDiagram.levelEquivalent_of_familyLog_eq _
      (fun i => {y | h'.realCharacter (ν i) y = I.offset i}) ν _
      (a := Sigma.fst) (b := Sigma.fst) (fun x => ?_) (fun x => ?_) (fun x => ?_)
      (fun x => ?_) k fun i => ?_
  · simpa using I.image_spatialMap_hyperplane ν P hPA x.1
  · simp [hPν]
  · simp
  · simp
  · refine (DirectedDiagram.familyLog_pushforward (D := I.diagram h c) (a := Sigma.fst) P k
      i).trans ?_
    refine (congrArg _ (familyLog_ofHyperplaneRayFactors _ _ _ _ _ _ _ _ i)).trans ?_
    refine (LieHom.log_bchGroupMap _ _).symm.trans ?_
    refine (congrArg BCHGroup.log ((P.lieHom.projection_completedMap k _).symm.trans
      (congrArg _ (I.completedMap_label t ν hν P hP hPT c i)))).trans ?_
    exact (familyLog_ofHyperplaneRayFactors _ _ _ _ _ _ _ k i).symm

include hP hPν hPA in
/-- Let pushforward data over a degree map `T` with `ρ' ∘ T = t ∘ ρ` on allowed degrees act by
`z^n ∂_{μ_i} ↦ z^{T n} ∂_{ν_i}`, where `ν_i ∘ t = μ_i`, send the normals `μ_i` to `ν_i`, and have
spatial map pulling `ν_i` back to `μ_i`. Then pushing forward the scattering class of the input
gives the scattering class of the mapped input. -/
theorem pushforward_scat_diagram :
    Class.pushforward P ((I.diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) =
      ((I.map P.degreeMap t hPT ν hν).diagram h' c).Scat
        (fun _ => ofHyperplaneRayFactors_full ..) :=
  ((I.diagram h c).pushforward_scat _ _).trans
    (DirectedDiagram.scat_eq_of_equivalent _ _
      (I.diagram_pushforward_equivalent t ν hν P hP hPT c hPν hPA))

end Mei.HyperplaneTermInput
