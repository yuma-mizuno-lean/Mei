/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.RayFactor
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.FiniteAlphabet

/-!
# Function walls and positivity of polynomial walls on hyperplanes

Let `I` be a `HyperplaneTermInput` on `(Γ, P, δ)` with projection `ρ : Γ → Λ`, and fix a
spatial projection `π : Γ → M`. Suppose that on each hyperplane `i` the exponents `n_α` of the
terms project under `π` to positive multiples of one direction `u_i`, as for the terms `s w_i`
of a BLM polynomial, and that the normals `μ_i` are primitive. Then grouping the walls of the
ray presentation `I.diagram` by hyperplane is a function-wall grouping
(`HyperplaneTermInput.grouping`), whose group `i` has the label `exp(log(f_i) ∂_{μ_i})` of
`f_i = 1 + ∑_{wallIndex α = i} c_α z^{n_α}` (`HyperplaneTermInput.label_grouping`).
Without a common direction the walls of one hyperplane need not form one function wall: two
terms on a hyperplane of rank two can have linearly independent exponents.

For a coefficient monoid `Q` containing `±p` with `μ_i(ρ p) = 1`, the image of `f_i` in the
completion of `R[Q]` (`HyperplaneTermInput.completedWallFunction`) is the wall function of the
group `i` (`HyperplaneTermInput.isWallFunction_grouping`). If the coefficients `c_α` lie in the
image of a semiring map `φ : S →+* R`, the wall functions are positive for the image of `S[Q]`,
so the ray presentation is a positive wall representative
(`HyperplaneTermInput.isPositiveWallRepresentative_diagram`).

Lifting an input on the finite alphabet with exponents `x_α` along `τ` to degree data on `L`
with projection `π : L → M` (`HyperplaneTermInput.liftFiniteAlphabet`) gives the walls
`1 + ∑ c_α z^{τ x_α}`, and `π` sends `τ x_α` to the first coordinate of `x_α`; for the
alphabet input `x_α = v_α`, this is `π n_α = m_α`. If these first coordinates on each
hyperplane are positive multiples of one direction of `M`, the lifted ray presentation is a
positive wall representative for the projection `π`
(`HyperplaneTermInput.isPositiveWallRepresentative_liftFiniteAlphabet_diagram`). This is the
grouping and positivity of the lifted wall functions in the finite alphabet lift of
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, §9.2
(arXiv:2503.03719v1), with the grouped wall functions of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2). The identification of the
alphabet with the variables `p_{i,s}` of a BLM polynomial input is not treated here.
-/

public section

open TauCeti (PositiveDegrees SupportedRay)

noncomputable section

namespace Mei.HyperplaneTermInput

open _root_.AddMonoidAlgebra DirectedDiagram

section Grouping

variable {Γ Λ R ι E V M : Type*} [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup M]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} (I : HyperplaneTermInput d ρ ι E) [CommRing R]
  [Fintype E] [DecidableEq ι] [DecidableEq Γ] [Algebra ℚ R] [Module.Free ℤ Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {j : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice j)
  (c : E → R) (π : Γ →+ M) (u : ι → M)

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ

variable (hμ : ∀ i, TauCeti.IsPrimitive (I.normal i))
  (hu : ∀ α, ∃ b : ℕ, 0 < b ∧ π (I.exponent α) = b • u (I.wallIndex α))

/-- The grouping of the ray walls of `I.diagram` by hyperplane, for primitive normals and
exponents projecting under `π` to positive multiples of one direction `u_i` on each
hyperplane `i`. -/
def grouping : (I.diagram h c).FunctionWallGrouping π ι :=
  FunctionWallGrouping.ofRayFactors (isRayFactorPresentation_ofHyperplaneRayFactors ..) hμ π u
    fun i _ hw => I.rayFactor_label_projectedDirection c π u hu i hw

/-- A ray wall belongs to the group of its hyperplane. -/
@[simp]
theorem grouping_group (x : Σ i, {w : SupportedRay d // I.normal i (ρ w.generator) = 0}) :
    (I.grouping h c π u hμ hu).group x = x.1 :=
  FunctionWallGrouping.ofRayFactors_group ..

/-- The label of the group of the hyperplane `i` is the function-wall label of `f_i`. -/
@[simp]
theorem label_grouping (i : ι) : (I.grouping h c π u hμ hu).label i = I.label c i :=
  FunctionWallGrouping.label_ofRayFactors _ hμ π u _ i _ (I.label_def c i)

section Action

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d Q

/-- If `Q` contains `±p` for a degree `p` with `μ_i(ρ p) = 1`, the completed wall function
`f_i` is the wall function of the group of the hyperplane `i`. -/
theorem isWallFunction_grouping (i : ι) {p : Γ} (hp : I.normal i (ρ p) = 1) (hpQ : p ∈ Q)
    (hnpQ : -p ∈ Q) :
    (I.grouping h c π u hμ hu).IsWallFunction ((G).completedBCHAction d ℒ) i
      (I.completedWallFunction c Q i) :=
  FunctionWallGrouping.isWallFunction_ofRayFactors _ hμ π u _ Q i _ (I.label_def c i) _
    (by
      rw [coe_completedWallFunction, completedTropicalTangentInclusion_toCompletion]
      simp only [map_add, map_one, map_sum, tropicalTangentInclusion_single, coe_tangentExponent])
    hp hpQ hnpQ

variable (hQ : ∀ i, ∃ p ∈ Q, -p ∈ Q ∧ I.normal i (ρ p) = 1)
  {S : Type*} [Semiring S] (φ : S →+* R) (hc : ∀ α, c α ∈ φ.rangeS)

include hQ hc

/-- The grouping by hyperplane is positive for the image of `S[Q]` when the coefficients lie in
the image of `φ` and `Q` contains `±p` for a degree `p` of normal pairing one on each
hyperplane. -/
theorem isPositive_grouping :
    (I.grouping h c π u hμ hu).IsPositive ((G).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS :=
  ((I.grouping h c π u hμ hu).isPositive_iff _ _).mpr fun i => by
    obtain ⟨p, hpQ, hnpQ, hp⟩ := hQ i
    exact ⟨I.completedWallFunction c Q i, I.isWallFunction_grouping h c π u hμ hu Q i hp hpQ hnpQ,
      I.isPositive_completedWallFunction c Q φ hc i⟩

omit hμ in
include hu in
/-- **Positivity of polynomial walls on hyperplanes.** If the exponents on each hyperplane `i`
project under `π` to positive multiples of one direction `u_i`, the coefficients lie in the
image of `φ : S →+* R`, and `Q` contains `±p` for a degree `p` of normal pairing one on each
hyperplane, then the ray presentation `I.diagram` is a positive wall representative for the
image of `S[Q]`. -/
theorem isPositiveWallRepresentative_diagram :
    (I.diagram h c).IsPositiveWallRepresentative ((G).completedBCHAction d ℒ)
      (mapRingHom Q φ).rangeS π :=
  (I.isPositive_grouping h c π u (fun i => by
    obtain ⟨p, -, -, hp⟩ := hQ i
    exact TauCeti.isPrimitive_def.mpr ⟨(AddMonoidHom.eval (ρ p)).toIntLinearMap, by simpa using hp⟩)
    hu
    Q hQ φ hc).isPositiveWallRepresentative

end Action

end Grouping

section FiniteAlphabet

open scoped Mei.TropicalVertexCoefficientAction

universe u

variable {R M ι E L : Type u} {V : Type*} [CommRing R] [AddCommGroup M] [Fintype E]
  [DecidableEq E] [AddCommGroup L] {m : E → M} {f : PositiveDegrees L}
  {τ : M × (E → ℤ) →+ L} (hτ : ∀ α, τ (PositiveDegrees.letter m α) ∈ f.monoid)
  (hτ0 : ∀ α, τ (PositiveDegrees.letter m α) ≠ 0) {π : L →+ M}
  (hπ : ∀ α, π (τ (PositiveDegrees.letter m α)) = m α)
  (I : HyperplaneTermInput (PositiveDegrees.finiteAlphabet m) (AddMonoidHom.fst M (E → ℤ)) ι E)

variable [Algebra ℚ R] [Module.Free ℤ L] [DecidableEq ι] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {j : M →+ V} (g : TauCeti.Toric.IsIntegralLattice j)
  (c : E → R) (u : ι → M) (hu : ∀ α, ∃ b : ℕ, 0 < b ∧ (I.exponent α).1 = b • u (I.wallIndex α))
  (Q : AddSubmonoid L) [Fact (f.monoid ≤ Q)] (hQ : ∀ i, ∃ p ∈ Q, -p ∈ Q ∧ I.normal i (π p) = 1)
  {S : Type*} [Semiring S] (φ : S →+* R) (hc : ∀ α, c α ∈ φ.rangeS)

include hu hQ hc in
/-- **Positivity of lifted wall functions.** For an input on the finite alphabet with exponents
`x_α`, if the first coordinates of the `x_α` on each hyperplane `i` are positive multiples of
one direction `u_i` of `M`, the coefficients lie in the image of `φ : S →+* R`, and `Q`
contains `±p` for a degree `p` with `μ_i(π p) = 1` on each hyperplane, then the ray
presentation of the lifted walls `1 + ∑ c_α z^{τ x_α}` is a positive wall representative for
the image of `S[Q]` and the projection `π`. -/
theorem isPositiveWallRepresentative_liftFiniteAlphabet_diagram :
    ((I.liftFiniteAlphabet hτ hτ0 hπ).diagram g c).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration (R := R) f Q).completedBCHAction f
        (tropicalVertexGrading (R := R) f π)) (mapRingHom Q φ).rangeS π :=
  (I.liftFiniteAlphabet hτ hτ0 hπ).isPositiveWallRepresentative_diagram g c π u
    (I.liftFiniteAlphabet_projectedDirection hτ hτ0 hπ u hu) Q (by simpa using hQ) φ hc

end FiniteAlphabet

end Mei.HyperplaneTermInput
