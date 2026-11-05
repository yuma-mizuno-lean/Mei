/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Grouping
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Pushforward
public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Translation
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness
public import Mei.Algebra.PositiveDegrees.Examples
public import Mei.Algebra.PositiveDegrees.Basis

/-!
# Examples of rank-two polynomial inputs

## A horizontal line

Take `L = M = ℤ²`, `π = id`, the even quadrant `P = 2ℕe₁ + ℕe₂` with `δ(a, b) = a + b`
(`Mei.PositiveDegrees.Examples.evenOrthant`), and the horizontal incoming line `{y = 0}` with
wall function `1 + c z^{2e₁}` (`RankTwoPolynomialInput.Examples.horizontalInput`). The primitive
generator `e₁` of the horizontal ray is not an allowed degree, but its ray is supported by
`2e₁`, and it is the only supported ray tangent to the line
(`RankTwoPolynomialInput.Examples.eq_evenHorizontalRay`). Hence the incoming diagram has a single
wall, on the supported primitive ray `e₁`, and the logarithm of `1 + c z^{2e₁}` is supported on
`2ℕ_{>0}e₁` (`RankTwoPolynomialInput.Examples.exists_eq_of_logComponent_initialLabel_ne_zero`).
Being a single full hyperplane, the diagram is consistent, so with no further walls it is its
own outgoing completion (`RankTwoPolynomialInput.Examples.isOutgoingCompletion`), and for the
independent variable `c` it is a positive wall representative
(`RankTwoPolynomialInput.Examples.isPositiveWallRepresentative`). The horizontal input is an
instance of Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*,
Theorem 9.9 (arXiv:2503.03719v1). The consistency uses
`DirectedDiagram.consistent_of_support_eq`.

Matched groups of other representatives have the same wall function on the line. Every point
`θ` of the line is regular, so with a direction `v` crossing the line negatively it is a
crossing germ of the group of the line at every order
(`RankTwoPolynomialInput.Examples.isCrossingGerm_incomingGrouping`).
Let `E` be any diagram equivalent to the incoming diagram, and let a grouping of `E` have a group
with crossing germs at `θ` and `v` at every order, containing a wall with the same normal. Then
every wall function of that group is `1 + c z^{2e₁}`, with coefficients in `ℕ[c]`
(`RankTwoPolynomialInput.Examples.eq_completedInitialFunction_of_equivalent`), by
`DirectedDiagram.FunctionWallGrouping.IsWallFunction.eq_of_equivalent` and
`DirectedDiagram.FunctionWallGrouping.IsWallFunction.isPositive_of_equivalent`.

## Enlarging the positive degrees

The identity of `ℤ²` is a positive degree map from the even quadrant to the quadrant
`ℕ² = ℕe₁ + ℕe₂`, with the same coordinate-sum degree
(`RankTwoPolynomialInput.Examples.evenOrthantInclusion`). Pushing forward along it
(`DirectedWall.Pushforward.ofTropicalDegreeMap`) keeps the support and the normal of the
horizontal wall and its label as a tropical vertex field, but replaces the positive monoid
`2ℕe₁ + ℕe₂` by `ℕ²`, and with it the supported rays and the truncations. The pushed
single-wall diagram is an outgoing completion of the pushed incoming wall
(`RankTwoPolynomialInput.Examples.isOutgoingCompletion_pushforward`), and the pushed incoming
diagram is a positive wall representative for the tropical vertex action of `ℕ²` on
`ℚ[c][[ℤ²]]` (`RankTwoPolynomialInput.Examples.isPositiveWallRepresentative_pushforward`), by
`DirectedDiagram.IsPositiveWallRepresentative.pushforward_ofTropicalDegreeMap_rangeS`.

## Three concurrent lines

The lines `{y = 0}`, `{x = 0}` and `{x = y}`, with wall functions `1 + c z^{2e₁}`, `1 + c z^{e₂}`
and `1 + c z^{2e₁ + 2e₂}` on the same quadrant, are pairwise transverse
(`RankTwoPolynomialInput.Examples.isTransverse_concurrentInput`) and all pass through the
origin, so they are not in general position
(`RankTwoPolynomialInput.Examples.not_isGenericOn_concurrentInput`). Translating the diagonal
line to `{x - y = 1}` puts them in general position
(`RankTwoPolynomialInput.Examples.isGenericOn_translate_concurrentInput`): the third coorientation
is the difference of the first two. This example only illustrates general position: no outgoing
completion or consistency statement is proved for it.
-/

public section

noncomputable section

namespace Mei.RankTwoPolynomialInput.Examples

open PositiveDegrees.Examples

/-- The horizontal line `{y = 0}` of `ℤ²` with the wall function `1 + c z^{2e₁}`, on the even
quadrant with the coordinate-sum degree. -/
def horizontalInput : RankTwoPolynomialInput evenOrthant (ℤ × ℤ) Unit where
  projection := AddMonoidHom.id _
  projection_surjective := Function.surjective_id
  finrank_eq_two := by simp
  tangent _ := (1, 0)
  isPrimitive_tangent _ := TauCeti.isPrimitive_def.mpr ⟨LinearMap.fst ℤ ℤ ℤ, rfl⟩
  normal _ := LinearMap.snd ℤ ℤ ℤ
  isPrimitive_normal _ := TauCeti.isPrimitive_def.mpr ⟨Module.Dual.eval ℤ _ (0, 1), rfl⟩
  normal_tangent _ := rfl
  offset _ := 0
  exponents _ := {(2, 0)}
  mem_monoid_of_mem_exponents {_ n} hn := by
    rw [Finset.mem_singleton] at hn
    subst hn
    simp
  ne_zero_of_mem_exponents {_ n} hn := by
    rw [Finset.mem_singleton] at hn
    subst hn
    simp
  exists_projection_eq_of_mem_exponents {_ n} hn := by
    rw [Finset.mem_singleton] at hn
    subst hn
    exact ⟨2, two_pos, by simp⟩
  finite_nontrivial _ := Set.toFinite _

/-- The projection of the horizontal input is the identity of `ℤ²`. -/
@[simp]
theorem horizontalInput_projection : horizontalInput.projection = AddMonoidHom.id (ℤ × ℤ) :=
  (rfl)

/-- The tangent of the horizontal line is `e₁`. -/
@[simp]
theorem horizontalInput_tangent (j : Unit) : horizontalInput.tangent j = (1, 0) := (rfl)

/-- The cylinder normal of the horizontal line is the second coordinate. -/
@[simp]
theorem wallNormal_horizontalInput (j : Unit) (q : ℤ × ℤ) :
    horizontalInput.wallNormal j q = q.2 :=
  horizontalInput.wallNormal_apply j q

/-- The only supported ray tangent to the horizontal line is the horizontal ray, with
primitive generator `e₁`. -/
theorem eq_evenHorizontalRay (w : SupportedRay evenOrthant)
    (hw : horizontalInput.wallNormal () w.generator = 0) : w = evenHorizontalRay := by
  obtain ⟨⟨x, y⟩, hprim, a, ha, hmem⟩ := w
  simp only [wallNormal_horizontalInput] at hw
  subst hw
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hprim
  have hx : x * f (1, 0) = 1 := by
    have he : ((x, 0) : ℤ × ℤ) = x • ((1, 0) : ℤ × ℤ) := by simp
    rwa [he, map_zsmul, smul_eq_mul] at hf
  rw [evenOrthant_monoid] at hmem
  have hax : 0 ≤ a * x := by simpa using (mem_evenOrthantMonoid.mp hmem).1
  have hx0 : 0 ≤ x := nonneg_of_mul_nonneg_right (by linarith [mul_comm a x]) ha
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hx with rfl | rfl
  · exact SupportedRay.ext evenHorizontalRay_generator.symm
  · omega

/-- The incoming walls of the horizontal input are indexed by the horizontal ray alone. -/
instance : Unique horizontalInput.IncomingIndex where
  default := ⟨(), evenHorizontalRay, by simp⟩
  uniq := by
    rintro ⟨⟨⟩, w, hw⟩
    obtain rfl := eq_evenHorizontalRay w hw
    rfl

variable {R : Type*} [CommRing R] [Algebra ℚ R] (c : horizontalInput.Variable → R)

local notation "ρ" => AddMonoidHom.id (ℤ × ℤ)
local notation "ℒ" => tropicalVertexGrading (R := R) evenOrthant ρ

/-- The logarithm of `1 + c z^{2e₁}` is supported on `2ℕ_{>0}e₁`. -/
theorem exists_eq_of_logComponent_initialLabel_ne_zero {q : ℤ × ℤ}
    (hq : evenOrthant.logComponent ℒ (horizontalInput.initialLabel c ()) q ≠ 0) :
    ∃ a : ℤ, 0 < a ∧ q = (2 * a, 0) := by
  obtain ⟨hqP, -⟩ := evenOrthant.mem_monoid_and_ne_zero_of_logComponent_ne_zero ℒ hq
  obtain ⟨k, hk, hkq⟩ :=
    horizontalInput.exists_projection_eq_of_logComponent_initialLabel_ne_zero c () hq
  simp only [horizontalInput_projection, horizontalInput_tangent, AddMonoidHom.id_apply] at hkq
  rw [evenOrthant_monoid] at hqP
  obtain ⟨-, -, b, hb⟩ := mem_evenOrthantMonoid.mp hqP
  simp only [hkq, Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero] at hb ⊢
  exact ⟨b, by omega, by simp only [Prod.mk.injEq, and_true]; omega⟩

variable {latticeMap : ℤ × ℤ →+ ℝ × ℝ} (h : TauCeti.Toric.IsIntegralLattice latticeMap)

local notation "H" => tropicalVertexWallSpaces (R := R) evenOrthant ρ

/-- The single wall of the horizontal input lies on the supported primitive ray `e₁`. -/
theorem incomingDiagram_ray_eq (j : horizontalInput.IncomingIndex) :
    ((horizontalInput.incomingDiagram h c).wall j).ray = evenHorizontalRay := by
  rw [incomingDiagram_ray]
  exact eq_evenHorizontalRay _ j.2.property

/-- The incoming diagram of the horizontal input, with no additional walls. -/
def completionDiagram :
    DirectedDiagram (d := evenOrthant) h (H) (horizontalInput.IncomingIndex ⊕ PEmpty) where
  wall := Sum.elim (horizontalInput.incomingDiagram h c).wall PEmpty.elim
  finite_active k := by
    apply (((horizontalInput.incomingDiagram h c).finite_active k).image Sum.inl).subset
    rintro (j | j) hj
    · exact ⟨j, hj, rfl⟩
    · exact j.elim

/-- The walls of the completion diagram are the incoming walls. -/
@[simp]
theorem completionDiagram_wall_inl (j : horizontalInput.IncomingIndex) :
    (completionDiagram c h).wall (Sum.inl j) = (horizontalInput.incomingDiagram h c).wall j :=
  (rfl)

/-- The single-wall incoming diagram of the horizontal input is its own outgoing completion:
it is consistent, being a single full hyperplane, and has no further walls. -/
theorem isOutgoingCompletion :
    DirectedDiagram.IsOutgoingCompletion (horizontalInput.incomingDiagram h c).wall
      (completionDiagram c h) where
  wall_inl := completionDiagram_wall_inl c h
  outgoing_inr j := j.elim
  consistent := by
    let : Unique (horizontalInput.IncomingIndex ⊕ PEmpty) := (Equiv.sumEmpty _ _).unique
    obtain ⟨a, ha⟩ := horizontalInput.incomingDiagram_full h c default
    refine DirectedDiagram.consistent_of_support_eq
      (W := (horizontalInput.incomingDiagram h c).wall default) ?_ a ha
    rintro (j | j)
    · rw [completionDiagram_wall_inl, Unique.eq_default j]
    · exact j.elim

open scoped Mei.TropicalVertexCoefficientAction

local instance : Fact (evenOrthant.monoid ≤ (⊤ : AddSubmonoid (ℤ × ℤ))) := ⟨le_top⟩

/-- For the independent variable `c`, the incoming diagram of the horizontal input is a
positive wall representative: its wall function `1 + c z^{2e₁}` has coefficients in `ℕ[c]`. -/
theorem isPositiveWallRepresentative :
    (horizontalInput.incomingDiagram h MvPolynomial.X).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration
        (R := MvPolynomial horizontalInput.Variable ℚ) evenOrthant ⊤).completedBCHAction
          evenOrthant (tropicalVertexGrading (R := MvPolynomial horizontalInput.Variable ℚ)
            evenOrthant ρ))
      (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid (ℤ × ℤ))
        (MvPolynomial.map (σ := horizontalInput.Variable) (Nat.castRingHom ℚ))).rangeS
      horizontalInput.projection :=
  horizontalInput.isPositiveWallRepresentative_incomingDiagram_variables h

/-- The horizontal line has offset zero. -/
@[simp]
theorem horizontalInput_offset (j : Unit) : horizontalInput.offset j = 0 := (rfl)

/-- A point `θ` of the horizontal line and a direction `v` pairing negatively with its normal
form a crossing germ of the group of the line at every order. -/
theorem isCrossingGerm_incomingGrouping {θ v : ℝ × ℝ}
    (hθ : h.realCharacter (horizontalInput.wallNormal ()) θ = 0)
    (hv : h.realCharacter (horizontalInput.wallNormal ()) v < 0) (k : ℕ) :
    (horizontalInput.incomingGrouping h c).IsCrossingGerm () k θ v where
  notMem_singularSupport :=
    (horizontalInput.incomingDiagram h c).notMem_singularSupport_of_support_eq (j₀ := default)
      (c := 0) (by simp) (fun j => by rw [Unique.eq_default j]) k θ
  mem_support_iff j := by simp [hθ]
  realCharacter_normal_neg j _ := by simpa using hv

section Representatives

/-- The completed coefficients `ℚ[c][[ℤ²]]` of the horizontal input over the even quadrant. -/
local notation "Fc" => TropicalVertexCoefficientAction.filtration
  (R := MvPolynomial horizontalInput.Variable ℚ) evenOrthant (⊤ : AddSubmonoid (ℤ × ℤ))

/-- **The wall function of the horizontal line in matched representatives.** Let `E` be any
directed diagram equivalent to the incoming diagram of the horizontal input over `ℚ[c]`, that
is, any representative of its completed class. Let `G'` be a grouping of `E` whose group `g'`
has, at every order, a crossing germ at a point `θ` of the line and a direction `v` pairing
negatively with its normal, and which contains a wall cooriented by the second coordinate. Then
every wall function of `g'` is `1 + c z^{2e₁}`, and it has coefficients in `ℕ[c]`. The crossing
germs of `g'` and its wall with that normal are hypotheses. -/
theorem eq_completedInitialFunction_of_equivalent {ι' κ' : Type*}
    {E : DirectedDiagram (d := evenOrthant) h
      (tropicalVertexWallSpaces (R := MvPolynomial horizontalInput.Variable ℚ) evenOrthant ρ) ι'}
    (hDE : (horizontalInput.incomingDiagram h MvPolynomial.X).Equivalent E)
    (G' : E.FunctionWallGrouping horizontalInput.projection κ') {g' : κ'} {θ v : ℝ × ℝ}
    (hθ : h.realCharacter (horizontalInput.wallNormal ()) θ = 0)
    (hv : h.realCharacter (horizontalInput.wallNormal ()) v < 0)
    (hgerm : ∀ k, G'.IsCrossingGerm g' k θ v) {j' : ι'} (hj' : G'.group j' = g')
    (hν : (E.wall j').normal = horizontalInput.wallNormal ())
    {f' : (Fc).completionˣ}
    (hf' : G'.IsWallFunction ((Fc).completedBCHAction evenOrthant
      (tropicalVertexGrading (R := MvPolynomial horizontalInput.Variable ℚ) evenOrthant ρ)) g' f') :
    f' = horizontalInput.completedInitialFunction MvPolynomial.X ⊤ () ∧
      (Fc).IsPositive (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid (ℤ × ℤ))
        (MvPolynomial.map (σ := horizontalInput.Variable) (Nat.castRingHom ℚ))).rangeS f' := by
  have hQ (i : Unit) : ∃ p : ℤ × ℤ, horizontalInput.wallNormal i p = 1 ∧
      p ∈ (⊤ : AddSubmonoid (ℤ × ℤ)) ∧ -p ∈ (⊤ : AddSubmonoid (ℤ × ℤ)) :=
    (horizontalInput.exists_wallNormal_eq_one i).imp fun _ hp => ⟨hp, trivial, trivial⟩
  have hgerm' (k : ℕ) : ∃ θ' v',
      (horizontalInput.incomingGrouping h (MvPolynomial.X (R := ℚ))).IsCrossingGerm () k θ' v' ∧
        G'.IsCrossingGerm g' k θ' v' :=
    ⟨θ, v, isCrossingGerm_incomingGrouping (MvPolynomial.X (R := ℚ)) h hθ hv k, hgerm k⟩
  have hν' : ((horizontalInput.incomingDiagram h (MvPolynomial.X (R := ℚ))).wall default).normal =
      (E.wall j').normal := by
    rw [incomingDiagram_normal, hν]
  refine ⟨((horizontalInput.isWallFunction_incomingGrouping h MvPolynomial.X ⊤ () (hQ ())
    ).eq_of_equivalent hDE hgerm' hf' (by simp) hj' hν').symm, ?_⟩
  exact hf'.isPositive_of_equivalent (horizontalInput.isPositive_incomingGrouping h
    MvPolynomial.X ⊤ hQ _ fun v => ⟨MvPolynomial.X v, MvPolynomial.map_X _ v⟩) hDE hgerm'
      (by simp) hj' hν'

end Representatives

section Orthant

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

local instance : Fact ((ℕ²).monoid ≤ (⊤ : AddSubmonoid (ℤ × ℤ))) := ⟨le_top⟩

/-- The identity of `ℤ²` as a positive degree map from the even quadrant to the quadrant `ℕ²`,
with identity cutoff modulus. -/
def evenOrthantInclusion : PositiveDegreeMap evenOrthant ℕ² :=
  PositiveDegreeMap.ofBound (AddMonoidHom.id _)
    (fun n hn => by
      simp only [evenOrthant_monoid, mem_evenOrthantMonoid] at hn
      simp [Fin.forall_fin_two, hn.1, hn.2.1])
    1 (fun n _ => by simp)

/-- The inclusion of the even quadrant is the identity of `ℤ²`. -/
@[simp]
theorem evenOrthantInclusion_apply (n : ℤ × ℤ) : evenOrthantInclusion n = n := by
  rw [evenOrthantInclusion, PositiveDegreeMap.ofBound_apply, AddMonoidHom.id_apply]

/-- The pushforward along the inclusion of the even quadrant into `ℕ²`. It keeps the
supports, the normals and the labels as tropical vertex fields; only the positive degrees,
and with them the supported rays and the truncations, change. -/
abbrev evenOrthantPushforward :
    DirectedWall.Pushforward evenOrthant ℕ² h h
      (tropicalVertexWallSpaces (R := MvPolynomial horizontalInput.Variable ℚ) evenOrthant ρ)
      (tropicalVertexWallSpaces ℕ² ρ) :=
  DirectedWall.Pushforward.ofTropicalDegreeMap evenOrthantInclusion (fun n _ => by simp)

/-- Pushed to the quadrant `ℕ²`, the single-wall diagram of the horizontal input over the even
quadrant is still an outgoing completion of its incoming wall. -/
theorem isOutgoingCompletion_pushforward :
    DirectedDiagram.IsOutgoingCompletion
      (fun j => ((horizontalInput.incomingDiagram h MvPolynomial.X).wall j).pushforward
        (evenOrthantPushforward h))
      ((completionDiagram MvPolynomial.X h).pushforward (evenOrthantPushforward h)) :=
  (isOutgoingCompletion MvPolynomial.X h).pushforward

/-- Pushed to the quadrant `ℕ²`, the incoming diagram of the horizontal input is a positive wall
representative for the tropical vertex action of `ℕ²` on `ℚ[c][[ℤ²]]`: its grouped wall function
is still `1 + c z^{2e₁}`, with coefficients in `ℕ[c]`. -/
theorem isPositiveWallRepresentative_pushforward :
    ((horizontalInput.incomingDiagram h MvPolynomial.X).pushforward
        (evenOrthantPushforward h)).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration
        (R := MvPolynomial horizontalInput.Variable ℚ) ℕ² ⊤).completedBCHAction
          ℕ² (tropicalVertexGrading (R := MvPolynomial horizontalInput.Variable ℚ) ℕ² ρ))
      (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid (ℤ × ℤ))
        (MvPolynomial.map (σ := horizontalInput.Variable) (Nat.castRingHom ℚ))).rangeS
      horizontalInput.projection :=
  (isPositiveWallRepresentative h).pushforward_ofTropicalDegreeMap_rangeS _ _ (AddMonoidHom.id _)
    (fun q => by simp) Function.surjective_id (fun q _ => by simp) (fun n _ => by simp) _

end Orthant

section Concurrent

/-- The lines `{y = 0}`, `{x = 0}` and `{x = y}` of `ℤ²`, with the wall functions
`1 + c z^{2e₁}`, `1 + c z^{e₂}` and `1 + c z^{2e₁ + 2e₂}`, on the even quadrant with the
coordinate-sum degree. -/
def concurrentInput : RankTwoPolynomialInput evenOrthant (ℤ × ℤ) (Fin 3) where
  projection := AddMonoidHom.id _
  projection_surjective := Function.surjective_id
  finrank_eq_two := by simp
  tangent := ![(1, 0), (0, 1), (1, 1)]
  isPrimitive_tangent j := by
    fin_cases j
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.fst ℤ ℤ ℤ, rfl⟩
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.snd ℤ ℤ ℤ, rfl⟩
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.fst ℤ ℤ ℤ, rfl⟩
  normal := ![LinearMap.snd ℤ ℤ ℤ, LinearMap.fst ℤ ℤ ℤ, LinearMap.fst ℤ ℤ ℤ - LinearMap.snd ℤ ℤ ℤ]
  isPrimitive_normal j := by
    fin_cases j
    · exact TauCeti.isPrimitive_def.mpr ⟨Module.Dual.eval ℤ _ (0, 1), rfl⟩
    · exact TauCeti.isPrimitive_def.mpr ⟨Module.Dual.eval ℤ _ (1, 0), rfl⟩
    · exact TauCeti.isPrimitive_def.mpr ⟨Module.Dual.eval ℤ _ (1, 0), rfl⟩
  normal_tangent j := by
    fin_cases j <;> rfl
  offset _ := 0
  exponents j := {![(2, 0), (0, 1), (2, 2)] j}
  mem_monoid_of_mem_exponents {j n} hn := by
    obtain rfl := Finset.mem_singleton.mp hn
    fin_cases j <;> simp
  ne_zero_of_mem_exponents {j n} hn := by
    obtain rfl := Finset.mem_singleton.mp hn
    fin_cases j <;> simp
  exists_projection_eq_of_mem_exponents {j n} hn := by
    obtain rfl := Finset.mem_singleton.mp hn
    fin_cases j
    · exact ⟨2, two_pos, by simp⟩
    · exact ⟨1, one_pos, by simp⟩
    · exact ⟨2, two_pos, by simp⟩
  finite_nontrivial _ := Set.toFinite _

/-- The coorientations of the three lines are `y`, `x` and `x - y`. -/
@[simp]
theorem concurrentInput_normal :
    concurrentInput.normal =
      ![LinearMap.snd ℤ ℤ ℤ, LinearMap.fst ℤ ℤ ℤ, LinearMap.fst ℤ ℤ ℤ - LinearMap.snd ℤ ℤ ℤ] :=
  (rfl)

/-- The three lines pass through the origin. -/
@[simp]
theorem concurrentInput_offset (j : Fin 3) : concurrentInput.offset j = 0 := (rfl)

/-- Distinct lines of the concurrent input are transverse. -/
theorem isTransverse_concurrentInput {a b : Fin 3} (hab : a ≠ b) :
    concurrentInput.IsTransverse a b := by
  refine isTransverse_iff.mpr (LinearIndependent.pair_iff.mpr fun s t hst => ?_)
  have h₁ := DFunLike.congr_fun hst ((1, 0) : ℤ × ℤ)
  have h₂ := DFunLike.congr_fun hst ((0, 1) : ℤ × ℤ)
  clear hst
  fin_cases a <;> fin_cases b <;> simp_all

/-- The cylinder normal of the diagonal line is the difference of the other two. -/
theorem realCharacter_wallNormal_concurrentInput_two (x : ℝ × ℝ) :
    h.realCharacter (concurrentInput.wallNormal 2) x =
      h.realCharacter (concurrentInput.wallNormal 1) x -
        h.realCharacter (concurrentInput.wallNormal 0) x := by
  have hsub : concurrentInput.normal 2 = concurrentInput.normal 1 - concurrentInput.normal 0 := by
    simp [concurrentInput_normal]
  have hrel : (1 : ℤ) • concurrentInput.normal 2 =
      (-1 : ℤ) • concurrentInput.normal 0 + (1 : ℤ) • concurrentInput.normal 1 := by
    rw [one_smul, one_smul, neg_one_smul, hsub, sub_eq_neg_add]
  have := realCharacter_wallNormal_of_smul_normal_eq (h := h) hrel x
  push_cast at this
  linarith

/-- The three lines all pass through the origin, so they are not in general position. -/
theorem not_isGenericOn_concurrentInput : ¬ concurrentInput.IsGenericOn h Set.univ := by
  intro hgen
  have h0 : (0 : ℝ × ℝ) ∈ concurrentInput.cylinder h 0 ∩ concurrentInput.cylinder h 1 ∩
      concurrentInput.cylinder h 2 := by
    simp
  rw [hgen.inter_eq_empty trivial trivial trivial (isTransverse_concurrentInput (by decide))
    (isTransverse_concurrentInput (by decide)) (isTransverse_concurrentInput (by decide))] at h0
  exact h0

/-- After translating the diagonal line to `{x - y = 1}`, the three lines are in general
position. -/
theorem isGenericOn_translate_concurrentInput :
    (concurrentInput.translate ![0, 0, 1]).IsGenericOn h Set.univ := by
  refine isGenericOn_iff.mpr fun a _ b _ c _ hab hac hbc => ?_
  have hab := isTransverse_translate.mp hab
  have hac := isTransverse_translate.mp hac
  have hbc := isTransverse_translate.mp hbc
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  simp only [Set.mem_inter_iff, mem_cylinder_translate, concurrentInput_offset, zero_add] at hx
  have h₂ := realCharacter_wallNormal_concurrentInput_two h x
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first
    | exact hab.ne rfl
    | exact hac.ne rfl
    | exact hbc.ne rfl
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] at hx; linarith)

end Concurrent

end Mei.RankTwoPolynomialInput.Examples
