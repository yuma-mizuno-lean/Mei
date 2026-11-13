/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Specialization
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RestrictScalars
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Specialization
public import Mei.Algebra.Lie.Logarithmic.Positive
import Mei.RingTheory.FilteredAlgebra.Algebra

/-!
# Positive wall representatives under changes of the coefficient ring

Let `D` be a directed diagram for wall spaces over a commutative `ℚ`-algebra `R`, and `K` a
smaller scalar ring. A function-wall grouping of `D` is a grouping of its restriction of scalars
`D.restrictScalars K`, and conversely, with the same groups
(`DirectedDiagram.FunctionWallGrouping.restrictScalars`,
`DirectedDiagram.FunctionWallGrouping.ofRestrictScalars`); the completed group labels
correspond under the scalar-restriction comparison of completed BCH groups. If an action `σK` of
the restricted completed group is the action `σ` of the original group composed with that
comparison, the two groupings have the same wall functions and the same positivity, so
restriction of scalars preserves and reflects positive wall representatives
(`DirectedDiagram.isPositiveWallRepresentative_restrictScalars_iff`).

Combined with the fixed-degree positive specializations of
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Specialization`, this gives positive
specializations across a change of the coefficient ring. Let `f` be a `K`-linear fixed-degree
graded Lie map of the restricted gradings preserving the restricted wall spaces. A
`DirectedDiagram.PositiveCoefficientChange` along `f` consists of actions of the restricted
completed groups that are the original actions through the scalar-restriction comparisons, and a
positive specialization of completed coefficients that intertwines them along `f` and fixes the
monomials, such that the target action fixes the constants. For such data the
coefficient change `DirectedDiagram.mapRestrictScalars` sends positive wall representatives to
positive wall representatives (`DirectedDiagram.IsPositiveWallRepresentative.mapRestrictScalars`),
and positive wall representatives of outgoing completions to positive wall representatives of
outgoing completions of the image input
(`DirectedDiagram.IsOutgoingCompletion.isPositiveWallRepresentative_mapRestrictScalars`). If the
scattering class of a full-hyperplane input has a positive wall representative, so does the
scattering class of the image input
(`DirectedDiagram.Class.HasPositiveWallRepresentative.scat_mapRestrictScalars`).

For the tropical vertex algebra, let `φ : R → S` be a homomorphism of `ℚ`-algebras whose
coefficientwise map `R[Q] → S[Q]` sends a positive subsemiring `P` into `P'`. The coefficient
specialization `z^n ∂_m ↦ z^n ∂_(φ ∘ m)` (`LogarithmicVectorField.coefficientMonoidGradedLieHom`
with trivial twist) preserves the restricted tropical vertex wall spaces, and all the hypotheses
above hold for the monoid-local positive specialization
`LogarithmicVectorField.coefficientMonoidPositiveSpecialization`, the target action fixing the
constants because it is `S`-linear
(`DirectedDiagram.coefficientMonoidPositiveCoefficientChange`). Hence changing the coefficients
along `φ` preserves positive wall representatives
(`DirectedDiagram.IsPositiveWallRepresentative.coefficientMonoidGradedLieHom`),
outgoing completions with positive wall representatives
(`DirectedDiagram.IsOutgoingCompletion.isPositiveWallRepresentative_coefficientMonoidGradedLieHom`)
and the existence of positive wall representatives of scattering classes
(`DirectedDiagram.Class.HasPositiveWallRepresentative.scat_coefficientMonoidGradedLieHom`). This
is the statement, for tropical vertex coefficient changes with fixed supports and normals and
grouped wall functions mapped by `φ`, that positive specializations along coefficient maps of
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i)
(arXiv:1503.06183v5), preserve outgoing completions and the positivity of the grouped wall
functions of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), as used for coefficient specializations in Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, §8.1 (arXiv:2503.03719v1). Monomial twists are not
covered, since the transfer of wall functions requires the monomials to be fixed.
-/

public section

open TauCeti (AlgFiltration)

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading GradedLieHom)

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei.DirectedDiagram

open _root_.AddMonoidAlgebra

universe u v w t

section RestrictScalars

variable {Γ Λ K R V M : Type*} {L : Type u} {ι : Type v} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing K] [CommRing R] [Algebra ℚ K] [Algebra ℚ R] [SMul K R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra K L] [LieAlgebra ℚ L]
  [IsScalarTower K R L] [IsScalarTower ℚ K L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup M]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h H ι} {π : Γ →+ M} {κ : Type*}

namespace FunctionWallGrouping

variable (K) in
/-- A function-wall grouping of a diagram is a grouping of its restriction of scalars, with the
same groups: supports, normals and supported rays are unchanged, and a restricted label is
trivial exactly when the original label is. -/
def restrictScalars (G : D.FunctionWallGrouping π κ) :
    (D.restrictScalars K).FunctionWallGrouping π κ where
  group := G.group
  support_eq hj := by
    simpa only [restrictScalars_wall, DirectedWall.restrictScalars_support] using G.support_eq hj
  normal_eq hj := by
    simpa only [restrictScalars_wall, DirectedWall.restrictScalars_normal] using G.normal_eq hj
  projectedDirection_eq {j j'} hj hj1 hj'1 := by
    simp only [restrictScalars_wall, DirectedWall.restrictScalars_ray, ne_eq,
      DirectedWall.restrictScalars_label_eq_one_iff] at hj1 hj'1 ⊢
    exact G.projectedDirection_eq hj hj1 hj'1
  isPrimitive_normal j := by
    simpa only [restrictScalars_wall, DirectedWall.restrictScalars_normal] using
      G.isPrimitive_normal j

/-- A function-wall grouping of the restriction of scalars of a diagram is a grouping of the
diagram, with the same groups. -/
def ofRestrictScalars (G : (D.restrictScalars K).FunctionWallGrouping π κ) :
    D.FunctionWallGrouping π κ where
  group := G.group
  support_eq hj := by
    simpa only [restrictScalars_wall, DirectedWall.restrictScalars_support] using G.support_eq hj
  normal_eq hj := by
    simpa only [restrictScalars_wall, DirectedWall.restrictScalars_normal] using G.normal_eq hj
  projectedDirection_eq {j j'} hj hj1 hj'1 := by
    have h := G.projectedDirection_eq hj
    simp only [restrictScalars_wall, DirectedWall.restrictScalars_ray, ne_eq,
      DirectedWall.restrictScalars_label_eq_one_iff] at h
    exact h hj1 hj'1
  isPrimitive_normal j := by
    simpa only [restrictScalars_wall, DirectedWall.restrictScalars_normal] using
      G.isPrimitive_normal j

variable (G : D.FunctionWallGrouping π κ) (G' : (D.restrictScalars K).FunctionWallGrouping π κ)

/-- The restricted grouping places every wall in its original group. -/
@[simp]
theorem restrictScalars_group (j : ι) : (G.restrictScalars K).group j = G.group j := (rfl)

/-- The unrestricted grouping places every wall in its original group. -/
@[simp]
theorem ofRestrictScalars_group (j : ι) : G'.ofRestrictScalars.group j = G'.group j := (rfl)

/-- The finite scalar-restriction comparison sends the group labels of a grouping of the
restriction to the group labels of the corresponding grouping of `D`. -/
theorem bchGroupEquiv_groupLabel_restrictScalars (g : κ) (k : ℕ) :
    (d.truncatedRestrictScalarsEquiv (R := K) ℒ k).bchGroupEquiv (G'.groupLabel g k) =
      G'.ofRestrictScalars.groupLabel g k := by
  classical
  let s := (Set.toFinite (D.active k)).toFinset.filter fun j => G'.group j = g
  have hs : ∀ j ∈ s, G'.group j = g := fun j hj => (Finset.mem_filter.mp hj).2
  have hact : ∀ j ∈ D.active k, G'.group j = g → j ∈ s := fun j hj hg =>
    Finset.mem_filter.mpr ⟨(Set.toFinite _).mem_toFinset.mpr hj, hg⟩
  rw [G'.groupLabel_eq_noncommProd g k s hs fun j hj => hact j (by simpa using hj),
    G'.ofRestrictScalars.groupLabel_eq_noncommProd g k s hs hact]
  refine (Finset.map_noncommProd s _ _ _).trans (Finset.noncommProd_congr rfl (fun j _ => ?_) _)
  exact D.bchGroupEquiv_projection_restrictScalars_wall_label k j

/-- The completed group labels of a grouping of the restriction correspond to those of the
corresponding grouping of `D` under the scalar-restriction comparison. -/
@[simp]
theorem completedBCHRestrictScalarsEquiv_label (g : κ) :
    d.completedBCHRestrictScalarsEquiv (R := K) ℒ (G'.label g) = G'.ofRestrictScalars.label g := by
  refine (G'.ofRestrictScalars.eq_label_iff g _).mpr fun k => ?_
  rw [PositiveDegrees.projection_completedBCHRestrictScalarsEquiv, projection_label,
    ← LieEquiv.coe_bchGroupEquiv, MonoidHom.coe_ofClass,
    bchGroupEquiv_groupLabel_restrictScalars]

/-- Restricting and then unrestricting a grouping recovers it. -/
@[simp]
theorem ofRestrictScalars_restrictScalars : (G.restrictScalars K).ofRestrictScalars = G := by
  ext j
  rw [ofRestrictScalars_group, restrictScalars_group]

/-- Unrestricting and then restricting a grouping of the restriction recovers it. -/
@[simp]
theorem restrictScalars_ofRestrictScalars : G'.ofRestrictScalars.restrictScalars K = G' := by
  ext j
  rw [restrictScalars_group, ofRestrictScalars_group]

/-- The completed group labels of the restricted grouping are the inverse images of the group
labels under the scalar-restriction comparison. -/
theorem label_restrictScalars (g : κ) :
    (G.restrictScalars K).label g = (d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm
      (G.label g) := by
  rw [MulEquiv.eq_symm_apply, completedBCHRestrictScalarsEquiv_label,
    ofRestrictScalars_restrictScalars]

section WallFunction

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra K A]
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}
  {σK : d.completedBCHGroup (fun n => (ℒ n).restrictScalars K) →*
    (F.completion ≃ₐ[K] F.completion)}
  (hσ : ∀ g x, σK g x = σ (d.completedBCHRestrictScalarsEquiv (R := K) ℒ g) x)
  {P : Subsemiring (AddMonoidAlgebra A Q)}

include hσ

/-- If the restricted action is the original action composed with the scalar-restriction
comparison, a grouping of the restriction has the wall functions of the corresponding grouping
of `D`. -/
theorem isWallFunction_iff_ofRestrictScalars (g : κ) (u : F.completionˣ) :
    G'.IsWallFunction σK g u ↔ G'.ofRestrictScalars.IsWallFunction σ g u := by
  simp only [isWallFunction_iff, hσ, completedBCHRestrictScalarsEquiv_label,
    ofRestrictScalars_group, restrictScalars_wall, DirectedWall.restrictScalars_normal]

/-- Under the hypothesis of `isWallFunction_iff_ofRestrictScalars`, a grouping of the
restriction is positive exactly when the corresponding grouping of `D` is. -/
theorem isPositive_iff_ofRestrictScalars :
    G'.IsPositive σK P ↔ G'.ofRestrictScalars.IsPositive σ P := by
  simp only [isPositive_iff, G'.isWallFunction_iff_ofRestrictScalars hσ]

end WallFunction

end FunctionWallGrouping

section WallFunction

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra K A]
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}
  {σK : d.completedBCHGroup (fun n => (ℒ n).restrictScalars K) →*
    (F.completion ≃ₐ[K] F.completion)}
  (hσ : ∀ g x, σK g x = σ (d.completedBCHRestrictScalarsEquiv (R := K) ℒ g) x)
  {P : Subsemiring (AddMonoidAlgebra A Q)}

include hσ

variable (D) in
/-- If the restricted action is the original action composed with the scalar-restriction
comparison, restriction of scalars preserves and reflects positive wall representatives. -/
theorem isPositiveWallRepresentative_restrictScalars_iff :
    (D.restrictScalars K).IsPositiveWallRepresentative σK P π ↔
      D.IsPositiveWallRepresentative σ P π := by
  rw [isPositiveWallRepresentative_iff, isPositiveWallRepresentative_iff]
  refine ⟨fun ⟨κ, G, hG⟩ => ⟨κ, G.ofRestrictScalars,
    (G.isPositive_iff_ofRestrictScalars hσ).mp hG⟩, fun ⟨κ, G, hG⟩ => ⟨κ, G.restrictScalars K, ?_⟩⟩
  rw [(G.restrictScalars K).isPositive_iff_ofRestrictScalars hσ,
    FunctionWallGrouping.ofRestrictScalars_restrictScalars]
  exact hG

end WallFunction

section Map

variable {S : Type*} {L' : Type u} [CommRing S] [Algebra ℚ S] [SMul K S]
  [LieRing L'] [LieAlgebra S L'] [LieAlgebra K L'] [LieAlgebra ℚ L']
  [IsScalarTower K S L'] [IsScalarTower ℚ K L'] [IsScalarTower ℚ S L']
  {ℳ : Γ → Submodule S L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]
  {H' : DirectedWallSpaces ρ ℳ}
  (f : GradedLieHom (PositiveDegreeMap.id d) (fun n => (ℒ n).restrictScalars K)
    (fun n => (ℳ n).restrictScalars K))
  (hf : ∀ n m, ∀ x ∈ (H.restrictScalars K).wall n m, f x ∈ (H'.restrictScalars K).wall n m)
  {A A' : Type*} [CommRing A] [CommRing A'] [Algebra R A] [Algebra K A]
  [Algebra S A'] [Algebra K A']
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  {F' : AlgFiltration (AddMonoidAlgebra A' Q)}

variable (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion))
  (σ' : d.completedBCHGroup ℳ →* (F'.completion ≃ₐ[S] F'.completion))
  (P : Subsemiring (AddMonoidAlgebra A Q)) (P' : Subsemiring (AddMonoidAlgebra A' Q)) in
/-- A positive specialization of completed coefficients compatible with a change of the
coefficient ring along a `K`-linear fixed-degree graded Lie map `f` of the restricted gradings:
actions `restrictedAction` and `restrictedAction'` of the restricted completed groups that are
the actions `σ` and `σ'` composed with the scalar-restriction comparisons, and a positive
specialization `specialization` from `P` to `P'` that intertwines them along `f`, fixes the
monomials, and such that `σ'` fixes the constants. -/
@[ext]
structure PositiveCoefficientChange where
  /-- The action of the restricted completed source group. -/
  restrictedAction : d.completedBCHGroup (fun n => (ℒ n).restrictScalars K) →*
    (F.completion ≃ₐ[K] F.completion)
  /-- The action of the restricted completed target group. -/
  restrictedAction' : d.completedBCHGroup (fun n => (ℳ n).restrictScalars K) →*
    (F'.completion ≃ₐ[K] F'.completion)
  /-- The restricted source action is `σ` through the scalar-restriction comparison. -/
  restrictedAction_apply (g x) :
    restrictedAction g x = σ (d.completedBCHRestrictScalarsEquiv (R := K) ℒ g) x
  /-- The restricted target action is `σ'` through the scalar-restriction comparison. -/
  restrictedAction'_apply (g x) :
    restrictedAction' g x = σ' (d.completedBCHRestrictScalarsEquiv (R := K) ℳ g) x
  /-- The positive specialization of completed coefficients. -/
  specialization : PositiveSpecialization F F' P P'
  /-- The specialization intertwines the restricted actions along `f`. -/
  completionMap_restrictedAction (g x) : specialization.completionMap (restrictedAction g x) =
    restrictedAction' (f.completedMap g) (specialization.completionMap x)
  /-- The specialization fixes the monomials. -/
  toRingHom_single_one (p : Q) : specialization.toRingHom (single p 1) = single p 1
  /-- The target action fixes the constants. -/
  action_single_zero (g) (c : A') :
    σ' g (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c)

variable {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}
  {σ' : d.completedBCHGroup ℳ →* (F'.completion ≃ₐ[S] F'.completion)}
  {P : Subsemiring (AddMonoidAlgebra A Q)} {P' : Subsemiring (AddMonoidAlgebra A' Q)}
  (c : PositiveCoefficientChange f σ σ' P P')

include c

/-- **Positive specializations across a change of the coefficient ring.** For a positive
specialization compatible with the change of the coefficient ring along `f`, the coefficient
change of a positive wall representative is a positive wall representative. -/
theorem IsPositiveWallRepresentative.mapRestrictScalars
    (hD : D.IsPositiveWallRepresentative σ P π) :
    (D.mapRestrictScalars f hf).IsPositiveWallRepresentative σ' P' π := by
  rw [← isPositiveWallRepresentative_restrictScalars_iff _ c.restrictedAction'_apply,
    restrictScalars_mapRestrictScalars]
  -- The constants are fixed by the restricted target action, which is the original one.
  refine IsPositiveWallRepresentative.map f hf c.specialization c.completionMap_restrictedAction
    c.toRingHom_single_one
    (fun g a => by rw [c.restrictedAction'_apply, c.action_single_zero]) ?_
  exact (isPositiveWallRepresentative_restrictScalars_iff _ c.restrictedAction_apply).mpr hD

/-- For a positive specialization compatible with the change of the coefficient ring along `f`,
the coefficient change of a positive wall representative `E` of an outgoing completion of `D₀` is
a positive wall representative of an outgoing completion of the image input. -/
theorem IsOutgoingCompletion.isPositiveWallRepresentative_mapRestrictScalars {ι₀ η : Type v}
    {D₀ : ι₀ → DirectedWall (d := d) h H} {E : DirectedDiagram (d := d) h H (ι₀ ⊕ η)}
    (hE : IsOutgoingCompletion D₀ E) (hpos : E.IsPositiveWallRepresentative σ P π) :
    IsOutgoingCompletion (fun j => (D₀ j).mapRestrictScalars f hf) (E.mapRestrictScalars f hf) ∧
      (E.mapRestrictScalars f hf).IsPositiveWallRepresentative σ' P' π :=
  ⟨hE.mapRestrictScalars f hf, hpos.mapRestrictScalars f hf c⟩

variable [Module.Free ℤ Γ]

/-- For a positive specialization compatible with the change of the coefficient ring along `f`,
if the scattering class of a full-hyperplane input has a positive wall representative, so does
the scattering class of the image input. -/
theorem Class.HasPositiveWallRepresentative.scat_mapRestrictScalars
    (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    (hD : (D.Scat hfull).HasPositiveWallRepresentative σ P π) :
    ((D.mapRestrictScalars f hf).Scat (by
      simpa only [mapRestrictScalars_wall, DirectedWall.mapRestrictScalars_support,
        DirectedWall.mapRestrictScalars_normal] using hfull)).HasPositiveWallRepresentative
      σ' P' π := by
  obtain ⟨κ, E, hE, hpos⟩ := (Class.hasPositiveWallRepresentative_iff _ _ _ _).mp hD
  exact (Class.hasPositiveWallRepresentative_iff _ _ _ _).mpr ⟨κ, E.mapRestrictScalars f hf,
    toClass_mapRestrictScalars_eq_scat f hf D hfull hE, hpos.mapRestrictScalars f hf c⟩

end Map

end RestrictScalars

section TropicalVertex

open LogarithmicVectorField
open scoped TropicalVertexCoefficientAction

variable {R S : Type u} {Γ : Type v} {Λ : Type w} {V M : Type*} {ι₀ η : Type t}
  [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [AddCommGroup Γ] [AddCommGroup Λ] [DecidableEq Γ] [AddCommGroup M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {Q : AddSubmonoid Γ} [Fact (d.monoid ≤ Q)]
  (φ : R →ₐ[ℚ] S) {P : Subsemiring R[Q]} {P' : Subsemiring S[Q]}
  (hP : ∀ a ∈ P, mapAlgHom Q φ a ∈ P')
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {π : Γ →+ M}

local instance : LieModule ℚ (tropicalVertexLieAlgebra (R := R) d ρ) R[Q] :=
  LieModule.restrictScalars ℚ R _ _

local instance : LieModule ℚ (tropicalVertexLieAlgebra (R := S) d ρ) S[Q] :=
  LieModule.restrictScalars ℚ S _ _

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := S) d Q
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "ℳ" => tropicalVertexGrading (R := S) d ρ
local notation "ℒℚ" => (fun n => Submodule.restrictScalars ℚ (tropicalVertexGrading (R := R) d ρ n))
local notation "ℳℚ" => (fun n => Submodule.restrictScalars ℚ (tropicalVertexGrading (R := S) d ρ n))

local instance : IsFiltrationRaising d ℒℚ ((F).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := R) (F) d ℒ

local instance : IsFiltrationRaising d ℳℚ ((G).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := S) (G) d ℳ

local notation "φ*" => coefficientMonoidGradedLieHom ρ φ Q 1 d Fact.out
local notation "hφ*" => coefficientMonoidGradedLieHom_mem_wall d ρ φ Q 1 Fact.out

include hP in
/-- The coefficientwise specialization along `φ`, as a positive specialization compatible with
the change of coefficient ring along `z^n ∂_m ↦ z^n ∂_(φ ∘ m)`, for the tropical vertex actions on
`R[[Q]]` and `S[[Q]]`: the restricted actions are the completed BCH actions of the restricted
gradings, and the specialization is `coefficientMonoidPositiveSpecialization` with trivial
twist. -/
def coefficientMonoidPositiveCoefficientChange :
    PositiveCoefficientChange φ* ((F).completedBCHAction d ℒ) ((G).completedBCHAction d ℳ)
      P P' where
  restrictedAction := (F).completedBCHAction (R := ℚ) d ℒℚ
  restrictedAction' := (G).completedBCHAction (R := ℚ) d ℳℚ
  restrictedAction_apply := (F).completedBCHAction_restrictScalars_apply d ℒ
  restrictedAction'_apply := (G).completedBCHAction_restrictScalars_apply d ℳ
  specialization := coefficientMonoidPositiveSpecialization d Q φ 1 (mapAlgHom Q φ)
    (mapAlgHom_single_eq_mul_one Q φ) P P' hP
  completionMap_restrictedAction := coefficientMonoidPositiveSpecialization_completedBCHAction
    d ρ Q φ 1 (mapAlgHom Q φ) (mapAlgHom_single_eq_mul_one Q φ) hP
  toRingHom_single_one p := by
    rw [coefficientMonoidPositiveSpecialization_toRingHom, AlgHom.coe_toRingHom,
      mapAlgHom_single, map_one]
  action_single_zero g c := AlgFiltration.algEquiv_toCompletion_single_zero _ c

/-- The restricted source action is the completed BCH action of the restricted grading. -/
@[simp]
theorem coefficientMonoidPositiveCoefficientChange_restrictedAction :
    (coefficientMonoidPositiveCoefficientChange φ hP).restrictedAction =
      (F).completedBCHAction (R := ℚ) d ℒℚ := (rfl)

/-- The restricted target action is the completed BCH action of the restricted grading. -/
@[simp]
theorem coefficientMonoidPositiveCoefficientChange_restrictedAction' :
    (coefficientMonoidPositiveCoefficientChange φ hP).restrictedAction' =
      (G).completedBCHAction (R := ℚ) d ℳℚ := (rfl)

/-- The specialization is the coefficientwise map along `φ`, with trivial twist. -/
@[simp]
theorem coefficientMonoidPositiveCoefficientChange_specialization :
    (coefficientMonoidPositiveCoefficientChange (ρ := ρ) φ hP).specialization =
      coefficientMonoidPositiveSpecialization d Q φ (1 : Multiplicative Q →* S) (mapAlgHom Q φ)
        (mapAlgHom_single_eq_mul_one Q φ) P P' hP := (rfl)

include hP in
/-- **Tropical vertex coefficient specializations preserve positive wall representatives.**
Let `φ : R → S` be a homomorphism of `ℚ`-algebras whose coefficientwise map `R[Q] → S[Q]` sends
the positive subsemiring `P` into `P'`. Changing the coefficients of a tropical vertex diagram
along `φ` (the specialization `z^n ∂_m ↦ z^n ∂_(φ ∘ m)`, with fixed supports, normals and
supported rays) sends a positive wall representative for the tropical vertex action on `R[[Q]]`
to a positive wall representative for the tropical vertex action on `S[[Q]]`. -/
theorem IsPositiveWallRepresentative.coefficientMonoidGradedLieHom {ι : Type t}
    {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ) ι}
    (hD : D.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ) P π) :
    (D.mapRestrictScalars φ* hφ*).IsPositiveWallRepresentative
      ((G).completedBCHAction d ℳ) P' π :=
  hD.mapRestrictScalars φ* hφ* (coefficientMonoidPositiveCoefficientChange φ hP)

include hP in
/-- Under the hypotheses of `IsPositiveWallRepresentative.coefficientMonoidGradedLieHom`, changing
the coefficients along `φ` sends a positive wall representative `E` of an outgoing completion of
`D₀` to a positive wall representative of an outgoing completion of the image input. -/
theorem IsOutgoingCompletion.isPositiveWallRepresentative_coefficientMonoidGradedLieHom
    {D₀ : ι₀ → DirectedWall (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)}
    {E : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ) (ι₀ ⊕ η)}
    (hE : IsOutgoingCompletion D₀ E)
    (hpos : E.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ) P π) :
    IsOutgoingCompletion (fun j => (D₀ j).mapRestrictScalars φ* hφ*)
        (E.mapRestrictScalars φ* hφ*) ∧
      (E.mapRestrictScalars φ* hφ*).IsPositiveWallRepresentative
        ((G).completedBCHAction d ℳ) P' π :=
  hE.isPositiveWallRepresentative_mapRestrictScalars φ* hφ*
    (coefficientMonoidPositiveCoefficientChange φ hP) hpos

include hP in
/-- Under the hypotheses of `IsPositiveWallRepresentative.coefficientMonoidGradedLieHom`, if the
scattering class of a full-hyperplane tropical vertex input over `R` has a positive wall
representative, so does the scattering class of the input with coefficients changed along
`φ`. -/
theorem Class.HasPositiveWallRepresentative.scat_coefficientMonoidGradedLieHom [Module.Free ℤ Γ]
    {ι : Type t} (D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ) ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    (hD : (D.Scat hfull).HasPositiveWallRepresentative ((F).completedBCHAction d ℒ) P π) :
    ((D.mapRestrictScalars φ* hφ*).Scat (by
      simpa only [mapRestrictScalars_wall, DirectedWall.mapRestrictScalars_support,
        DirectedWall.mapRestrictScalars_normal] using hfull)).HasPositiveWallRepresentative
      ((G).completedBCHAction d ℳ) P' π :=
  scat_mapRestrictScalars φ* hφ* (coefficientMonoidPositiveCoefficientChange φ hP) D hfull hD

end TropicalVertex

end Mei.DirectedDiagram
