/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat

/-!
# Positive specializations of positive wall representatives

A fixed-degree graded Lie homomorphism `f : ℒ → ℳ` preserving wall spaces maps a directed
diagram `D` to `D.map f hf`, retaining every support, ray and normal. A function-wall
grouping of `D` is therefore also a grouping of the image (`FunctionWallGrouping.map`):
an image label that is nontrivial comes from a nontrivial label, so the projected
direction condition persists. The completed label of a group is mapped to the completed
label of the image group (`FunctionWallGrouping.label_map`), since the image of a finite
product of commuting projected labels is the product of their images.

Let `Φ : A[Q]^ → A'[Q]^` be a map of completed coefficient algebras that intertwines the
coefficient actions `σ` and `σ'` along `f`, fixes the monomials `z^p`, and such that the
target action fixes the constants of `A'`. Then a wall function `u` of a group is sent to the
wall function `Φ(u)` of the image group (`FunctionWallGrouping.IsWallFunction.map`): a
fixed-degree map preserves the normals, so the exponent `ν(ρ p)` is unchanged. This is the case
of the identity on exponents of `FunctionWallGrouping.IsWallFunction.of_intertwining`; the
degree-changing case is in
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Pushforward`. For a positive
specialization `φ` of the coefficient algebras with these compatibilities, positivity of wall
functions is preserved by `PositiveSpecialization.map_isPositive`, so positive groupings and
positive wall representatives are carried to the image diagram
(`DirectedDiagram.IsPositiveWallRepresentative.map`).

Coefficient maps preserve outgoing completions (`DirectedDiagram.IsOutgoingCompletion.map`)
and commute with the scattering class (`DirectedDiagram.map_scat`). Hence the image of a
positive wall representative of an outgoing completion is a positive wall representative of
an outgoing completion of the image input
(`DirectedDiagram.IsOutgoingCompletion.isPositiveWallRepresentative_map`), and a scattering
class with a positive wall representative maps to the scattering class of the image input,
which again has one (`DirectedDiagram.Class.HasPositiveWallRepresentative.scat_map`).

The coefficient ring may change: the Lie algebras are taken over a common scalar ring `R`
(for instance `ℚ`), while the coefficient algebras `A` and `A'` are arbitrary `R`-algebras.
The hypothesis `hconst` that the target action fixes the constants of `A'` is automatic only
when `A' = R`, by `AlgFiltration.algEquiv_toCompletion_single_zero`. Applying these results to
a coefficientwise specialization such as `a ↦ 1`
(`LogarithmicVectorField.coefficientMonoidPositiveSpecialization` with trivial twist) also
requires proving `hconst` for the target action, which is not done here.

This is the fixed-degree case of the positive specialization statements of
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, §8.1 and §9.2
(arXiv:2503.03719v1), for the grouped wall functions of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

open AddMonoidAlgebra

universe u v

variable {Γ Λ R V M : Type*} {L L' : Type v} {ι : Type u}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup M]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  {D : DirectedDiagram (d := d) h H ι}
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m)
  {π : Γ →+ M} {κ : Type*}

namespace FunctionWallGrouping

variable (G : D.FunctionWallGrouping π κ)

/-- A function-wall grouping of a diagram is a grouping of its image under a fixed-degree
coefficient map: supports and normals are unchanged, and an image label is nontrivial only
if the original label is. -/
def map : (D.map f hf).FunctionWallGrouping π κ where
  group := G.group
  support_eq hj := by
    simpa only [map_wall, DirectedWall.map_support] using G.support_eq hj
  normal_eq hj := by
    simpa only [map_wall, DirectedWall.map_normal] using G.normal_eq hj
  projectedDirection_eq {j j'} hj hj1 hj'1 := by
    simp only [map_wall, DirectedWall.map_label, DirectedWall.map_ray] at hj1 hj'1 ⊢
    exact G.projectedDirection_eq hj (fun h1 => hj1 (by rw [h1, map_one]))
      (fun h1 => hj'1 (by rw [h1, map_one]))
  isPrimitive_normal j := by
    simpa only [map_wall, DirectedWall.map_normal] using G.isPrimitive_normal j

/-- The image grouping places every wall in its original group. -/
@[simp]
theorem map_group (j : ι) : (G.map f hf).group j = G.group j := (rfl)

/-- The order-`k` label of an image group is the image of the order-`k` group label. -/
theorem groupLabel_map (g : κ) (k : ℕ) :
    (G.map f hf).groupLabel g k =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap (G.groupLabel g k) := by
  classical
  let s := (Set.toFinite (D.active k)).toFinset.filter fun j => G.group j = g
  have hs : ∀ j ∈ s, G.group j = g := fun j hj => (Finset.mem_filter.mp hj).2
  have hact : ∀ j ∈ D.active k, G.group j = g → j ∈ s := fun j hj hg =>
    Finset.mem_filter.mpr ⟨(Set.toFinite _).mem_toFinset.mpr hj, hg⟩
  have hsub : (D.map f hf).active k ⊆ D.active k := by
    rw [← D.pushforward_ofFixedDegree f hf]
    exact D.active_pushforward_subset _ k (by simp)
  rw [(G.map f hf).groupLabel_eq_noncommProd g k s (fun j hj => by simpa using hs j hj)
      fun j hj hg => hact j (hsub hj) (by simpa using hg),
    G.groupLabel_eq_noncommProd g k s hs hact]
  refine (Finset.noncommProd_congr rfl (fun j _ => ?_) _).trans
    (Finset.map_noncommProd s _ _ _).symm
  rw [map_wall, DirectedWall.map_label, f.projection_completedMap_of_le k (a := k) (by simp)]

/-- The completed label of an image group is the image of the completed group label. -/
@[simp]
theorem label_map (g : κ) : (G.map f hf).label g = f.completedMap (G.label g) :=
  (((G.map f hf).eq_label_iff g _).mpr fun k => by
    rw [f.projection_completedMap_of_le k (a := k) (by simp), projection_label,
      groupLabel_map]).symm

section WallFunction

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  {F' : AlgFiltration (AddMonoidAlgebra A' Q)}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}
  {σ' : d.completedBCHGroup ℳ →* (F'.completion ≃ₐ[R] F'.completion)}

variable {G f hf} in
/-- A coefficient map intertwining the actions along `f`, fixing the monomials and such that
the target action fixes constants, sends a wall function of a group to a wall function of the
image group. -/
theorem IsWallFunction.map (Φ : F.completion →+* F'.completion)
    (hΦ : ∀ g x, Φ (σ g x) = σ' (f.completedMap g) (Φ x))
    (hmono : ∀ p : Q, Φ (F.toCompletion (single p 1)) = F'.toCompletion (single p 1))
    (hconst : ∀ g (c : A'),
      σ' g (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c))
    {g : κ} {u : F.completionˣ} (hu : G.IsWallFunction σ g u) :
    (G.map f hf).IsWallFunction σ' g (Units.map Φ.toMonoidHom u) :=
  hu.of_intertwining (G.map f hf) g Φ id Function.surjective_id hmono
    (fun x => by rw [label_map]; exact hΦ _ x) (hconst _)
    fun j hj => ⟨j, by simpa using hj, fun p => by rw [map_wall, DirectedWall.map_normal, id_eq]⟩

variable {P : Subsemiring (AddMonoidAlgebra A Q)} {P' : Subsemiring (AddMonoidAlgebra A' Q)}

variable {G f hf} in
/-- A positive specialization of coefficient algebras that intertwines the actions along `f`,
fixes the monomials, and whose target action fixes constants, carries a positive grouping to
a positive grouping of the image diagram. -/
theorem IsPositive.map (φ : PositiveSpecialization F F' P P')
    (hφσ : ∀ g x, φ.completionMap (σ g x) = σ' (f.completedMap g) (φ.completionMap x))
    (hφ : ∀ p : Q, φ.toRingHom (single p 1) = single p 1)
    (hconst : ∀ g (c : A'),
      σ' g (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c))
    (hG : G.IsPositive σ P) : (G.map f hf).IsPositive σ' P' :=
  hG.of_isWallFunction_completionMap (G.map f hf) φ fun _ _ hu => hu.map φ.completionMap hφσ
    (fun p => by rw [φ.completionMap_toCompletion, hφ]) hconst

end WallFunction

end FunctionWallGrouping

section WallFunction

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  {F' : AlgFiltration (AddMonoidAlgebra A' Q)}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}
  {σ' : d.completedBCHGroup ℳ →* (F'.completion ≃ₐ[R] F'.completion)}
  {P : Subsemiring (AddMonoidAlgebra A Q)} {P' : Subsemiring (AddMonoidAlgebra A' Q)}
  (φ : PositiveSpecialization F F' P P')
  (hφσ : ∀ g x, φ.completionMap (σ g x) = σ' (f.completedMap g) (φ.completionMap x))
  (hφ : ∀ p : Q, φ.toRingHom (single p 1) = single p 1)
  (hconst : ∀ g (c : A'),
    σ' g (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c))

include hφσ hφ hconst

/-- A positive specialization of coefficient algebras compatible with a fixed-degree
coefficient map `f` carries positive wall representatives to positive wall representatives
of the image diagram. -/
theorem IsPositiveWallRepresentative.map (hD : D.IsPositiveWallRepresentative σ P π) :
    (D.map f hf).IsPositiveWallRepresentative σ' P' π := by
  obtain ⟨κ, G, hG⟩ := (D.isPositiveWallRepresentative_iff σ P π).mp hD
  exact (hG.map φ hφσ hφ hconst).isPositiveWallRepresentative

omit D in
/-- The image of a positive wall representative of an outgoing completion is a positive wall
representative of an outgoing completion of the image input. -/
theorem IsOutgoingCompletion.isPositiveWallRepresentative_map {ι₀ η : Type u}
    {D₀ : ι₀ → DirectedWall (d := d) h H} {E : DirectedDiagram (d := d) h H (ι₀ ⊕ η)}
    (hE : IsOutgoingCompletion D₀ E) (hpos : E.IsPositiveWallRepresentative σ P π) :
    IsOutgoingCompletion (fun j => (D₀ j).map f hf) (E.map f hf) ∧
      (E.map f hf).IsPositiveWallRepresentative σ' P' π :=
  ⟨hE.map f hf, hpos.map f hf φ hφσ hφ hconst⟩

end WallFunction

section Class

variable {A : Type*} [CommRing A] [Algebra R A] {Q : AddSubmonoid Γ}
  {F : AlgFiltration (AddMonoidAlgebra A Q)}
  (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion))
  (P : Subsemiring (AddMonoidAlgebra A Q)) (π : Γ →+ M)

/-- A completed class of directed diagrams has a positive wall representative when one of its
presentations is a positive wall representative for the action `σ`, the positive subsemiring
`P` and the spatial projection `π`. -/
def Class.HasPositiveWallRepresentative (c : Class.{u} (d := d) (h := h) (H := H)) : Prop :=
  ∃ (ι : Type u) (E : DirectedDiagram (d := d) h H ι),
    E.toClass = c ∧ E.IsPositiveWallRepresentative σ P π

/-- The defining condition of a class with a positive wall representative. -/
theorem Class.hasPositiveWallRepresentative_iff (c : Class.{u} (d := d) (h := h) (H := H)) :
    c.HasPositiveWallRepresentative σ P π ↔
      ∃ (ι : Type u) (E : DirectedDiagram (d := d) h H ι),
        E.toClass = c ∧ E.IsPositiveWallRepresentative σ P π :=
  Iff.rfl

variable {σ P π}

/-- The class of a positive wall representative has a positive wall representative. -/
theorem IsPositiveWallRepresentative.hasPositiveWallRepresentative_toClass
    (hD : D.IsPositiveWallRepresentative σ P π) :
    D.toClass.HasPositiveWallRepresentative σ P π :=
  ⟨ι, D, rfl, hD⟩

variable {A' : Type*} [CommRing A'] [Algebra R A']
  {F' : AlgFiltration (AddMonoidAlgebra A' Q)}
  {σ' : d.completedBCHGroup ℳ →* (F'.completion ≃ₐ[R] F'.completion)}
  {P' : Subsemiring (AddMonoidAlgebra A' Q)}
  (φ : PositiveSpecialization F F' P P')
  (hφσ : ∀ g x, φ.completionMap (σ g x) = σ' (f.completedMap g) (φ.completionMap x))
  (hφ : ∀ p : Q, φ.toRingHom (single p 1) = single p 1)
  (hconst : ∀ g (c : A'),
    σ' g (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c))

include hφσ hφ hconst

/-- Changing coefficients along a compatible positive specialization preserves the existence
of a positive wall representative of a completed class. -/
theorem Class.HasPositiveWallRepresentative.map {c : Class.{u} (d := d) (h := h) (H := H)}
    (hc : c.HasPositiveWallRepresentative σ P π) :
    (Class.map f hf c).HasPositiveWallRepresentative σ' P' π := by
  obtain ⟨ι, E, rfl, hE⟩ := hc
  exact ⟨ι, E.map f hf, (Class.map_toClass f hf E).symm, hE.map f hf φ hφσ hφ hconst⟩

omit D in
/-- If the scattering class of a full-hyperplane input has a positive wall representative, so
does the scattering class of the image input under a compatible positive specialization. -/
theorem Class.HasPositiveWallRepresentative.scat_map [Module.Free ℤ Γ]
    (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    (hD : (D.Scat hfull).HasPositiveWallRepresentative σ P π) :
    ((D.map f hf).Scat (by
      simpa only [map_wall, DirectedWall.map_support, DirectedWall.map_normal] using hfull)
      ).HasPositiveWallRepresentative σ' P' π := by
  rw [← map_scat]
  exact hD.map f hf φ hφσ hφ hconst

end Class

end Mei.DirectedDiagram
