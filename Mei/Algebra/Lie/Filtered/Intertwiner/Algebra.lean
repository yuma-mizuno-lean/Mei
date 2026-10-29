/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Map
public import Mei.CategoryTheory.Grothendieck.Intertwiner.SingleObj

/-!
# Represented intertwiners for filtered BCH algebra actions

The quotient algebra actions of a filtration-raising Lie action give a
representation of the one-object label system in `AlgCat`. An equivariant filtered
algebra map along a graded Lie homomorphism gives an `ActionIntertwiner` of these
representations. Its coefficient maps are algebra maps, so comparisons of section
limits retain multiplication as well as the linear action.

This is the algebra-valued companion to the module construction in
`Mei.Algebra.Lie.Filtered.Intertwiner.Basic`. It uses
`Functor.singleObjActionIntertwiner` and the existing
`AlgFiltration.truncatedBCHAction`, with finite equivariance supplied by
`quotientMapₐ_truncatedExpLieAction_of_gradedLieHom`. The concrete completion map
is identified with the comparison of quotient algebra limits in
`mapCompletionₐ_completionAlgebraIsoLimit`. No cofinality of the common cutoff
modulus is required.

The integrated coefficient actions follow Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §2.1 (arXiv:1503.06183v5).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Mei.AlgFiltration

variable {N R : Type*} {L : Type u} {A : Type v}
  [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [Ring A] [Algebra R A] [Algebra ℚ A] [LieRingModule L A] [LieModule R L A]
  (F : AlgFiltration A) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)] [IsDerivationAction L A]

/-- The finite BCH action as categorical automorphisms of the coefficient algebra. -/
def truncatedBCHAlgebraAut (k : ℕ) :
    BCHGroup (d.truncatedLie ℒ k) →* Aut (AlgCat.of R (A ⧸ F.ideal (k + 1))) where
  toFun g := Aut.of (F.truncatedBCHAction d ℒ k g).toAlgebraIso
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply AlgCat.hom_ext
    ext x
    simp
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply AlgCat.hom_ext
    ext x
    simp

/-- Categorical evaluation is the original finite BCH algebra action. -/
@[simp]
theorem truncatedBCHAlgebraAut_hom_apply (k : ℕ)
    (g : BCHGroup (d.truncatedLie ℒ k)) (x : A ⧸ F.ideal (k + 1)) :
    (F.truncatedBCHAlgebraAut d ℒ k g).asIso.hom x =
      F.truncatedBCHAction d ℒ k g x := (rfl)

/-- Finite BCH algebra automorphisms commute with the quotient algebra transitions. -/
theorem truncatedBCHAlgebraAut_naturality {k l : ℕᵒᵖ} (f : k ⟶ l)
    (g : (d.groupTower ℒ).obj k) :
    (F.truncatedBCHAlgebraAut d ℒ k.unop g).asIso.hom ≫
        F.quotientAlgebraDiagram.map f =
      F.quotientAlgebraDiagram.map f ≫
        (F.truncatedBCHAlgebraAut d ℒ l.unop ((d.groupTower ℒ).map f g)).asIso.hom := by
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact F.factor_truncatedBCHAction d ℒ (leOfHom f.unop) g x

/-- The quotient-algebra actions represented on the total one-object label system. -/
-- Coefficient objects must compute in the types of represented comparisons.
abbrev bchRepresentation :
    Grothendieck (d.groupTower ℒ ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) ⥤ AlgCat R :=
  (d.groupTower ℒ).singleObjRepresentation F.quotientAlgebraDiagram
    (fun k => F.truncatedBCHAlgebraAut d ℒ k.unop)
    (fun f g => truncatedBCHAlgebraAut_naturality F d ℒ f g)

variable {N' : Type*} {L' : Type u} {B : Type v}
  [AddCommMonoid N'] [DecidableEq N']
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [Ring B] [Algebra R B] [Algebra ℚ B] [LieRingModule L' B] [LieModule R L' B]
  {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ' : N' → Submodule R L'} [GradedLieAlgebra ℒ'] [IsPositiveGrading e ℒ']
  (G : AlgFiltration B)
  [IsFiltrationRaising e ℒ' (G.toModuleFiltration R)] [IsDerivationAction L' B]
  (φ : GradedLieHom T ℒ ℒ') (ψ : A →ₐ[R] B)
  (μ : ℕ → ℕ) (hμ : Monotone μ) (hT : ∀ k, T.modulus k ≤ μ k)
  (hψ : ∀ k, F.ideal (μ k + 1) ≤ (G.ideal (k + 1)).comap ψ)
  (hequiv : ∀ (x : L) (a : A), ψ ⁅x, a⁆ = ⁅φ x, ψ a⁆)

/-- Equivariant filtered algebra maps give represented-action intertwiners with
algebra-valued coefficients, at any common sufficient cutoff. -/
def bchActionIntertwiner :
    ActionIntertwiner (⟨μ, hμ⟩ : ℕ →o ℕ).toFunctor.op
      (F.bchRepresentation d ℒ) (G.bchRepresentation e ℒ') := by
  let τ := φ.groupTowerMap ⟨μ, hμ⟩ hT
  exact Functor.singleObjActionIntertwiner
    (X := F.quotientAlgebraDiagram) (X' := G.quotientAlgebraDiagram) _ τ
    (fun k => F.truncatedBCHAlgebraAut d ℒ k.unop)
    (fun k => G.truncatedBCHAlgebraAut e ℒ' k.unop)
    (fun f g => truncatedBCHAlgebraAut_naturality F d ℒ f g)
    (fun f g => truncatedBCHAlgebraAut_naturality G e ℒ' f g)
    (F.quotientAlgebraDiagramMap G ψ μ hμ hψ) (by
      intro k g
      have hτ : τ.app k =
          GrpCat.ofHom (φ.truncatedMap k.unop (hT k.unop)).bchGroupMap := by
        apply GrpCat.hom_ext
        exact φ.groupTowerMap_app_hom ⟨μ, hμ⟩ hT k
      rw [hτ, quotientAlgebraDiagramMap_app]
      apply AlgCat.hom_ext
      apply AlgHom.ext
      intro a
      -- Restore concrete quotient types after categorical reindexing, so the
      -- action computation lemmas can rewrite under their original scalar action.
      change Ideal.quotientMapₐ (G.ideal (k.unop + 1)) ψ (hψ k.unop)
          (F.truncatedBCHAction d ℒ (μ k.unop) g a) =
        G.truncatedBCHAction e ℒ' k.unop ((φ.truncatedMap k.unop (hT k.unop)).bchGroupMap g)
          (Ideal.quotientMapₐ (G.ideal (k.unop + 1)) ψ (hψ k.unop) a)
      erw [truncatedBCHAction_apply, truncatedBCHAction_apply, LieHom.log_bchGroupMap]
      exact F.quotientMapₐ_truncatedExpLieAction_of_gradedLieHom G φ ψ hequiv
        k.unop (hT k.unop) (hψ k.unop) (BCHGroup.log g) a)

/-- The coefficient component is the induced quotient algebra map. -/
@[simp]
theorem bchActionIntertwiner_coefficient_app
    (a : Grothendieck ((⟨μ, hμ⟩ : ℕ →o ℕ).toFunctor.op ⋙
      (d.groupTower ℒ ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat))) :
    (F.bchActionIntertwiner d ℒ G φ ψ μ hμ hT hψ hequiv).coefficient.app a =
      AlgCat.ofHom (Ideal.quotientMapₐ (G.ideal (a.base.unop + 1)) ψ (hψ a.base.unop)) := by
  unfold bchActionIntertwiner
  -- Identify the concrete quotient algebras behind the represented objects.
  erw [Functor.singleObjActionIntertwiner_coefficient_app, quotientAlgebraDiagramMap_app]

/-- The label component is the BCH map at the prescribed cutoffs. -/
@[simp]
theorem bchActionIntertwiner_labelMap_map (k : ℕᵒᵖ)
    (g : BCHGroup (d.truncatedLie ℒ (μ k.unop))) :
    (((F.bchActionIntertwiner d ℒ G φ ψ μ hμ hT hψ hequiv).labelMap.app k).toFunctor.map
      (X := SingleObj.star (BCHGroup (d.truncatedLie ℒ (μ k.unop))))
      (Y := SingleObj.star (BCHGroup (d.truncatedLie ℒ (μ k.unop)))) g) =
        (φ.truncatedMap k.unop (hT k.unop)).bchGroupMap g := by
  unfold bchActionIntertwiner
  -- The group tower objects are the corresponding concrete BCH quotient groups.
  erw [Functor.singleObjActionIntertwiner_labelMap]
  exact congrArg (fun f => f g) (φ.groupTowerMap_app_hom ⟨μ, hμ⟩ hT k)

/-- Along the identity-transport section the comparison is the original map of
quotient algebras. Its limit is therefore the filtered algebra completion map. -/
theorem bchActionIntertwiner_sectionComparison_app (k : ℕᵒᵖ) :
    ((F.bchActionIntertwiner d ℒ G φ ψ μ hμ hT hψ hequiv).sectionComparison
      (d.groupTower ℒ).singleObjSection.toSection).app k =
      AlgCat.ofHom (Ideal.quotientMapₐ (G.ideal (k.unop + 1)) ψ (hψ k.unop)) := by
  unfold bchActionIntertwiner
  -- Identify the quotient objects under the identity-transport section wrappers.
  erw [Functor.singleObjActionIntertwiner_sectionComparison_app, quotientAlgebraDiagramMap_app]

end Mei.AlgFiltration
