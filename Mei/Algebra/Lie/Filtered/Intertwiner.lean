/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Map
public import Mei.CategoryTheory.Grothendieck.Intertwiner.SingleObj

/-!
# Represented intertwiners for filtered BCH module actions

The finite BCH actions on filtered coefficient modules form representations of
the one-object groupoids of the truncation tower. An equivariant filtered linear
map along a graded Lie homomorphism gives an `ActionIntertwiner` between these
representations. The common cutoff can be any monotone modulus sufficient for
both maps; taking the maximum allows independent coefficient and Lie moduli.

The coefficient comparison is the existing quotient map, whose categorical limit
is `ModuleFiltration.completionMap`. This packages the finite equivariance theorem
`mapQ_truncatedBCHAction_of_gradedLieHom` rather than constructing a new action.
The integrated actions and shifted coefficient setting follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, §2.1
(arXiv:1503.06183v5).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Mei.ModuleFiltration

variable {N R : Type*} {L : Type u} {M : Type v}
  [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

/-- The finite BCH action as categorical automorphisms of the coefficient module. -/
def truncatedBCHModuleAut (k : ℕ) :
    BCHGroup (d.truncatedLie ℒ k) →* Aut (ModuleCat.of R (F.quotient k)) where
  toFun g := Aut.of (F.truncatedBCHAction d ℒ k g).toModuleIso
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply ModuleCat.hom_ext
    ext x
    simp
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply ModuleCat.hom_ext
    ext x
    simp

/-- Categorical evaluation is the original finite BCH action. -/
@[simp]
theorem truncatedBCHModuleAut_hom_apply (k : ℕ)
    (g : BCHGroup (d.truncatedLie ℒ k)) (x : F.quotient k) :
    (F.truncatedBCHModuleAut d ℒ k g).asIso.hom x =
      F.truncatedBCHAction d ℒ k g x := (rfl)

/-- Finite BCH module automorphisms commute with quotient transitions. -/
theorem truncatedBCHModuleAut_naturality {k l : ℕᵒᵖ} (f : k ⟶ l)
    (g : (d.groupTower ℒ).obj k) :
    (F.truncatedBCHModuleAut d ℒ k.unop g).asIso.hom ≫ F.quotientTower.map f =
      F.quotientTower.map f ≫
        (F.truncatedBCHModuleAut d ℒ l.unop ((d.groupTower ℒ).map f g)).asIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact F.transition_truncatedBCHAction d ℒ (leOfHom f.unop) g x

/-- The quotient-module actions represented on the total one-object label system. -/
-- Keep coefficient objects reducible in the types of the represented comparisons.
abbrev bchRepresentation :
    Grothendieck (d.groupTower ℒ ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) ⥤ ModuleCat R :=
  (d.groupTower ℒ).singleObjRepresentation F.quotientTower
    (fun k => F.truncatedBCHModuleAut d ℒ k.unop)
    (fun f g => truncatedBCHModuleAut_naturality F d ℒ f g)

variable {N' : Type*} {L' : Type u} {M' : Type v}
  [AddCommMonoid N'] [DecidableEq N']
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ' : N' → Submodule R L'} [GradedLieAlgebra ℒ'] [IsPositiveGrading e ℒ']
  (G : ModuleFiltration R M') [IsFiltrationRaising e ℒ' G]
  (φ : GradedLieHom T ℒ ℒ') (ψ : M →ₗ[R] M')
  (μ : ℕ → ℕ) (hμ : Monotone μ) (hT : ∀ k, T.modulus k ≤ μ k)
  (hψ : ∀ k, F.submodule (μ k + 1) ≤ (G.submodule (k + 1)).comap ψ)
  (hequiv : ∀ (x : L) (a : M), ψ ⁅x, a⁆ = ⁅φ x, ψ a⁆)

/-- Equivariant filtered maps give represented-action intertwiners. The common
cutoff need not be cofinal and neither underlying map needs to be injective. -/
def bchActionIntertwiner :
    ActionIntertwiner (⟨μ, hμ⟩ : ℕ →o ℕ).toFunctor.op
      (F.bchRepresentation d ℒ) (G.bchRepresentation e ℒ') := by
  let τ : (⟨μ, hμ⟩ : ℕ →o ℕ).toFunctor.op ⋙ d.groupTower ℒ ⟶ e.groupTower ℒ' :=
    { app := fun k => GrpCat.ofHom (φ.truncatedMap k.unop (hT k.unop)).bchGroupMap
      naturality := by
        intro k l f
        apply GrpCat.hom_ext
        -- The categorical group maps are the concrete BCH maps of the Lie quotients.
        change (φ.truncatedMap l.unop (hT l.unop)).bchGroupMap.comp
            (d.truncationMap ℒ (hμ (leOfHom f.unop))).bchGroupMap =
          (e.truncationMap ℒ' (leOfHom f.unop)).bchGroupMap.comp
            (φ.truncatedMap k.unop (hT k.unop)).bchGroupMap
        simp only [← LieHom.bchGroupMap_comp]
        exact congrArg (fun f => f.bchGroupMap)
          (φ.truncationMap_comp_truncatedMap_of_le (hμ (leOfHom f.unop))
            (leOfHom f.unop) (hT l.unop) (hT k.unop)).symm }
  exact Functor.singleObjActionIntertwiner (X := F.quotientTower) (X' := G.quotientTower) _ τ
    (fun k => F.truncatedBCHModuleAut d ℒ k.unop)
    (fun k => G.truncatedBCHModuleAut e ℒ' k.unop)
    (fun f g => truncatedBCHModuleAut_naturality F d ℒ f g)
    (fun f g => truncatedBCHModuleAut_naturality G e ℒ' f g)
    (F.quotientTowerMap G ψ μ hμ hψ) (by
      intro k g
      rw [quotientTowerMap_app]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact F.mapQ_truncatedBCHAction_of_gradedLieHom G φ ψ hequiv
        k.unop (hT k.unop) (hψ k.unop) g a)

/-- The coefficient component of the intertwiner is the induced linear quotient map. -/
@[simp]
theorem bchActionIntertwiner_coefficient_app
    (a : Grothendieck ((⟨μ, hμ⟩ : ℕ →o ℕ).toFunctor.op ⋙
      (d.groupTower ℒ ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat))) :
    (F.bchActionIntertwiner d ℒ G φ ψ μ hμ hT hψ hequiv).coefficient.app a =
      ModuleCat.ofHom ((F.submodule (μ a.base.unop + 1)).mapQ
        (G.submodule (a.base.unop + 1)) ψ (hψ a.base.unop)) := by
  unfold bchActionIntertwiner
  -- Identify the concrete quotient modules behind the categorical representation objects.
  erw [Functor.singleObjActionIntertwiner_coefficient_app, quotientTowerMap_app]

/-- The label component is the BCH map at the prescribed source and target cutoffs. -/
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
  rfl

end Mei.ModuleFiltration
