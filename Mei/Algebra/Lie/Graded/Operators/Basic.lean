/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Operators.Basic
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Submodule

/-!
# Lie actions on homogeneous operator families

A graded Lie action induces an action by postcomposition on linear families with
uniform finite homogeneous support. A Lie element has finitely many homogeneous
components, each of which shifts an operator's degree. Evaluation is an equivariant,
degree-preserving linear map. No finite generation of the input module is needed.

We use Mathlib's Hom representation with trivial action on the source and restrict
it to the existing `GradedOperators`. This supplies coefficient representations for
operator-valued semidirect probes; see Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.GradedOperators

variable {R H M Γ L : Type*} [CommRing R] [AddCommGroup H] [Module R H]
  [AddCommGroup M] [Module R M] [AddCommMonoid Γ] [DecidableEq Γ]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [DirectSum.Decomposition ℒ] [SetLike.GradedBracket ℒ ℳ]

omit [DirectSum.Decomposition ℒ] in
/-- Postcomposition by a homogeneous Lie element preserves finite homogeneous support. -/
private theorem postcomp_mem_of_homogeneous {n q : Γ} {x : L} (hx : x ∈ ℒ n)
    {f : GradedOperators ℳ H} (hf : f ∈ grading ℳ q) :
    (LieModule.toEnd R L M x).comp f.val ∈
      LinearMap.range (gradedOperatorMap (H := H) ℳ) := by
  let g : H →ₗ[R] ℳ (n + q) :=
    ((LieModule.toEnd R L M x).comp f.val).codRestrict (ℳ (n + q))
      (fun a => SetLike.GradedBracket.bracket_mem hx ((mem_grading_iff ℳ q f).mp hf a))
  refine ⟨DirectSum.lof R Γ (fun q => H →ₗ[R] ℳ q) (n + q) g, ?_⟩
  rw [gradedOperatorMap_lof]
  rfl

include ℒ in
/-- Postcomposition preserves uniform finite homogeneous support. -/
private theorem postcomp_mem (x : L) (f : GradedOperators ℳ H) :
    (LieModule.toEnd R L M x).comp f.val ∈
      LinearMap.range (gradedOperatorMap (H := H) ℳ) := by
  induction x using DirectSum.Decomposition.inductionOn ℒ with
  | zero => simp
  | @homogeneous n x =>
    induction f using DirectSum.Decomposition.inductionOn (grading ℳ) with
    | zero => simp
    | homogeneous f => exact postcomp_mem_of_homogeneous ℳ ℒ x.property f.property
    | add f g hf hg => simpa only [Submodule.coe_add, LinearMap.comp_add] using add_mem hf hg
  | add x y hx hy =>
    simpa only [map_add, LinearMap.add_comp] using add_mem hx hy

/-- The representation of uniformly finitely supported operator families. Its
carrier is `GradedOperators` on Mathlib's trivial source representation; the
abbreviation retains this carrier so its existing linear decomposition applies. -/
abbrev lieSubmodule : LieSubmodule R L (TrivialLieModule R L H →ₗ[R] M) where
  toSubmodule := LinearMap.range (gradedOperatorMap (H := TrivialLieModule R L H) ℳ)
  lie_mem {x f} hf := by
    have he : ⁅x, f⁆ = (LieModule.toEnd R L M x).comp f := by
      ext a
      simp only [LieHom.lie_apply, trivial_lie_zero, map_zero, sub_zero,
        LinearMap.comp_apply, LieModule.toEnd_apply_apply]
    rw [he]
    exact postcomp_mem ℳ ℒ x ⟨f, hf⟩

/-- The homogeneous operators in the restricted Lie representation. -/
abbrev lieGrading (q : Γ) : Submodule R (lieSubmodule (H := H) ℳ ℒ) :=
  grading (H := TrivialLieModule R L H) ℳ q

/-- The operator representation has the inherited internal direct-sum decomposition. -/
instance instDecompositionLieGrading : DirectSum.Decomposition (lieGrading (H := H) ℳ ℒ) :=
  inferInstanceAs (DirectSum.Decomposition (grading (H := TrivialLieModule R L H) ℳ))

/-- Evaluation is the ordinary action on the output and the trivial action on the input. -/
@[simp↓]
theorem eval_lie (x : L) (f : lieSubmodule (H := H) ℳ ℒ) (a : TrivialLieModule R L H) :
    eval ℳ a (⁅x, f⁆ : lieSubmodule (H := H) ℳ ℒ) = ⁅x, eval ℳ a f⁆ := by
  simp only [eval_apply, LieSubmodule.coe_bracket, LieHom.lie_apply, trivial_lie_zero,
    map_zero, sub_zero]

/-- The operator degree shifts by the degree of the acting Lie element. -/
instance : SetLike.GradedBracket ℒ (lieGrading (H := H) ℳ ℒ) where
  bracket_mem _ _ _ _ hx hf := by
    rw [mem_grading_iff]
    intro a
    simpa only [LieSubmodule.coe_bracket, LieHom.lie_apply, trivial_lie_zero,
      map_zero, sub_zero] using
      SetLike.GradedBracket.bracket_mem hx ((mem_grading_iff ℳ _ _).mp hf a)

/-- Evaluation at any input is a homomorphism of Lie representations. -/
def evalLieModuleHom (a : H) : lieSubmodule (H := H) ℳ ℒ →ₗ⁅R,L⁆ M where
  toLinearMap := eval ℳ ((TrivialLieModule.equiv R L H).symm a)
  map_lie' := fun {x f} => eval_lie ℳ ℒ x f _

@[simp]
theorem evalLieModuleHom_apply (a : H) (f : lieSubmodule (H := H) ℳ ℒ) :
    evalLieModuleHom ℳ ℒ a f = f.val ((TrivialLieModule.equiv R L H).symm a) :=
  eval_apply ℳ _ f

/-- Evaluation retains the operator's homogeneous degree, even when its value vanishes. -/
theorem evalLieModuleHom_mem (a : H) {q : Γ} {f : lieSubmodule (H := H) ℳ ℒ}
    (hf : f ∈ lieGrading ℳ ℒ q) : evalLieModuleHom ℳ ℒ a f ∈ ℳ q := by
  rw [evalLieModuleHom_apply]
  exact (mem_grading_iff ℳ q f).mp hf _

/-- Regard a linear family in a single piece as a homogeneous operator coefficient. -/
def homogeneousFamily (q : Γ) (f : H →ₗ[R] ℳ q) : lieGrading (H := H) ℳ ℒ q :=
  ⟨single ℳ q (f.comp (TrivialLieModule.equiv R L H).toLinearMap), single_mem ℳ q _⟩

/-- Evaluating a homogeneous incoming family recovers its prescribed input value. -/
@[simp↓]
theorem evalLieModuleHom_homogeneousFamily (q : Γ) (f : H →ₗ[R] ℳ q) (a : H) :
    evalLieModuleHom ℳ ℒ a (homogeneousFamily ℳ ℒ q f) = (f a : M) := by
  simp only [evalLieModuleHom_apply, homogeneousFamily, coe_single, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

end Mei.GradedOperators
