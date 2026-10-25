/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.GroupTheory.CompletedGroup.Basic
public import Mei.LinearAlgebra.ModuleFiltration.Map
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Group actions on filtered module completions

Compatible linear representations of a group tower on the finite quotients of a
filtered module induce a representation of the completed group on the completed
module. Its projections characterize it uniquely. The action preserves each
completed filtration term, and group elements vanishing through an order act
trivially through that order. Faithful finite representations give a faithful
completed representation. Equivariant filtered linear maps remain equivariant
after completion.

The construction uses `ModuleFiltration.lift` to assemble endomorphisms and
Mathlib's `MonoidHom.toHomUnits` and
`LinearMap.GeneralLinearGroup.generalLinearEquiv` to recover invertibility. It is
the linear counterpart of `AlgFiltration.completedAction`. No surjectivity of the
group transitions or separatedness of the original module is required.
-/

public section

open CategoryTheory Opposite

universe u

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M) {G : ℕᵒᵖ ⥤ GrpCat.{u}}
  (ρ : ∀ k : ℕ, G.obj (op k) →* (F.quotient k ≃ₗ[R] F.quotient k))
  (hρ : ∀ {k l : ℕ} (h : k ≤ l) (g : G.obj (op l)) (x : F.quotient l),
    F.transition h (ρ l g x) = ρ k (G.map (homOfLE h).op g) (F.transition h x))

private def actionEnd : completedGroup G →* Module.End R F.completion where
  toFun g := F.lift
    (fun k => (ρ k (CompletedGroup.projection k g)).toLinearMap.comp (F.projection k))
    (by
      intro k l h
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hρ h, CompletedGroup.map_projection, F.transition_projection h])
  map_one' := by
    apply LinearMap.ext
    intro x
    apply F.completion_ext
    intro k
    simp
  map_mul' g g' := by
    apply LinearMap.ext
    intro x
    apply F.completion_ext
    intro k
    simp

/-- Extend compatible finite-order linear representations to the completed module. -/
def completedAction : completedGroup G →* (F.completion ≃ₗ[R] F.completion) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R F.completion).toMonoidHom.comp
    (F.actionEnd ρ hρ).toHomUnits

/-- The completed action is computed by the corresponding finite-order action. -/
@[simp]
theorem projection_completedAction (g : completedGroup G) (x : F.completion) (k : ℕ) :
    F.projection k (F.completedAction ρ hρ g x) =
      ρ k (CompletedGroup.projection k g) (F.projection k x) := by
  simp [completedAction, actionEnd]

/-- The finite-order projection formula uniquely determines the representation. -/
theorem completedAction_unique (σ : completedGroup G →* (F.completion ≃ₗ[R] F.completion))
    (hσ : ∀ (g : completedGroup G) (x : F.completion) (k : ℕ),
      F.projection k (σ g x) = ρ k (CompletedGroup.projection k g) (F.projection k x)) :
    σ = F.completedAction ρ hρ := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro x
  apply F.completion_ext
  intro k
  rw [F.projection_completedAction, hσ]

/-- Every completed automorphism preserves and reflects the induced module filtration. -/
@[simp]
theorem completedAction_mem_completedFiltration_iff (g : completedGroup G)
    (x : F.completion) (k : ℕ) :
    F.completedAction ρ hρ g x ∈ F.completedFiltration.submodule k ↔
      x ∈ F.completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [completedFiltration_succ, LinearMap.mem_ker, F.projection_completedAction,
      LinearEquiv.map_eq_zero_iff]

/-- Group elements vanishing through order `k` act trivially on that quotient. -/
theorem projection_completedAction_of_mem_degreeFiltration {g : completedGroup G}
    {k : ℕ} (hg : g ∈ CompletedGroup.degreeFiltration G (k + 1)) (x : F.completion) :
    F.projection k (F.completedAction ρ hρ g x) = F.projection k x := by
  have hg' : CompletedGroup.projection k g = 1 := by
    simpa only [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker] using hg
  simp [hg']

/-- An element of group order `k + 1` moves vectors only in module order `k + 1`. -/
theorem completedAction_sub_mem_completedFiltration {g : completedGroup G} {k : ℕ}
    (hg : g ∈ CompletedGroup.degreeFiltration G (k + 1)) (x : F.completion) :
    F.completedAction ρ hρ g x - x ∈ F.completedFiltration.submodule (k + 1) := by
  simp only [completedFiltration_succ, LinearMap.mem_ker, map_sub,
    F.projection_completedAction_of_mem_degreeFiltration ρ hρ hg, sub_self]

/-- Faithful representations at every finite order give a faithful completed representation.
Only vectors coming from the original module are needed to test faithfulness. -/
theorem completedAction_injective (hfaithful : ∀ k, Function.Injective (ρ k)) :
    Function.Injective (F.completedAction ρ hρ) := by
  intro g g' he
  apply CompletedGroup.ext
  intro k
  apply hfaithful k
  apply LinearEquiv.ext
  intro x
  obtain ⟨a, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective x
  have hx := congrArg (fun e : F.completion ≃ₗ[R] F.completion =>
    F.projection k (e (F.of a))) he
  simpa only [F.projection_completedAction, F.projection_of, Submodule.mkQ_apply] using hx

section EquivariantMap

variable {N : Type*} [AddCommGroup N] [Module R N]
  (H : ModuleFiltration R N)
  (σ : ∀ k : ℕ, G.obj (op k) →* (H.quotient k ≃ₗ[R] H.quotient k))
  (hσ : ∀ {k l : ℕ} (h : k ≤ l) (g : G.obj (op l)) (x : H.quotient l),
    H.transition h (σ l g x) = σ k (G.map (homOfLE h).op g) (H.transition h x))
  (f : M →ₗ[R] N) (hf : ∀ k, F.submodule (k + 1) ≤ (H.submodule (k + 1)).comap f)

/-- A filtration-preserving map intertwining the finite-order actions also intertwines
the completed actions. The source module need not be separated. -/
theorem completionMap_completedAction
    (hequiv : ∀ (k : ℕ) (g : G.obj (op k)) (x : F.quotient k),
      (F.submodule (k + 1)).mapQ (H.submodule (k + 1)) f (hf k) (ρ k g x) =
        σ k g ((F.submodule (k + 1)).mapQ (H.submodule (k + 1)) f (hf k) x))
    (g : completedGroup G) (x : F.completion) :
    F.completionMap H f id monotone_id hf (F.completedAction ρ hρ g x) =
      H.completedAction σ hσ g (F.completionMap H f id monotone_id hf x) := by
  apply H.completion_ext
  intro k
  simp only [projection_completionMap, projection_completedAction, id_eq]
  exact hequiv k (CompletedGroup.projection k g) (F.projection k x)

end EquivariantMap

end Mei.ModuleFiltration
