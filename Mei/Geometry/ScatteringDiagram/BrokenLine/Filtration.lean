/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Filtration
public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay

/-!
# Component filtration bounds for actual decorated rays

Attach the chamber-degree lift to the complete history of an actual decorated
admissible ray. Its encounters, including unchanged-degree encounters, retain their
positions in the path. A filtration-raising mark may depend on the input and output
degrees of the component, rather than on the entire wall operator. In particular a
degree change may be marked even when its spatial velocity is unchanged.

A nonzero ray in a filtration vanishing at order `r`, with at most `h` unmarked
encounters between marked ones, has at most `r * h + r - 1` encounters. The bound
applies to the actual fiber and its full incoming datum; no local restriction of an
incoming tail or deletion of identity encounters is used.
The bound on unmarked runs is the hypothesis `hp`.
-/

public noncomputable section

open Quiver

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V} {W : J → Set V} {S : K → Set V} {C : Set V}
  {Q : V}

namespace DecoratedAdmissibleRay

/-- The complete homogeneous history as a path of encounter-labelled degree pairs. -/
def componentPath (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :=
  Path.Degrees.liftPath p₀ (SingleObj.pathOfFn (fun j : Fin n => j))
    (SingleObj.degreesPathOfFn Γ (fun j : Fin n => j) β.1.val)

/-- The lifted path is determined by the ray's complete degree history. -/
theorem componentPath_def
    (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    β.componentPath = Path.Degrees.liftPath p₀ (SingleObj.pathOfFn (fun j : Fin n => j))
      (SingleObj.degreesPathOfFn Γ (fun j : Fin n => j) β.1.val) := (rfl)

/-- No original encounter, including an unchanged-degree encounter, is removed. -/
theorem componentPath_length (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    β.componentPath.length = n := by
  rw [componentPath_def, Path.Degrees.length_liftPath]
  exact SingleObj.length_pathOfFn _

/-- Forgetting component degrees recovers every original encounter label. -/
@[simp]
theorem mapPath_componentPath (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    (GradedVertex.forget (ι := fun _ : SingleObj (Fin n) => Γ)).mapPath β.componentPath =
      SingleObj.pathOfFn (fun j : Fin n => j) := by
  rw [componentPath_def, Path.Degrees.mapPath_liftPath]

/-- The source vertex records exactly the prescribed incoming degree. -/
theorem componentPath_source_degree
    (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    (β.componentPath.vertices.head β.componentPath.vertices_ne_nil).degree = p₀ := by
  rw [Path.vertices_head_eq]

/-- A nilpotent component filtration bounds the complete encounter itinerary of
an actual ray. Marks distinguish homogeneous components of the same wall map;
unchanged spatial velocity imposes no restriction on a mark. -/
theorem filtrationEncounterBound (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q)
    (F : ModuleFiltration R M) (w : Fin n → Γ → Γ → ℕ)
    (hT : ∀ e i j k (x : M), x ∈ ℳ i → x ∈ F.submodule k →
      homogeneousComponent ℳ j (T e x) ∈ F.submodule (k + w e i j))
    {r h : ℕ} (hr : F.submodule r = ⊥)
    (hp : Path.IsZeroRunBounded (GradedVertex.componentWeight
      (Q := SingleObj (Fin n)) (fun e => w e)) h β.componentPath) :
    Path.addWeight (GradedVertex.componentWeight
      (Q := SingleObj (Fin n)) (fun e => w e)) β.componentPath < r ∧
      n ≤ r * h + r - 1 := by
  have hnonzero : (SingleObj.pathOfFn (fun j : Fin n => j)).homogeneousHistory
      (M := fun _ => M) (fun e => T e) (fun _ => ℳ)
      (SingleObj.degreesPathOfFn Γ (fun j : Fin n => j) β.1.val) (a : M) ≠ 0 := by
    rw [← homogeneousHistory_eq_pathOfFn]
    exact ((mem_decoratedHistorySupport ℳ T p₀ a v f ε β.1.val).mp β.1.property).1
  have hraise : ComponentTransfersRaise (Q := SingleObj (Fin n))
      (M := fun _ => M) (T := fun e => T e) (ℳ := fun _ => ℳ)
      (F := fun _ => F) (w := fun e => w e) := by
    rw [componentTransfersRaise_iff]
    intro b c e i j k x hxi hxF
    exact hT e i j k x hxi hxF
  have hweight := Path.componentWeight_lt_of_homogeneousHistory_ne_zero
    (SingleObj.pathOfFn (fun j : Fin n => j)) hraise p₀ a.property hr hnonzero
  have hlength := Path.length_add_one_le_of_homogeneousHistory_ne_zero
    (SingleObj.pathOfFn (fun j : Fin n => j)) hraise p₀ a.property hr hnonzero
      (by simpa only [componentPath_def] using hp)
  rw [SingleObj.length_pathOfFn, Nat.mul_add, Nat.mul_one] at hlength
  exact ⟨by simpa only [componentPath_def] using hweight, by omega⟩

/-- A component degree order supplies the encounter bound directly. Every
nonidentity degree transition is marked, even if it lies in the kernel of the
spatial projection. The hypotheses only constrain surviving components. -/
theorem degreeEncounterBound (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q)
    (rank : Γ → ℕ)
    (hT : ∀ e i j (x : M), x ∈ ℳ i → homogeneousComponent ℳ j (T e x) ≠ 0 →
      rank i + (if i = j then 0 else 1) ≤ rank j)
    {r h : ℕ} (hr : ∀ i, r ≤ rank i → ℳ i = ⊥)
    (hp : Path.IsZeroRunBounded (GradedVertex.componentWeight
      (Q := SingleObj (Fin n)) (fun _ i j => if i = j then 0 else 1)) h β.componentPath) :
    Path.addWeight (GradedVertex.componentWeight
      (Q := SingleObj (Fin n)) (fun _ i j => if i = j then 0 else 1)) β.componentPath < r ∧
      n ≤ r * h + r - 1 := by
  apply β.filtrationEncounterBound (componentDegreeFiltration ℳ rank)
    (fun _ i j => if i = j then 0 else 1) ?_ (componentDegreeFiltration_eq_bot ℳ rank hr) hp
  intro e i j k x hxi hxF
  have hraise : ComponentTransfersRaise (Q := SingleObj (Fin n))
      (M := fun _ => M) (T := fun e => T e) (ℳ := fun _ => ℳ)
      (F := fun _ => componentDegreeFiltration ℳ rank)
      (w := fun _ i j => if i = j then 0 else 1) :=
    componentTransfersRaise_of_rank (fun _ => rank) (fun e => hT e)
  rw [componentTransfersRaise_iff] at hraise
  exact hraise (b := SingleObj.star (Fin n)) (c := SingleObj.star (Fin n)) e i j k x hxi hxF

end DecoratedAdmissibleRay

end Mei
