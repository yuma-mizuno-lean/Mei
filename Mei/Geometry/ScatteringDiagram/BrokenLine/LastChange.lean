/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Admissible.Terminal
public import Mei.LinearAlgebra.GradedModule.History.Erasure
import Mei.Data.Fin.LastChange

/-!
# The last degree change of a decorated ray

For propagation maps whose diagonal homogeneous component is the identity, an
actual decorated ray is either unchanged throughout or has a unique last change
of degree. After that encounter its whole decoration is constant and its path
is straight, including any recorded encounters that leave the degree unchanged.
The final decoration is exactly the selected component at the last change.

The index runs backwards from the endpoint. A change in the kernel of the
spatial velocity map is still a degree change, even though the terminal path
continues straight through it. These statements isolate the terminal piece for
recursions comparing probe coefficients with broken-line sums. For the
broken-line conventions and endpoint transport, see Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Definition 2.10 and
§3.3.3 (arXiv:1503.06183v5).

We use `homogeneousHistoryStage_eq_of_degrees_eq` for whole decorations and
`AdmissibleRayRealization.ray_eq_endpoint_sub_smul` for the actual path.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {velocity : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)

local notation "b" => Fin.snoc (α := fun _ => Γ) (Subtype.val (Sigma.fst r)) p₀

/-- If all segment degrees equal the incoming degree, the whole final
decoration is the input and the entire negative half-line is straight.
Recorded unchanged-degree encounters are allowed. -/
theorem decoration_eq_input_and_ray_eq_of_degrees_eq
    (hT : ∀ j s x, x ∈ ℳ s → (DirectSum.decompose ℳ (T j x) s : M) = x)
    (hr : ∀ i, b i = p₀) :
    r.decoration 0 = (a : M) ∧ ∀ t ≤ 0, r.2.ray t = Q - t • velocity p₀ := by
  have hstage := homogeneousHistoryStage_eq_of_degrees_eq r.1.val (fun j => hT j _) a.property
    (Fin.last n) (fun i _ => (hr i).trans (hr 0).symm)
  refine ⟨?_, fun t ht => ?_⟩
  · simpa only [homogeneousHistoryStage_last, LinearMap.id_apply,
      decoration_zero] using hstage.symm
  · simpa only [hr] using r.2.ray_eq_endpoint_sub_smul_of_directions_eq
      (fun i => congrArg velocity ((hr i).trans (hr 0).symm)) ht

/-- A nonconstant degree history has a unique last changing encounter. Its
incoming degree differs from the final degree; every later segment has the final
degree, its whole output is the final decoration, and the closed terminal piece
is straight. Only diagonal preservation at the final degree is required.
Degree changes of zero spatial velocity are included. -/
theorem existsUnique_last_degree_change
    (hT : ∀ j x, x ∈ ℳ (b 0) → (DirectSum.decompose ℳ (T j x) (b 0) : M) = x)
    (hr : ¬ ∀ i, b i = b 0) :
    ∃! j : Fin n, b j.succ ≠ b 0 ∧
      (∀ i ≤ j.castSucc, b i = b 0) ∧
      r.decoration 0 = (DirectSum.decompose ℳ (T j (r.decoration j.succ)) (b 0) : M) ∧
      ∀ t ∈ Icc (r.2.parameter j.succ) 0, r.2.ray t = Q - t • velocity (b 0) := by
  obtain ⟨j, ⟨hne, hp⟩, hu⟩ := Fin.existsUnique_first_change b hr
  have hweight : r.decoration 0 = r.decoration j.castSucc := by
    simpa only [decoration_def, homogeneousHistoryStage_zero] using
      (homogeneousHistoryStage_eq_of_degrees_eq r.1.val hT a.property j.castSucc hp).symm
  refine ⟨j, ⟨hne, hp, ?_, ?_⟩, fun l hl => hu l ⟨hl.1, hl.2.1⟩⟩
  · have hj : r.1.val j = b 0 := by
      simpa only [Fin.snoc_castSucc] using hp j.castSucc le_rfl
    rw [hweight, r.decoration_castSucc, hj]
  · intro t ht
    apply r.2.ray_eq_endpoint_sub_smul j.succ _ ht
    intro i hi
    exact congrArg velocity (hp i (Fin.le_castSucc_iff.mpr hi))

end Mei.DecoratedAdmissibleRay
