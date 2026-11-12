/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion.Local

/-!
# Lower-degree recursions with degree-dependent event types

An output degree may use its own event inventory, for example wall events in a
geometric truncation chosen by that degree. Tagging each event by its output degree
places all inventories in the existing lower-step construction. The resulting
operator has the same strict-degree nilpotence and local finite-sum solution.
No finiteness of the entire event type is required; each endpoint uses a finite set.
-/

public noncomputable section

open TauCeti (PositiveDegrees)

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ R M V : Type*} [AddCommGroup Γ] [Semiring R]
  [AddCommMonoid M] [Module R M] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ) (k : ℕ)
  {ι : d.cutoff k → Type*}
  (events : (Q : V) → (n : d.cutoff k) → Finset (ι n))
  (block : (n : d.cutoff k) → ι n → (m : d.cutoff k) → d.Precedes m.val n.val →
    ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
  (point : (n : d.cutoff k) → ι n → V → d.cutoff k → V)

open Classical in
private def taggedBlock (b : Σ n, ι n) (n m : d.cutoff k)
    (hmn : d.Precedes m.val n.val) : ℳ (p + m.val) →ₗ[R] ℳ (p + n.val) :=
  if h : b.1 = n then block n (h ▸ b.2) m hmn else 0

open Classical in
private def taggedPoint (b : Σ n, ι n) (Q : V) (n m : d.cutoff k) : V :=
  if h : b.1 = n then point n (h ▸ b.2) Q m else Q

/-- The lower-degree step with a separate event type for each output degree. -/
def shiftedDependentLowerStep : Module.End R (ShiftedEndpointFunction d ℳ p V k) :=
  shiftedLowerStep d ℳ p k (fun Q n => (events Q n).map (Function.Embedding.sigmaMk n))
    (taggedBlock d ℳ p k block) (taggedPoint d k point)

/-- The dependent step sums the output degree's own events and preceding inputs. -/
theorem shiftedDependentLowerStep_apply
    (F : ShiftedEndpointFunction d ℳ p V k) (Q : V) (n : d.cutoff k) :
    shiftedDependentLowerStep d ℳ p k events block point F Q n =
      ∑ b ∈ events Q n, ∑ m : d.cutoff k,
        if hmn : d.Precedes m.val n.val then block n b m hmn (F (point n b Q m) m)
        else 0 := by
  classical
  simp only [shiftedDependentLowerStep, shiftedLowerStep_apply, Finset.sum_map,
    Function.Embedding.sigmaMk_apply, taggedBlock, taggedPoint, ↓reduceDIte]
  rfl

/-- Tagging degree-dependent inventories preserves strict-degree nilpotence. -/
theorem shiftedDependentLowerStep_pow_eq_zero :
    (shiftedDependentLowerStep d ℳ p k events block point) ^ (k + 1) = 0 :=
  shiftedLowerStep_pow_eq_zero d ℳ p k _ _ _

/-- Actual local recurrences with degree-dependent inventories have the shared
finite-sum solution, provided every nonzero block reads in its input domain. -/
theorem eqOn_finiteRecursion_of_shiftedDependentLowerStep_eq_add
    (Ω : d.cutoff k → Set V)
    (hΩ : ∀ Q n, Q ∈ Ω n → ∀ b ∈ events Q n, ∀ m hmn,
      block n b m hmn ≠ 0 → point n b Q m ∈ Ω m)
    (a F : ShiftedEndpointFunction d ℳ p V k)
    (hF : ∀ Q n, Q ∈ Ω n →
      F Q n = a Q n + shiftedDependentLowerStep d ℳ p k events block point F Q n) :
    ∀ n, Set.EqOn (F · n)
      ((Module.End.finiteRecursion
        (shiftedDependentLowerStep d ℳ p k events block point) (k + 1) a) · n) (Ω n) := by
  classical
  apply eqOn_finiteRecursion_of_shiftedLowerStep_eq_add d ℳ p k
    (fun Q n => (events Q n).map (Function.Embedding.sigmaMk n))
    (taggedBlock d ℳ p k block) (taggedPoint d k point) Ω ?_ a F hF
  intro Q n hQ b hb m hmn hblock
  obtain ⟨j, hj, hjb⟩ := Finset.mem_map.mp hb
  subst b
  simp only [Function.Embedding.sigmaMk_apply, taggedBlock, ↓reduceDIte] at hblock
  simp only [Function.Embedding.sigmaMk_apply, taggedPoint, ↓reduceDIte]
  exact hΩ Q n hQ j hj m hmn hblock

end TauCeti.PositiveDegrees
