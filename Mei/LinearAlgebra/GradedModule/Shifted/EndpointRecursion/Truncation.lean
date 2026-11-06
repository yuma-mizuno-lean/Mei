/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion
public import Mathlib.LinearAlgebra.Pi

/-!
# Truncating lower-degree endpoint steps

Restricting endpoint functions to a smaller degree cutoff commutes with a
lower-degree step. For a retained output, every contributing input has smaller
degree and is therefore retained as well. The event sets and read points may
depend on both the endpoint and the output degree; no geometric hypothesis on
the endpoint space is required. Coefficients are semimodules.

This permits combining recurrences proved at different orders on the same
endpoint functions, without retaining spurious higher-degree input terms.
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M V : Type*} [AddCommGroup Γ] [Semiring R]
  [AddCommMonoid M] [Module R M] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ)

/-- Forget coefficients beyond a smaller cutoff, retaining every endpoint. -/
def shiftedEndpointRestrict {k l : ℕ} (hkl : k ≤ l) :
    ShiftedEndpointFunction d ℳ p V l →ₗ[R] ShiftedEndpointFunction d ℳ p V k :=
  LinearMap.pi fun Q => LinearMap.pi fun n =>
    (LinearMap.proj (⟨n.val, d.cutoff_mono hkl n.property⟩ : d.cutoff l) :
      ((m : d.cutoff l) → ℳ (p + m.val)) →ₗ[R] ℳ (p + n.val)).comp
      (LinearMap.proj Q)

/-- Restriction reads the same whole homogeneous coefficient. -/
@[simp]
theorem shiftedEndpointRestrict_apply {k l : ℕ} (hkl : k ≤ l)
    (F : ShiftedEndpointFunction d ℳ p V l) (Q : V) (n : d.cutoff k) :
    shiftedEndpointRestrict d ℳ p hkl F Q n =
      F Q ⟨n.val, d.cutoff_mono hkl n.property⟩ := (rfl)

/-- Restriction to the current cutoff is the identity. -/
@[simp]
theorem shiftedEndpointRestrict_refl (k : ℕ) :
    shiftedEndpointRestrict (V := V) d ℳ p (le_refl k) = LinearMap.id := by
  ext F Q n
  rfl

/-- Successive restrictions agree with restriction to the smallest cutoff. -/
@[simp]
theorem shiftedEndpointRestrict_comp {k l t : ℕ} (hkl : k ≤ l) (hlt : l ≤ t) :
    (shiftedEndpointRestrict (V := V) d ℳ p hkl).comp
      (shiftedEndpointRestrict d ℳ p hlt) =
        shiftedEndpointRestrict d ℳ p (hkl.trans hlt) := by
  ext F Q n
  rfl

/-- The restriction of a lower-degree step is the step on its retained blocks,
event sets and read points. Inputs outside the smaller cutoff cannot contribute
to any retained output. -/
theorem shiftedEndpointRestrict_shiftedLowerStep {k l : ℕ} (hkl : k ≤ l)
    {ι : Type*} (events : V → d.cutoff l → Finset ι)
    (block : ι → (n m : d.cutoff l) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff l) → V)
    (F : ShiftedEndpointFunction d ℳ p V l) :
    shiftedEndpointRestrict d ℳ p hkl (shiftedLowerStep d ℳ p l events block point F) =
      shiftedLowerStep d ℳ p k
        (fun Q n => events Q ⟨n.val, d.cutoff_mono hkl n.property⟩)
        (fun b n m hmn => block b ⟨n.val, d.cutoff_mono hkl n.property⟩
          ⟨m.val, d.cutoff_mono hkl m.property⟩ hmn)
        (fun b Q n m => point b Q ⟨n.val, d.cutoff_mono hkl n.property⟩
          ⟨m.val, d.cutoff_mono hkl m.property⟩)
        (shiftedEndpointRestrict d ℳ p hkl F) := by
  classical
  funext Q n
  simp only [shiftedEndpointRestrict_apply, shiftedLowerStep_apply]
  apply Finset.sum_congr rfl
  intro b _
  symm
  apply Fintype.sum_of_injective
    (fun m : d.cutoff k => (⟨m.val, d.cutoff_mono hkl m.property⟩ : d.cutoff l))
    (fun m m' he => Subtype.ext (congrArg (fun m : d.cutoff l => m.val) he))
  · intro m hm
    have hnot : ¬ d.Precedes m.val n.val := by
      intro hmn
      apply hm
      exact ⟨⟨m.val, d.mem_cutoff.mpr ⟨(d.mem_cutoff.mp m.property).1,
        (degree_lt_of_precedes d hmn).le.trans (d.mem_cutoff.mp n.property).2⟩⟩,
        Subtype.ext rfl⟩
    simp only [hnot, ↓reduceDIte]
  · intro m
    rfl

end Mei.PositiveDegrees
