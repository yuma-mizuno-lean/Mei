/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion
public import Mei.LinearAlgebra.End.Recursion

/-!
# Lower-degree recursions on endpoint domains

Geometric recursion equations may hold only on generic endpoint domains, and
these domains may depend on the retained degree. If each contributing block
reads inside the corresponding input domain, the source determines every
solution on those domains. No recurrence or comparison is required elsewhere.
Zero blocks impose no condition on their read points.

The proof cuts off the event sets and endpoint functions outside the domains, then
uses the shared nilpotent recursion uniqueness theorem. Thus exceptional
endpoint values do not require a second solution construction. The resulting
finite-sum formula uses the original endpoint operator and any extension of
the source. This is a supplier for the generic-endpoint comparison in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open TauCeti (PositiveDegrees)

namespace TauCeti.PositiveDegrees


variable {Γ R M V ι : Type*} [AddCommGroup Γ] [Semiring R]
  [AddCommMonoid M] [Module R M] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ) (k : ℕ)
  (events : V → d.cutoff k → Finset ι)
  (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
    ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
  (point : ι → V → (n m : d.cutoff k) → V)
  (Ω : d.cutoff k → Set V)
  (hΩ : ∀ Q n, Q ∈ Ω n → ∀ b ∈ events Q n, ∀ m hmn,
    block b n m hmn ≠ 0 → point b Q n m ∈ Ω m)

local notation "U" => (shiftedLowerStep d ℳ p k events block point)

include hΩ in
/-- Solutions of the same lower-degree recursion agree on degree-dependent
endpoint domains closed under nonzero contributing blocks. Their sources need
only agree there; values and equations outside the domains are irrelevant. -/
theorem eqOn_of_shiftedLowerStep_eq_add
    (a c F G : ShiftedEndpointFunction d ℳ p V k)
    (hac : ∀ n, Set.EqOn (a · n) (c · n) (Ω n))
    (hF : ∀ Q n, Q ∈ Ω n → F Q n = a Q n + U F Q n)
    (hG : ∀ Q n, Q ∈ Ω n → G Q n = c Q n + U G Q n) :
    ∀ n, Set.EqOn (F · n) (G · n) (Ω n) := by
  classical
  let mask (X : ShiftedEndpointFunction d ℳ p V k) :=
    fun Q n => if Q ∈ Ω n then X Q n else 0
  let events' Q n := if Q ∈ Ω n then events Q n else ∅
  let U' := shiftedLowerStep d ℳ p k events' block point
  have hstep (X : ShiftedEndpointFunction d ℳ p V k) :
      U' (mask X) = mask (U X) := by
    funext Q n
    by_cases hQ : Q ∈ Ω n
    · simp only [U', shiftedLowerStep_apply, events', hQ, ↓reduceIte, mask]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro m _
      by_cases hmn : d.Precedes m.val n.val
      · simp only [hmn, ↓reduceDIte]
        by_cases hz : block b n m hmn = 0
        · simp only [hz, LinearMap.zero_apply]
        · simp only [hΩ Q n hQ b hb m hmn hz, ↓reduceIte]
      · simp only [hmn, ↓reduceDIte]
    · simp only [U', shiftedLowerStep_apply, events', hQ, ↓reduceIte,
        Finset.sum_empty, mask]
  have hrec (a F : ShiftedEndpointFunction d ℳ p V k)
      (hF : ∀ Q n, Q ∈ Ω n → F Q n = a Q n + U F Q n) :
      mask F = mask a + U' (mask F) := by
    rw [hstep]
    funext Q n
    by_cases hQ : Q ∈ Ω n
    · simpa only [mask, hQ, ↓reduceIte, Pi.add_apply] using hF Q n hQ
    · simp only [mask, hQ, ↓reduceIte, Pi.add_apply, add_zero]
  have hsource : mask a = mask c := by
    funext Q n
    by_cases hQ : Q ∈ Ω n
    · simpa only [mask, hQ, ↓reduceIte] using hac n hQ
    · simp only [mask, hQ, ↓reduceIte]
  have heq := Module.End.eq_of_eq_add_of_pow_eq_zero U'
    (shiftedLowerStep_pow_eq_zero d ℳ p k events' block point)
    (hrec a F hF) (hsource.symm ▸ hrec c G hG)
  intro n Q hQ
  simpa only [mask, hQ, ↓reduceIte] using congrFun (congrFun heq Q) n

include hΩ in
/-- A recursion valid only on the endpoint domains still has the original
finite-sum solution there. Any extension of the source away from the domains
gives the same values; the operator and its zero terms are unchanged. -/
theorem eqOn_finiteRecursion_of_shiftedLowerStep_eq_add
    (a F : ShiftedEndpointFunction d ℳ p V k)
    (hF : ∀ Q n, Q ∈ Ω n → F Q n = a Q n + U F Q n) :
    ∀ n, Set.EqOn (F · n) ((Module.End.finiteRecursion U (k + 1) a) · n) (Ω n) := by
  apply eqOn_of_shiftedLowerStep_eq_add d ℳ p k events block point Ω hΩ a a F
    (Module.End.finiteRecursion U (k + 1) a) (fun _ _ _ => rfl) hF
  intro Q n _
  exact congrFun (congrFun (Module.End.finiteRecursion_eq_add U
    (shiftedLowerStep_pow_eq_zero d ℳ p k events block point) a) Q) n

end TauCeti.PositiveDegrees
