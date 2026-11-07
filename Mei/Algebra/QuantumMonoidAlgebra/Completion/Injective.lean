/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Completion
public import Mei.Algebra.QuantumMonoidAlgebra.Positive.Injective
public import Mei.RingTheory.FilteredAlgebra.Map.Injective

/-!
# Faithful transport of completed positive quantum coefficients

Injective scalar maps and exponent maps injective on the positive monoid induce
injective maps of positive completions. Source cutoffs have finite support, so
their images lie below some target cutoff even when the given degree-map modulus
changes order. No injectivity of the finite quotient maps is assumed.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ hn => d.degree_nonneg hn)
local notation "G" => positiveFiltration q' β' e.monoid e.degree (fun _ hn => e.degree_nonneg hn)

/-- An injective scalar map and an exponent map injective on the positive monoid
induce an injective map of its quantum completion. -/
theorem mapPositiveCompletion_injective (hφ : Function.Injective φ)
    (hT : Set.InjOn T d.monoid) :
    Function.Injective (mapPositiveCompletion d e T φ h) := by
  have hmap : mapPositiveCompletion d e T φ h =
      (F).mapCompletion (G)
        (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn))
        T.modulus T.monotone_modulus (positiveMap_ideal_le d e T φ h) := by
    apply RingHom.ext
    intro x
    apply (G).completion_ext
    intro k
    exact (projection_mapPositiveCompletion d e T φ h k x).trans
      ((F).projection_mapCompletion (G)
        (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn))
        T.modulus T.monotone_modulus (positiveMap_ideal_le d e T φ h) k x).symm
  rw [hmap]
  exact (F).mapCompletion_injective_of_comap_le (G) _ _ _ _
    (positiveMap_comap_ideal_le d e T φ h hφ hT)

end Mei.QuantumMonoidAlgebra
