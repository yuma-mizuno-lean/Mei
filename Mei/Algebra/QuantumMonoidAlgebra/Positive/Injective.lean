/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Positive
public import TauCeti.Algebra.PositiveDegrees.FinitelyGenerated
public import Mei.Algebra.QuantumMonoidAlgebra.Hom.Injective

/-!
# Detection of positive quantum filtrations under faithful transport

Injective scalar maps and exponent maps injective on the positive monoid reflect
each source degree cutoff at some target cutoff. Finite source degree cutoffs
supply the target bound; equal or strictly preserved degrees are not required.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)
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

/-- Faithful scalar and positive exponent maps reflect every source cutoff at some
target cutoff. The exponent map need only be injective on the allowed monoid. -/
theorem positiveMap_comap_ideal_le (hφ : Function.Injective φ)
    (hT : Set.InjOn T d.monoid) (k : ℕ) :
    ∃ j, ((G).ideal (j + 1)).comap
      (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn)) ≤
      (F).ideal (k + 1) := by
  classical
  let I := (d.finite_cutoff k).toFinset
  let j := I.sup fun n => (e.degree (T n)).toNat
  refine ⟨j, ?_⟩
  intro x hx
  rw [mem_positiveFiltration_iff]
  intro n hn
  by_cases hnP : n ∈ d.monoid
  · have hnI : n ∈ I := by
      simpa only [I, Set.Finite.mem_toFinset, PositiveDegrees.mem_cutoff] using
        And.intro hnP (by omega : d.degree n ≤ k)
    have hnj : (e.degree (T n)).toNat ≤ j :=
      Finset.le_sup (f := fun n => (e.degree (T n)).toNat) hnI
    have hdeg : e.degree (T n) < (j + 1 : ℕ) := by omega
    have hzero := (mem_positiveFiltration_iff q' β' e.monoid e.degree
      (fun _ hn => e.degree_nonneg hn) (j + 1) _).mp hx (T n) hdeg
    have hcoeff := repr_map_of_injOn φ T.toAddMonoidHom h d.monoid hT
      (x : QuantumMonoidAlgebra q β)
      (fun m hm => by
        by_contra hmP
        exact hm ((mem_positiveSubalgebra_iff q β d.monoid x).mp x.property m hmP)) n hnP
    rw [coe_positiveMap, hcoeff] at hzero
    exact hφ (hzero.trans (map_zero φ).symm)
  · exact (mem_positiveSubalgebra_iff q β d.monoid x).mp x.property n hnP

end Mei.QuantumMonoidAlgebra
