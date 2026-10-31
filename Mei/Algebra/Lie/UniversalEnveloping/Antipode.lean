/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.Algebra.Lie.UniversalEnveloping.HopfAlgebra

/-!
# The antipode preserves total Lie degree

The antipode reverses homogeneous words and negates their Lie generators,
so it preserves each enveloping homogeneous piece and every degree ideal.
This permits antipode contraction in total-degree tensor quotients.

The proof uses Tau Ceti's enveloping antipode and the homogeneous word spans.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "S" => _root_.HopfAlgebraStruct.antipode R (A := U)

/-- The enveloping antipode preserves each total Lie-degree summand. -/
theorem antipode_mem_homogeneousSubmodule {n : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ n) : S a ∈ homogeneousSubmodule ℒ n := by
  have hw (l : List (Σ i, ℒ i)) :
      S (l.map (fun x => _root_.UniversalEnvelopingAlgebra.ι R (x.2 : L))).prod ∈
        homogeneousSubmodule ℒ (l.map Sigma.fst).sum := by
    induction l with
    | nil => simpa using (SetLike.one_mem_graded (homogeneousSubmodule ℒ))
    | cons x l ih =>
      have hι : S (_root_.UniversalEnvelopingAlgebra.ι R (x.2 : L)) =
          -_root_.UniversalEnvelopingAlgebra.ι R (x.2 : L) := by
        rw [TauCeti.UniversalEnvelopingAlgebra.hopfAlgebraStructAntipode_eq_antipode,
          _root_.UniversalEnvelopingAlgebra.antipode_ι]
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [_root_.HopfAlgebra.antipode_mul_antidistrib, hι]
      simpa only [add_comm] using SetLike.mul_mem_graded ih
        ((homogeneousSubmodule ℒ x.1).neg_mem (ι_mem_homogeneousSubmodule ℒ x.2.property))
  rw [homogeneousSubmodule_def] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    simpa only [hl] using hw l
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using (homogeneousSubmodule ℒ n).add_mem ha hb
  | smul r a _ ha => simpa only [map_smul] using (homogeneousSubmodule ℒ n).smul_mem r ha

variable [DecidableEq Γ] [GradedLieAlgebra ℒ] (d : Γ →+ ℤ)
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "F" => degreeFiltration ℒ d hneg

/-- The enveloping antipode preserves every degree ideal. -/
theorem antipode_mem_degreeFiltration {k : ℕ} {a : U} (ha : a ∈ (F).ideal k) :
    S a ∈ (F).ideal k := by
  have ht : Mei.DirectSum.degreeTail (homogeneousSubmodule ℒ) d k ≤
      (((F).ideal k).restrictScalars R).comap S := by
    simp only [Mei.DirectSum.degreeTail_def, iSup_le_iff]
    intro n hn a ha
    rw [Submodule.mem_comap]
    rw [Submodule.restrictScalars_mem, degreeFiltration_ideal]
    exact Mei.GradedAlgebra.le_degreeIdeal _ d _ hn _
      (antipode_mem_homogeneousSubmodule ℒ ha)
  rw [degreeFiltration_ideal, Mei.GradedAlgebra.mem_degreeIdeal_iff] at ha
  exact ht ha

end Mei.UniversalEnvelopingAlgebra
