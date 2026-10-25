/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Action
public import Mei.Algebra.Lie.UniversalEnveloping.CompletedLie
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Enveloping representations at finite coefficient order

A filtration-raising Lie action extends to an enveloping-algebra representation
which adds enveloping degree to coefficient order. It therefore factors through
the finite enveloping degree quotient on each finite coefficient quotient. These
representations connect finite enveloping units with coefficient automorphisms.

We use `TauCeti.UniversalEnvelopingAlgebra.representation`, the homogeneous word
spans of `Mei.UniversalEnvelopingAlgebra.homogeneousSubmodule`, and
`Ideal.Quotient.liftₐ`. Quotient equivariance uses Tau Ceti's
`map_smul_of_map_ι_smul`. No basis or faithful representation is required.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Mei.ModuleFiltration

open _root_.UniversalEnvelopingAlgebra
open Mei.UniversalEnvelopingAlgebra

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]
  (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ρ" => TauCeti.UniversalEnvelopingAlgebra.representation R L M
local notation "E" => degreeFiltration ℒ d.degree
  (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem representation_word_mem (l : List (Σ n, ℒ n))
    {b : ℕ} {m : M} (hm : m ∈ F.submodule b) :
    ρ (l.map (fun x => ι R (x.2 : L))).prod m ∈
      F.submodule ((l.map (fun x => (d.degree x.1).toNat)).sum + b) := by
  induction l generalizing b m with
  | nil => simpa using hm
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, Module.End.mul_apply]
    rw [TauCeti.UniversalEnvelopingAlgebra.representation_ι, LieModule.toEnd_apply_apply]
    simpa only [Nat.add_assoc] using
      F.lie_mem_of_mem_homogeneous d ℒ x.2.property (ih hm)

/-- An enveloping element of degree at least `a` raises coefficient order by at least `a`. -/
theorem representation_mem_of_mem_degreeFiltration {a b : ℕ} {u : U} {m : M}
    (hu : u ∈ (E).ideal a) (hm : m ∈ F.submodule b) :
    ρ u m ∈ F.submodule (a + b) := by
  have hs : Mei.DirectSum.degreeTail (homogeneousSubmodule ℒ) d.degree a ≤
      (F.submodule (a + b)).comap
        ((LinearMap.applyₗ m).comp (ρ).toLinearMap) := by
    rw [Mei.DirectSum.degreeTail_def]
    refine iSup_le fun n => iSup_le fun hn => ?_
    apply (homogeneousSubmodule_le_iff ℒ n _).mpr
    intro l hl
    have hbound : (a : ℤ) ≤ ((l.map (fun x => (d.degree x.1).toNat)).sum : ℕ) := by
      calc
        (a : ℤ) ≤ d.degree n := hn
        _ = (l.map (fun x => d.degree x.1)).sum := by
          rw [← hl, map_list_sum]
          simp only [List.map_map, Function.comp_def]
        _ ≤ ((l.map (fun x => (d.degree x.1).toNat)).sum : ℕ) := by
          simp only [Nat.cast_list_sum, List.map_map]
          exact List.sum_le_sum (fun x _ => Int.self_le_toNat _)
    exact F.antitone (Nat.add_le_add_right (by exact_mod_cast hbound) b)
      (F.representation_word_mem d ℒ l hm)
  apply hs
  simpa only [degreeFiltration_ideal, Mei.GradedAlgebra.mem_degreeIdeal_iff] using hu

private theorem lift_quotientLieAction_mk (k : ℕ) (u : U) (m : M) :
    (_root_.UniversalEnvelopingAlgebra.lift R (F.quotientLieAction d ℒ k)) u
        (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (ρ u m) := by
  let q := _root_.UniversalEnvelopingAlgebra.lift R (F.quotientLieAction d ℒ k)
  let := TauCeti.UniversalEnvelopingAlgebra.asModule R L M
  let := TauCeti.UniversalEnvelopingAlgebra.isScalarTower_asModule R L M
  let : Module U (F.quotient k) := Module.compHom _ q.toRingHom
  let : IsScalarTower R U (F.quotient k) :=
    ⟨fun r u a => LinearMap.congr_fun (map_smul q r u) a⟩
  have hq (v : U) (a : F.quotient k) : v • a = q v a := (rfl)
  have he := TauCeti.UniversalEnvelopingAlgebra.map_smul_of_map_ι_smul
    ((F.submodule (k + 1)).mkQ) (fun x m => by
      rw [TauCeti.UniversalEnvelopingAlgebra.asModule_ι_smul]
      simpa only [hq, q, lift_ι_apply, Submodule.mkQ_apply] using
        (F.quotientLieAction_mk d ℒ k x m).symm) u m
  simpa only [Submodule.mkQ_apply,
    TauCeti.UniversalEnvelopingAlgebra.asModule_smul_def, hq, q] using he.symm

/-- The coefficient representation kills the enveloping degree ideal above its cutoff. -/
theorem degreeFiltration_le_ker_quotientAction (k : ℕ) :
    (E).ideal (k + 1) ≤
      RingHom.ker
        (_root_.UniversalEnvelopingAlgebra.lift R (F.quotientLieAction d ℒ k)).toRingHom := by
  intro u hu
  rw [RingHom.mem_ker]
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective q
  rw [Submodule.mkQ_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    lift_quotientLieAction_mk, LinearMap.zero_apply,
    Submodule.Quotient.mk_eq_zero]
  simpa only [Nat.add_zero] using F.representation_mem_of_mem_degreeFiltration d ℒ hu
    (by simp : m ∈ F.submodule 0)

/-- The order-`k` enveloping degree quotient acts on the order-`k` coefficient module. -/
noncomputable def truncatedEnvelopingAction (k : ℕ) :
    (U ⧸ (E).ideal (k + 1)) →ₐ[R] Module.End R (F.quotient k) :=
  Ideal.Quotient.liftₐ ((E).ideal (k + 1))
    (_root_.UniversalEnvelopingAlgebra.lift R (F.quotientLieAction d ℒ k))
    (fun _ hu => RingHom.mem_ker.mp
      (F.degreeFiltration_le_ker_quotientAction d ℒ k hu))

/-- The finite enveloping representation is induced by the original quotient Lie action. -/
@[simp]
theorem truncatedEnvelopingAction_mk (k : ℕ) (u : U) :
    F.truncatedEnvelopingAction d ℒ k (Ideal.Quotient.mk _ u) =
      _root_.UniversalEnvelopingAlgebra.lift R (F.quotientLieAction d ℒ k) u := by
  exact AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp ((E).ideal (k + 1))
    (_root_.UniversalEnvelopingAlgebra.lift R (F.quotientLieAction d ℒ k))
    (fun _ hu => RingHom.mem_ker.mp
      (F.degreeFiltration_le_ker_quotientAction d ℒ k hu))) u

/-- On canonical Lie coordinates, the enveloping representation is the truncated Lie action. -/
@[simp]
theorem truncatedEnvelopingAction_truncatedLieToU (k : ℕ) (x : d.truncatedLie ℒ k) :
    F.truncatedEnvelopingAction d ℒ k (truncatedLieToU d ℒ k x) =
      F.truncatedLieAction d ℒ k x := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  rw [LieIdeal.mkQ_apply, truncatedLieToU_mk, truncatedEnvelopingAction_mk,
    lift_ι_apply, truncatedLieAction_mk]

end Mei.ModuleFiltration
