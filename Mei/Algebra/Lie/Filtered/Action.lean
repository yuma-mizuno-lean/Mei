/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import Mei.LinearAlgebra.ModuleFiltration.Nilpotent

/-!
# Finite-order filtration-raising Lie actions

A filtration-raising action of a positively graded Lie algebra on a filtered module descends
to the finite-order coefficient modules. The order-`k` action factors through the order-`k`
Lie truncation, every acting endomorphism has `(k + 1)`st power zero, and the quotient
transitions intertwine the actions. These are the finite-order representations needed for
exponentiating actions on completed coefficient modules.

The quotient representation uses Mathlib's `LieSubmodule.Quotient.actionAsEndoMap`.
Nilpotence uses `Submodule.mapQ_pow` and `Module.End.pow_apply_mem_of_map_le` from
`TauCeti.LinearAlgebra.Submodule.CompleteFiltration`. No freeness, separatedness,
finite-dimensionality, or characteristic-zero assumption is needed.
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M]

/-- An action raises filtration orders when Lie terms of degree at least `a + 1` send
module terms of order `b` into order `a + b + 1`. The successor convention agrees with
`PositiveDegrees.degreeSubmodule`, which consists of Lie degrees strictly above its cutoff. -/
class IsFiltrationRaising (d : PositiveDegrees N) (ℒ : N → Submodule R L)
    (F : ModuleFiltration R M) : Prop where
  /-- Lie and module filtration orders add under the action. -/
  lie_mem : ∀ {a b : ℕ} {x : L} {m : M},
    x ∈ d.degreeSubmodule ℒ a → m ∈ F.submodule b →
      ⁅x, m⁆ ∈ F.submodule (a + b + 1)

/-- Restricting a filtration-raising action to a Lie subalgebra preserves the
filtration bound for the inverse-image homogeneous pieces. -/
instance IsFiltrationRaising.lieSubalgebra (d : PositiveDegrees N)
    (ℒ : N → Submodule R L) (F : ModuleFiltration R M)
    [IsFiltrationRaising d ℒ F] (K : LieSubalgebra R L) :
    IsFiltrationRaising d (fun n => (ℒ n).comap K.incl.toLinearMap) F where
  lie_mem {a b x m} hx hm := by
    have hle : d.degreeSubmodule (fun n => (ℒ n).comap K.incl.toLinearMap) a ≤
        (d.degreeSubmodule ℒ a).comap K.incl.toLinearMap := by
      rw [d.degreeSubmodule_def]
      exact iSup_le fun n => Submodule.comap_mono (d.le_degreeSubmodule ℒ n.property)
    exact IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F) (hle hx) hm

namespace ModuleFiltration

variable (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)

section Module

variable [DecidableEq N] [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

include d ℒ

omit [DecidableEq N] [DirectSum.Decomposition ℒ] in
/-- A homogeneous Lie element raises coefficient order by its integral degree. -/
theorem lie_mem_of_mem_homogeneous
    {n : N} {x : L} (hx : x ∈ ℒ n) {b : ℕ} {m : M} (hm : m ∈ F.submodule b) :
    ⁅x, m⁆ ∈ F.submodule ((d.degree n).toNat + b) := by
  by_cases hn : 0 < d.degree n
  · have hx' : x ∈ d.degreeSubmodule ℒ ((d.degree n).toNat - 1) :=
      d.le_degreeSubmodule ℒ (by omega) hx
    have h := IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F) hx' hm
    have he : (d.degree n).toNat - 1 + b + 1 = (d.degree n).toNat + b := by omega
    exact he ▸ h
  · have hx0 : x = 0 := by
      simpa only [d.eq_bot_of_degree_nonpos ℒ n (by omega), Submodule.mem_bot] using hx
    simp [hx0]

/-- Every Lie element raises the module filtration by at least one. -/
theorem lie_mem_succ (x : L) {b : ℕ} {m : M} (hm : m ∈ F.submodule b) :
    ⁅x, m⁆ ∈ F.submodule (b + 1) := by
  simpa only [Nat.zero_add] using
    IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F)
      (by simp : x ∈ d.degreeSubmodule ℒ 0) hm

/-- Every filtration term is a Lie submodule for a filtration-raising action. -/
def lieSubmodule (b : ℕ) : LieSubmodule R L M where
  toSubmodule := F.submodule b
  lie_mem := fun {x _} hm => F.antitone (Nat.le_succ b) (F.lie_mem_succ d ℒ x hm)

/-- Passing to the stable Lie submodule preserves the original filtration term. -/
@[simp]
theorem lieSubmodule_toSubmodule (b : ℕ) :
    (F.lieSubmodule d ℒ b).toSubmodule = F.submodule b := (rfl)

/-- Membership in a stable Lie submodule is membership in the original filtration term. -/
@[simp]
theorem mem_lieSubmodule {b : ℕ} {m : M} :
    m ∈ F.lieSubmodule d ℒ b ↔ m ∈ F.submodule b := (Iff.rfl)

variable [LieModule R L M]

/-- The representation on the module retaining coefficient orders at most `k`. -/
def quotientLieAction (k : ℕ) : L →ₗ⁅R⁆ Module.End R (F.quotient k) :=
  LieSubmodule.Quotient.actionAsEndoMap (F.lieSubmodule d ℒ (k + 1))

/-- On representatives, the quotient representation is the original Lie action. -/
@[simp]
theorem quotientLieAction_mk (k : ℕ) (x : L) (m : M) :
    F.quotientLieAction d ℒ k x (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk ⁅x, m⁆ := (rfl)

/-- The underlying endomorphism is the generic filtration-raising quotient map. -/
theorem quotientLieAction_eq_quotientRaisingEnd (k : ℕ) (x : L) :
    F.quotientLieAction d ℒ k x =
      F.quotientRaisingEnd (LieModule.toEnd R L M x)
        (fun _ _ hm => F.lie_mem_succ d ℒ x hm) k := by
  apply LinearMap.ext
  intro a
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective a
  exact (F.quotientLieAction_mk d ℒ k x m).trans
    (F.quotientRaisingEnd_mk (LieModule.toEnd R L M x)
      (fun _ _ hm => F.lie_mem_succ d ℒ x hm) k m).symm

/-- At order `k`, the `(k + 1)`st power of every acting endomorphism vanishes. -/
@[simp]
theorem quotientLieAction_pow_eq_zero (k : ℕ) (x : L) :
    F.quotientLieAction d ℒ k x ^ (k + 1) = 0 := by
  rw [quotientLieAction_eq_quotientRaisingEnd]
  exact F.quotientRaisingEnd_pow_eq_zero _ _ k

/-- Every finite-order acting endomorphism is nilpotent, over any commutative ring. -/
theorem isNilpotent_quotientLieAction (k : ℕ) (x : L) :
    IsNilpotent (F.quotientLieAction d ℒ k x) := by
  rw [quotientLieAction_eq_quotientRaisingEnd]
  exact F.isNilpotent_quotientRaisingEnd _ _ k

/-- Coefficient transitions intertwine the finite-order representations. -/
@[simp]
theorem transition_quotientLieAction {k l : ℕ} (h : k ≤ l) (x : L) (q : F.quotient l) :
    F.transition h (F.quotientLieAction d ℒ l x q) =
      F.quotientLieAction d ℒ k x (F.transition h q) := by
  simp only [quotientLieAction_eq_quotientRaisingEnd]
  exact F.transition_quotientRaisingEnd _ _ h q

end Module

section Lie

variable [LieModule R L M] [DecidableEq N] [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ] [IsFiltrationRaising d ℒ F]

/-- Lie terms above order `k` act trivially on the order-`k` coefficient module. -/
theorem degreeIdeal_le_ker_quotientLieAction (k : ℕ) :
    d.degreeIdeal ℒ k ≤ (F.quotientLieAction d ℒ k).ker := by
  intro x hx
  rw [LieHom.mem_ker]
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective q
  rw [Submodule.mkQ_apply, quotientLieAction_mk, LinearMap.zero_apply,
    Submodule.Quotient.mk_eq_zero]
  have hx' : x ∈ d.degreeSubmodule ℒ k := by
    rw [← d.degreeIdeal_toSubmodule ℒ k]
    exact hx
  simpa only [Nat.add_zero] using
    IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F) hx'
      (by simp : m ∈ F.submodule 0)

/-- The action of the order-`k` Lie truncation on the order-`k` coefficient module. -/
def truncatedLieAction (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ Module.End R (F.quotient k) :=
  (d.degreeIdeal ℒ k).liftQ (F.quotientLieAction d ℒ k)
    (F.degreeIdeal_le_ker_quotientLieAction d ℒ k)

/-- The truncated representation agrees with the quotient action on Lie representatives. -/
@[simp]
theorem truncatedLieAction_mk (k : ℕ) (x : L) :
    F.truncatedLieAction d ℒ k (LieSubmodule.Quotient.mk x) =
      F.quotientLieAction d ℒ k x := by
  simp [truncatedLieAction]

/-- The nilpotence bound holds for arbitrary elements of the Lie truncation. -/
theorem truncatedLieAction_pow_eq_zero (k : ℕ) (x : d.truncatedLie ℒ k) :
    F.truncatedLieAction d ℒ k x ^ (k + 1) = 0 := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  rw [LieIdeal.mkQ_apply, truncatedLieAction_mk]
  exact F.quotientLieAction_pow_eq_zero d ℒ k x

/-- Lie and coefficient truncations commute with their finite-order actions. -/
@[simp]
theorem transition_truncatedLieAction {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (q : F.quotient l) :
    F.transition h (F.truncatedLieAction d ℒ l x q) =
      F.truncatedLieAction d ℒ k (d.truncationMap ℒ h x) (F.transition h q) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, truncatedLieAction_mk, PositiveDegrees.truncationMap_mk]
  exact F.transition_quotientLieAction d ℒ h x q

end Lie

end ModuleFiltration
end Mei
