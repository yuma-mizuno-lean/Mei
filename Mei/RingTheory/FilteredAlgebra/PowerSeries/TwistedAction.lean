/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Action
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Map
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Semiconj

/-!
# Twisted two-sided actions of completed series

Rescaling the left unit series before evaluation gives a linear action on the
completed coefficient algebra. The right factor is the inverse of the original
series. This action preserves all completion ideals; the left and right factors
need not agree, so it generally does not preserve the algebra unit. Compatible
scalar and coefficient maps intertwine the action and its inverse, transporting
the rescaling parameter by the scalar map. No injectivity is assumed.
On each associated graded piece the action is the identity: subtracting the
original coefficient raises its order by at least one, with arbitrary unit constant term.
-/

public section
noncomputable section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

/-- Left evaluation of a rescaled unit and right evaluation of its original inverse. -/
def completedTwistedSeriesAction (x : F.completionIdeal 1) (c : R) :
    (PowerSeries R)ˣ →* (F.completion ≃ₗ[R] F.completion) where
  toFun H :=
    (Units.mulLeftLinearEquiv R F.completion
      (Units.map (F.completedAeval x).toMonoidHom
        (Units.map (PowerSeries.rescale c).toMonoidHom H))).trans
      (Units.mulRightLinearEquiv R
        (Units.map (F.completedAeval x).toMonoidHom (H⁻¹)))
  map_one' := by ext a; simp
  map_mul' H K := by ext a; simp [mul_assoc]

/-- The twisted action has the prescribed rescaled left factor. -/
theorem completedTwistedSeriesAction_apply (x : F.completionIdeal 1) (c : R)
    (H : (PowerSeries R)ˣ) (a : F.completion) :
    F.completedTwistedSeriesAction x c H a =
      F.completedAeval x (PowerSeries.rescale c (H : PowerSeries R)) * a *
        F.completedAeval x (↑(H⁻¹) : PowerSeries R) := by
  -- Both unit-multiplication equivalences and their trans composition compute pointwise.
  rfl

/-- Inverting the series reverses the twisted action. -/
@[simp]
theorem completedTwistedSeriesAction_inv (x : F.completionIdeal 1) (c : R)
    (H : (PowerSeries R)ˣ) :
    F.completedTwistedSeriesAction x c (H⁻¹) =
      (F.completedTwistedSeriesAction x c H).symm :=
  map_inv (F.completedTwistedSeriesAction x c) H

/-- Multiplication by the two evaluated factors preserves every completion ideal. -/
theorem completedTwistedSeriesAction_mem (x : F.completionIdeal 1) (c : R)
    (H : (PowerSeries R)ˣ) (k : ℕ) {a : F.completion} (ha : a ∈ F.completionIdeal k) :
    F.completedTwistedSeriesAction x c H a ∈ F.completionIdeal k := by
  rw [completedTwistedSeriesAction_apply]
  exact (F.completionIdeal k).mul_mem_right _ ((F.completionIdeal k).mul_mem_left _ ha)

/-- The twisted action preserves and reflects the full ideal filtration. -/
@[simp]
theorem completedTwistedSeriesAction_mem_iff (x : F.completionIdeal 1) (c : R)
    (H : (PowerSeries R)ˣ) (k : ℕ) (a : F.completion) :
    F.completedTwistedSeriesAction x c H a ∈ F.completionIdeal k ↔
      a ∈ F.completionIdeal k := by
  constructor
  · intro ha
    have he := F.completedTwistedSeriesAction_mem x c (H⁻¹) k ha
    simpa only [completedTwistedSeriesAction_inv, LinearEquiv.symm_apply_apply] using he
  · exact F.completedTwistedSeriesAction_mem x c H k

/-- A twisted series action is the identity on each associated graded piece. -/
theorem completedTwistedSeriesAction_sub_mem (x : F.completionIdeal 1) (c : R)
    (H : (PowerSeries R)ˣ) (k : ℕ) {a : F.completion}
    (ha : a ∈ F.completionIdeal k) :
    F.completedTwistedSeriesAction x c H a - a ∈ F.completionIdeal (k + 1) := by
  let u := F.completedAeval x (H : PowerSeries R)
  let v := F.completedAeval x (↑(H⁻¹) : PowerSeries R)
  let w := F.completedAeval x (PowerSeries.rescale c (H : PowerSeries R))
  let r := algebraMap R F.completion (PowerSeries.constantCoeff (H : PowerSeries R))
  have hwu : w - u ∈ F.completionIdeal 1 := by
    have h := F.completedAeval_mem_first x
      (f := PowerSeries.rescale c (H : PowerSeries R) - (H : PowerSeries R))
      (by simp only [map_sub, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_rescale, pow_zero, one_mul, sub_self])
    simpa only [map_sub] using h
  have hur : u - r ∈ F.completionIdeal 1 := by
    have h := F.completedAeval_mem_first x
      (f := (H : PowerSeries R) - PowerSeries.C (PowerSeries.constantCoeff (H : PowerSeries R)))
      (by simp)
    simpa only [map_sub, F.completedAeval_C] using h
  have hc : u * a - a * u ∈ F.completionIdeal (k + 1) := by
    have hleft : (u - r) * a ∈ F.completionIdeal (k + 1) := by
      simpa only [Nat.add_comm] using F.mul_mem_completionIdeal hur ha
    have hright := F.mul_mem_completionIdeal ha hur
    have he : (u - r) * a - a * (u - r) = u * a - a * u := by
      rw [sub_mul, mul_sub, (Algebra.commutes (PowerSeries.constantCoeff
        (H : PowerSeries R)) a)]
      abel
    exact he ▸ (F.completionIdeal (k + 1)).sub_mem hleft hright
  have hw : (w - u) * a ∈ F.completionIdeal (k + 1) := by
    simpa only [Nat.add_comm] using F.mul_mem_completionIdeal hwu ha
  have huv : u * v = 1 := by
    dsimp [u, v]
    rw [← map_mul, Units.mul_inv, map_one]
  have he : ((w - u) * a + (u * a - a * u)) * v = w * a * v - a := by
    simp only [add_mul, sub_mul, mul_assoc, huv, mul_one]
    abel
  rw [completedTwistedSeriesAction_apply]
  exact he ▸ (F.completionIdeal (k + 1)).mul_mem_right v
    ((F.completionIdeal (k + 1)).add_mem hw hc)

/-- Twisted actions respect products when the left evaluation point carries the second twist. -/
@[simp]
theorem completedTwistedSeriesAction_mul (x : F.completionIdeal 1) (c d : R)
    (H : (PowerSeries R)ˣ) (a b : F.completion) :
    F.completedTwistedSeriesAction x (c * d) H (a * b) =
      F.completedTwistedSeriesAction (d • x) c H a *
        F.completedTwistedSeriesAction x d H b := by
  simp only [completedTwistedSeriesAction_apply, completedAeval_smul,
    PowerSeries.rescale_rescale]
  have hi :
      F.completedAeval x (PowerSeries.rescale d (↑(H⁻¹) : PowerSeries R)) *
        F.completedAeval x (PowerSeries.rescale d (H : PowerSeries R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  simp only [mul_assoc, ← mul_assoc
    (F.completedAeval x (PowerSeries.rescale d (↑(H⁻¹) : PowerSeries R))), hi, one_mul]

variable {S B : Type*} [CommRing S] [Ring B] [Algebra S B]
  (G : AlgFiltration B) (φ : R →+* S) (ψ : A →+* B)
  (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r))
  (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap ψ)
  (h₁ : F.ideal 1 ≤ (G.ideal 1).comap ψ)

include hψ in
/-- Scalar and coefficient transport intertwines the twisted series action. -/
theorem mapCompletion_completedTwistedSeriesAction (x : F.completionIdeal 1) (c : R)
    (H : (PowerSeries R)ˣ) (a : F.completion) :
    F.mapCompletion G ψ l hl hf (F.completedTwistedSeriesAction x c H a) =
      G.completedTwistedSeriesAction
        ⟨F.mapCompletion G ψ l hl hf x,
          F.mapCompletion_mem_first G ψ l hl hf h₁ x.property⟩ (φ c)
        (Units.map (PowerSeries.map φ).toMonoidHom H) (F.mapCompletion G ψ l hl hf a) := by
  simp only [completedTwistedSeriesAction_apply, map_mul, Units.coe_map, Units.coe_map_inv,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [F.mapCompletion_completedAeval G φ ψ hψ l hl hf h₁,
    F.mapCompletion_completedAeval G φ ψ hψ l hl hf h₁, PowerSeries.rescale_map]

include hψ in
/-- The same transport intertwines the inverse twisted action. -/
theorem mapCompletion_completedTwistedSeriesAction_symm (x : F.completionIdeal 1) (c : R)
    (H : (PowerSeries R)ˣ) (a : F.completion) :
    F.mapCompletion G ψ l hl hf ((F.completedTwistedSeriesAction x c H).symm a) =
      (G.completedTwistedSeriesAction
        ⟨F.mapCompletion G ψ l hl hf x,
          F.mapCompletion_mem_first G ψ l hl hf h₁ x.property⟩ (φ c)
        (Units.map (PowerSeries.map φ).toMonoidHom H)).symm
        (F.mapCompletion G ψ l hl hf a) := by
  have he := F.mapCompletion_completedTwistedSeriesAction G φ ψ hψ l hl hf h₁ x c (H⁻¹) a
  rw [completedTwistedSeriesAction_inv, map_inv, completedTwistedSeriesAction_inv] at he
  exact he

/-- Twisted completed-series transport allows prescribed argument and rescaling images. -/
theorem mapCompletion_completedTwistedSeriesAction_of_eq
    {R S A B : Type*} [CommRing R] [CommRing S] [Ring A] [Ring B]
    [Algebra R A] [Algebra S B] (F : AlgFiltration A) (G : AlgFiltration B)
    (φ : R →+* S) (ψ : A →+* B)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r))
    (l : ℕ → ℕ) (hl : Monotone l)
    (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap ψ)
    (h₁ : F.ideal 1 ≤ (G.ideal 1).comap ψ)
    (x : F.completionIdeal 1) (y : G.completionIdeal 1)
    (hy : F.mapCompletion G ψ l hl hf x = y)
    (c : R) (d : S) (hc : φ c = d) (H : (PowerSeries R)ˣ) (a : F.completion) :
    F.mapCompletion G ψ l hl hf (F.completedTwistedSeriesAction x c H a) =
      G.completedTwistedSeriesAction y d (Units.map (PowerSeries.map φ).toMonoidHom H)
        (F.mapCompletion G ψ l hl hf a) := by
  have he := F.mapCompletion_completedTwistedSeriesAction G φ ψ hψ l hl hf h₁ x c H a
  have hy' : (⟨F.mapCompletion G ψ l hl hf x,
    F.mapCompletion_mem_first G ψ l hl hf h₁ x.property⟩ : G.completionIdeal 1) = y :=
    Subtype.ext hy
  rw [hy', hc] at he
  exact he

end Mei.AlgFiltration
