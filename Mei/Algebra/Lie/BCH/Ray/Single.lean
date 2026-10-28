/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Basic

/-!
# Ray groups supported in one homogeneous degree

If all pieces on a supported ray except one degree vanish, its completed BCH
subgroup is the additive group of the single piece. In particular completion
introduces no further coefficients on such a ray. This applies to charge-one
rays in semidirect Lie algebras with an abelian coefficient ideal.

The construction uses `logComponent`, `log_projection_eq_mkQ_sum` and the
existing completed ray subgroup. Its group law follows from the graded bracket:
the bracket of two homogeneous coefficients lies in the vanishing doubled piece.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommGroup N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (w : SupportedRay d) (n : N) (hn : n ∈ w.rayDegrees)
  (hvan : ∀ m ∈ w.rayDegrees, m ≠ n → ℒ m = ⊥)

include hn hvan

/-- A label on a ray with only one homogeneous piece is the exponential of its
coefficient in that degree. -/
theorem expToCompletion_logComponent_eq_of_ray_single
    {g : d.completedBCHGroup ℒ} (hg : g ∈ d.completedRaySubgroup ℒ w) :
    d.expToCompletion ℒ (d.logComponent ℒ g n) = g := by
  have hz (m : N) (hm : m ≠ n) : d.logComponent ℒ g m = 0 := by
    by_cases hray : m ∈ w.rayDegrees
    · apply Subtype.ext
      exact (Submodule.eq_bot_iff _).mp (hvan m hray hm) _
        (d.logComponent ℒ g m).property
    · exact d.logComponent_eq_zero_of_notMem_rayDegrees ℒ hg hray
  apply CompletedGroup.ext
  intro k
  apply BCHGroup.log_injective (L := d.truncatedLie ℒ k)
  rw [projection_expToCompletion, BCHGroup.log_exp, log_projection_eq_mkQ_sum]
  by_cases hk : d.degree n ≤ k
  · congr 1
    exact (Finset.sum_eq_single_of_mem (f := fun n => (d.logComponent ℒ g n : L)) n
      ((d.finite_cutoff k).mem_toFinset.mpr (d.mem_cutoff.mpr ⟨w.rayDegrees_subset hn, hk⟩))
      (fun m _ hm => by rw [hz m hm, ZeroMemClass.coe_zero])).symm
  · rw [(d.degreeIdeal ℒ k).mkQ_eq_zero.mpr
      (d.le_degreeIdeal ℒ (lt_of_not_ge hk) (d.logComponent ℒ g n).property)]
    rw [Finset.sum_eq_zero (fun m hm => by
      have hne : m ≠ n := by
        intro he
        subst m
        exact hk ((d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp hm)).2)
      rw [hz m hne, ZeroMemClass.coe_zero]), map_zero]

/-- Exponentiation identifies the additive homogeneous piece with the whole
completed subgroup of a ray having no other homogeneous pieces. -/
def completedRaySingleEquiv :
    Multiplicative (ℒ n) ≃* d.completedRaySubgroup ℒ w where
  toFun x := ⟨d.expToCompletion ℒ x.toAdd,
    d.expToCompletion_mem_completedRaySubgroup ℒ
      (le_rayLieSubalgebra ℒ hn x.toAdd.property)⟩
  invFun g := Multiplicative.ofAdd (d.logComponent ℒ g.val n)
  left_inv x := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    rw [logComponent_expToCompletion]
    exact DirectSum.decompose_of_mem_same ℒ x.toAdd.property
  right_inv g := Subtype.ext (d.expToCompletion_logComponent_eq_of_ray_single ℒ w n hn hvan
    g.property)
  map_mul' x y := by
    apply Subtype.ext
    -- Expose subgroup coercions and multiplication of the additive type tag.
    change d.expToCompletion ℒ ((x.toAdd : L) + (y.toAdd : L)) =
      d.expToCompletion ℒ x.toAdd * d.expToCompletion ℒ y.toAdd
    apply CompletedGroup.ext
    intro k
    rw [map_mul, projection_expToCompletion, projection_expToCompletion,
      projection_expToCompletion, map_add]
    apply BCHGroup.exp_add_of_lie_eq_zero
    rw [← LieHom.map_lie]
    have hne : n + n ≠ n := by
      intro h
      exact (SupportedRay.ne_zero_of_mem_rayDegrees hn)
        (add_left_cancel (h.trans (add_zero n).symm))
    have hmem := SetLike.GradedBracket.bracket_mem x.toAdd.property y.toAdd.property
    simp only [vadd_eq_add] at hmem
    rw [hvan _ (SupportedRay.add_mem_rayDegrees hn hn) hne, Submodule.mem_bot] at hmem
    rw [hmem, map_zero]

/-- The forward equivalence is the original completed exponential. -/
@[simp]
theorem coe_completedRaySingleEquiv (x : Multiplicative (ℒ n)) :
    (d.completedRaySingleEquiv ℒ w n hn hvan x : d.completedBCHGroup ℒ) =
      d.expToCompletion ℒ x.toAdd := (rfl)

/-- The inverse equivalence extracts the distinguished coefficient. -/
@[simp]
theorem completedRaySingleEquiv_symm_apply (g : d.completedRaySubgroup ℒ w) :
    (d.completedRaySingleEquiv ℒ w n hn hvan).symm g =
      Multiplicative.ofAdd (d.logComponent ℒ g.val n) := (rfl)

end Mei.PositiveDegrees
