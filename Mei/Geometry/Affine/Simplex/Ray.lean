/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Exit points of rays in simplices

A nonzero ray from an interior point of a simplex, in its affine direction,
exits through an opposite face at a positive parameter. The parameters for
which the ray belongs to the simplex form exactly the closed interval from
zero to this exit parameter. These exit points supply the parameter-face
intersections used by transverse simplex tests.

The construction uses Mathlib's affine-combination coordinates and follows the
minimum-ratio argument in Mathlib’s `Caratheodory.mem_convexHull_erase`
(Johan Commelin and Kim Morrison): increase the ray
parameter until the first barycentric weight becomes zero. Affine independence
identifies the weights of every later point on the ray.
-/

public section

open Set Finset

namespace Affine.Simplex

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] {n : ℕ}

/-- A ray from an interior point in a nonzero tangent direction exits the
simplex at a positive parameter on an opposite face. Its nonnegative parameters
inside the simplex are exactly those at most the exit parameter. -/
theorem exists_pos_ray_mem_face (s : Simplex K V (n + 1)) {p v : V}
    (hp : p ∈ s.interior) (hv : v ∈ vectorSpan K (range s.points)) (hv0 : v ≠ 0) :
    ∃ t : K, 0 < t ∧ ∃ j : Fin (n + 2),
      p + t • v ∈ (s.faceOpposite j).closedInterior ∧
      ∀ a : K, 0 ≤ a → (p + a • v ∈ s.closedInterior ↔ a ≤ t) := by
  classical
  -- Express the velocity as a zero-sum variation of barycentric weights.
  have hpA := s.closedInterior_subset_affineSpan (s.interior_subset_closedInterior hp)
  obtain ⟨b, hb1, hb, hbp⟩ := hp
  have hyA : p + v ∈ affineSpan K (range s.points) := by
    simpa only [vadd_eq_add, add_comm] using
      (affineSpan K (range s.points)).vadd_mem_of_mem_direction
        (by simpa only [direction_affineSpan] using hv) hpA
  obtain ⟨c, hc1, hcpv⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hyA
  let d : Fin (n + 2) → K := c - b
  have hd1 : ∑ j, d j = 0 := by simp [d, sum_sub_distrib, hb1, hc1]
  have hdn : ∃ j ∈ (Finset.univ : Finset (Fin (n + 2))), d j ≠ 0 := by
    by_contra! hz
    have hcb : c = b := funext fun j => sub_eq_zero.mp (hz j (mem_univ j))
    have heq : p = p + v := hbp.symm.trans (hcb ▸ hcpv.symm)
    exact hv0 (add_left_cancel (heq.symm.trans (add_zero p).symm))
  obtain ⟨j₀, _, hj₀⟩ := exists_neg_of_sum_zero_of_exists_nonzero d hd1 hdn
  -- The first weight to vanish determines the last permissible ray parameter.
  let S : Finset (Fin (n + 2)) := univ.filter fun j => d j < 0
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image (fun j => b j / (-d j))
    ⟨j₀, mem_filter.mpr ⟨mem_univ _, hj₀⟩⟩
  have hdj : d j < 0 := (mem_filter.mp hj).2
  let t := b j / (-d j)
  have ht : 0 < t := div_pos (hb j).1 (neg_pos.mpr hdj)
  let w : K → Fin (n + 2) → K := fun a i => b i + a * d i
  have hw1 (a : K) : ∑ i, w a i = 1 := by
    simp only [w, sum_add_distrib, ← mul_sum, hb1, hd1, mul_zero, add_zero]
  have hweights (a : K) (ha : 0 ≤ a) : (∀ i, 0 ≤ w a i) ↔ a ≤ t := by
    constructor
    · intro h
      have hle := h j
      have htj : t * (-d j) = b j := div_mul_cancel₀ _ (neg_ne_zero.mpr hdj.ne)
      have hdpos : 0 < -d j := neg_pos.mpr hdj
      apply (mul_le_mul_iff_right₀ hdpos).mp
      dsimp only [w] at hle
      nlinarith
    · intro hat i
      by_cases hdi : d i < 0
      · have hti : t ≤ b i / (-d i) := hmin i (mem_filter.mpr ⟨mem_univ _, hdi⟩)
        have hbound := (le_div_iff₀ (neg_pos.mpr hdi)).mp (hat.trans hti)
        dsimp only [w]
        nlinarith
      · exact add_nonneg (hb i).1.le (mul_nonneg ha (le_of_not_gt hdi))
  have hwj : w t j = 0 := by
    dsimp only [w, t]
    field_simp [hdj.ne]
    ring
  -- The affine combinations follow the actual ray in the ambient module.
  have hwp (a : K) : univ.affineCombination K s.points (w a) = p + a • v := by
    rw [affineCombination_eq_linear_combination _ _ _ (hw1 a)]
    have hbpsum := hbp
    rw [affineCombination_eq_linear_combination _ _ _ hb1] at hbpsum
    have hcpsum := hcpv.symm
    rw [affineCombination_eq_linear_combination _ _ _ hc1] at hcpsum
    simp only [w, d, Pi.sub_apply, add_smul, mul_smul, sub_smul,
      sum_add_distrib, sum_sub_distrib, ← smul_sum]
    rw [hbpsum, hcpsum]
    module
  refine ⟨t, ht, j, ?_, ?_⟩
  · rw [← hwp t, faceOpposite, affineCombination_mem_closedInterior_face_iff_nonneg s _ (hw1 t)]
    exact ⟨fun i _ => (hweights t ht.le).mpr le_rfl i, by simpa using hwj⟩
  · intro a ha
    rw [← hwp a, affineCombination_mem_closedInterior_iff (hw1 a)]
    constructor
    · exact fun h => (hweights a ha).mp fun i => (h i).1
    · intro hat i
      have hn := (hweights a ha).mpr hat
      exact ⟨hn i, by
        rw [← hw1 a]
        exact single_le_sum (fun k _ => hn k) (mem_univ i)⟩

/-- If a ray through an interior point of a triangle misses all vertices,
its exit lies on exactly one edge. This is the vertex-avoidance
condition on transverse triangular meridians. -/
theorem exists_pos_ray_mem_unique_face (s : Triangle K V) {p v : V}
    (hp : p ∈ s.interior) (hv : v ∈ vectorSpan K (range s.points)) (hv0 : v ≠ 0)
    (hmiss : ∀ a : K, 0 < a → ∀ i, p + a • v ≠ s.points i) :
    ∃ t : K, 0 < t ∧
      (∃! j : Fin 3, p + t • v ∈ (s.faceOpposite j).closedInterior) ∧
      ∀ a : K, 0 ≤ a → (p + a • v ∈ s.closedInterior ↔ a ≤ t) := by
  obtain ⟨t, ht, j, hj, hparam⟩ := s.exists_pos_ray_mem_face hp hv hv0
  refine ⟨t, ht, ⟨j, hj, ?_⟩, hparam⟩
  intro m hm
  by_contra hne
  obtain ⟨k, hkj, hkm⟩ := Fin.exists_ne_and_ne_of_two_lt j m (by decide)
  have hset : ({j}ᶜ ∩ {m}ᶜ : Set (Fin 3)) = {k} := by
    ext a
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff]
    constructor
    · intro ha
      omega
    · rintro rfl
      exact ⟨hkj, hkm⟩
  have hqA : p + t • v ∈ affineSpan K (s.points '' ({j}ᶜ ∩ {m}ᶜ)) := by
    rw [← s.independent.inf_affineSpan_eq_affineSpan_inter]
    constructor
    · simpa only [range_faceOpposite_points] using
        (s.faceOpposite j).closedInterior_subset_affineSpan hj
    · simpa only [range_faceOpposite_points] using
        (s.faceOpposite m).closedInterior_subset_affineSpan hm
  have hq : p + t • v = s.points k := by
    simpa only [hset, image_singleton, AffineSubspace.mem_affineSpan_singleton] using hqA
  exact hmiss t ht k hq

end Affine.Simplex
