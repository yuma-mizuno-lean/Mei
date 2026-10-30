/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Evaluation

/-!
# Shearing the decorated focus-focus ray fibers

At an upper encounter, the actual developed ray is the lower branch with its
incoming segment sheared and its terminal segment unchanged
(`SlabBrokenLine.ray_eq_piecewise_shear`). The shear is `(u,v) ↦ (u,v-u)`
for incoming `X` powers and its inverse for incoming `Y` powers.

A uniform integral shear `(u,v) ↦ (u,v+r*u)` of developed coordinates transports
an incoming exponent `(n,b)`
to `(n,b+r*n)`. It fixes the slab pointwise, preserves every crossing height,
and gives a bijection of the actual decorated crossing rays. The choices `r=-1`
and `r=1` give the two linear coordinate changes above. No genericity is needed:
branches through the singular origin are omitted on both sides.

We transport whole nonzero homogeneous decorations. Decorations killed by
binomial arithmetic or the smoothing parameter are omitted on both sides and
contribute zero. Normal Laurent exponents use
`-|n|` on the outgoing side, so at fixed spatial horizontal exponent `n` the
coefficient comparison is translation of the tangential exponent by `r*n`.
The finite weighted sums commute with that linear translation. Incoming rays
and the stationary sector obey the same formula.

The construction reuses `slabBrokenLineEquiv`, `FiniteAffineRay.map`, Mathlib's
`LinearEquiv.skewProd` and `AddMonoidAlgebra.mapDomainLinearMap`. The coordinate conventions follow
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties
with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra

private abbrev planeShear (r : ℤ) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.refl ℝ ℝ).skewProd (LinearEquiv.refl ℝ ℝ) ((r : ℝ) • LinearMap.id)

private theorem crossingHeight_shear (r n q : ℤ) (Q : ℝ × ℝ) (hn : n ≠ 0) :
    (Q.2 + r * Q.1) - ((q + r * n : ℤ) : ℝ) * Q.1 / n =
      Q.2 - (q : ℝ) * Q.1 / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp
  ring

private theorem incomingExponent_shear (r n b q : ℤ) (Q : ℝ × ℝ) (hn : n ≠ 0)
    (hheight : Q.2 - (q : ℝ) * Q.1 / n ≠ 0) :
    slabIncomingExponent n (b + r * n) (q + r * n) (Q.1, Q.2 + r * Q.1) =
      slabIncomingExponent n b q Q + r * n := by
  by_cases hneg : Q.2 - (q : ℝ) * Q.1 / n < 0
  · rw [slabIncomingExponent_of_neg _ _ _ _
      (by simpa only [crossingHeight_shear r n q Q hn] using hneg),
      slabIncomingExponent_of_neg _ _ _ _ hneg]
  · have hpos := lt_of_le_of_ne (le_of_not_gt hneg) hheight.symm
    rw [slabIncomingExponent_of_pos _ _ _ _
      (by simpa only [crossingHeight_shear r n q Q hn] using hpos),
      slabIncomingExponent_of_pos _ _ _ _ hpos]
    omega

variable {R : Type*} [CommRing R] {t c : R} {n b : ℤ} {Q : ℝ × ℝ}

namespace SlabBrokenLine

/-- Apply an integral shear to a decorated crossing ray. The same binomial index
survives, with its tangential exponent shifted by `r*n`. -/
def shear (β : SlabBrokenLine t c n b Q) (r : ℤ) :
    SlabBrokenLine t c n (b + r * n) (Q.1, Q.2 + r * Q.1) where
  degree := (β.degree.1, β.degree.2 + r * n)
  ray := β.ray.map (planeShear r).toAffineMap
  opposite := β.opposite
  transfer_ne_zero := by
    obtain ⟨j, hj, he, hc⟩ :=
      (Mei.NodeAlgebra.exponentCorrespondence_transfer_ne_zero_iff
        t c n.natAbs b 1 (by decide) β.degree).mp β.transfer_ne_zero
    apply (Mei.NodeAlgebra.exponentCorrespondence_transfer_ne_zero_iff
      t c n.natAbs (b + r * n) 1 (by decide) _).mpr
    refine ⟨j, hj, ?_, hc⟩
    simp only [mul_one] at he ⊢
    rw [he]
    congr 1
    omega
  endpoint_eq := by simp [β.endpoint_eq, planeShear]
  direction_eq := by simp [β.direction_eq, planeShear]
  incomingDirection_eq := by
    have hn : n ≠ 0 := by
      intro hn
      have h := β.opposite
      simp [hn] at h
    simp only [FiniteAffineRay.incomingDirection_map, β.incomingDirection_eq,
      incomingExponent_shear r n b β.degree.2 Q hn
        β.snd_sub_mul_fst_div_ne_zero]
    simp [planeShear]
  vertical_bends := by
    intro s hs
    have hb := β.vertical_bends s (β.ray.support_bends_map_subset _ hs)
    simpa [planeShear] using hb
  slab_bends := by
    intro s hs
    have hb := β.slab_bends s (β.ray.support_bends_map_subset _ hs)
    simpa [planeShear] using hb
  avoids_origin := by
    intro s hs he
    apply β.avoids_origin s hs
    have he' : planeShear r (β.ray s) = planeShear r 0 := by
      simpa using he
    exact (planeShear r).injective he'

/-- The spatial shear retains the normal Laurent degree and shifts the
outgoing tangential exponent by `r*n`. -/
@[simp]
theorem degree_shear (β : SlabBrokenLine t c n b Q) (r : ℤ) :
    (β.shear r).degree = (β.degree.1, β.degree.2 + r * n) := (rfl)

/-- The entire geometric realization, including the incoming tail, is the
linear image of the original ray. Encounter times are unchanged. -/
@[simp]
theorem ray_shear (β : SlabBrokenLine t c n b Q) (r : ℤ) :
    (β.shear r).ray = β.ray.map
      ((LinearEquiv.refl ℝ ℝ).skewProd (LinearEquiv.refl ℝ ℝ)
        ((r : ℝ) • LinearMap.id)).toAffineMap := (rfl)

/-- Whole decorations are translated in the tangential Laurent exponent.
This is a linear coefficient comparison on the fixed horizontal sector. -/
@[simp]
theorem decoration_shear (β : SlabBrokenLine t c n b Q) (r : ℤ) :
    (β.shear r).decoration =
      mapDomainLinearMap R R (fun q : ℤ × ℤ => (q.1, q.2 + r * n)) β.decoration := by
  obtain ⟨j, _, he, _⟩ :=
    (Mei.NodeAlgebra.exponentCorrespondence_transfer_ne_zero_iff
      t c n.natAbs b 1 (by decide) β.degree).mp β.transfer_ne_zero
  simp only [mul_one] at he
  rw [decoration_def, degree_shear, he, decoration_def, he]
  have hindex : b + (j : ℤ) + r * n = b + r * n + j := by omega
  have hl := Mei.NodeAlgebra.exponentCorrespondence_transfer_binomial
    t c n.natAbs (b + r * n) 1 (by decide) j
  have hr := Mei.NodeAlgebra.exponentCorrespondence_transfer_binomial
    t c n.natAbs b 1 (by decide) j
  rw [mul_one] at hl hr
  dsimp only [Prod.fst, Prod.snd]
  rw [hindex, hl, hr, mapDomainLinearMap_single]
  congr 1
  exact Prod.ext rfl hindex.symm

/-- At an upper encounter the actual developed path differs from the lower
branch only on the incoming segment. For negative horizontal degree this is the
upper shear `(u,v) ↦ (u,v-u)`; for positive degree it is its inverse. Both maps
fix the crossing point, and the terminal segment is unchanged. -/
theorem ray_eq_piecewise_shear (β : SlabBrokenLine t c n b Q)
    (hupper : 0 < Q.2 - (β.degree.2 : ℝ) * Q.1 / n) (s : ℝ) :
    β.ray s =
      let L := slabBranch n b β.degree.2 Q β.opposite s
      if s ≤ Q.1 / (n : ℝ) then
        (L.1, L.2 + (n.natAbs : ℝ) / n * L.1) else L := by
  rw [β.ray_eq_slabBranch, slabIncomingExponent_of_pos _ _ _ _ hupper]
  dsimp only
  split_ifs with hs
  · rw [slabBranch_apply_of_le _ _ _ _ _ hs, slabBranch_apply_of_le _ _ _ _ _ hs]
    have hn : (n : ℝ) ≠ 0 := (div_ne_zero_iff.mp β.opposite.ne).2
    apply Prod.ext
    · rfl
    · dsimp
      simp only [Int.cast_add, Int.cast_natCast]
      field_simp
      ring
  · rw [slabBranch_apply_of_ge _ _ _ _ _ (le_of_not_ge hs),
      slabBranch_apply_of_ge _ _ _ _ _ (le_of_not_ge hs)]

/-- Shearing gives a bijection of the actual evaluation fibers, with no
nonvanishing or endpoint-genericity hypotheses. -/
def shearEquiv (r : ℤ) :
    SlabBrokenLine t c n b Q ≃
      SlabBrokenLine t c n (b + r * n) (Q.1, Q.2 + r * Q.1) :=
  Equiv.ofBijective (fun β => β.shear r) ⟨by
    intro β γ h
    apply SlabBrokenLine.ext
    have he := congrArg SlabBrokenLine.degree h
    simpa only [degree_shear, Prod.mk.injEq, add_left_inj, Prod.ext_iff] using he, by
    intro γ
    have hQ : Q.1 / (n : ℝ) < 0 := γ.opposite
    let j := (slabBrokenLineEquiv t c n (b + r * n) (Q.1, Q.2 + r * Q.1) hQ).symm γ
    have hn : n ≠ 0 := by
      intro hn
      simp [hn] at hQ
    have hj : Q.2 - ((b + j.val.val : ℤ) : ℝ) * Q.1 / n ≠ 0 := by
      have hh := j.property.2
      have he : b + r * n + j.val.val = (b + j.val.val) + r * n := by omega
      rw [he, crossingHeight_shear r n (b + j.val.val) Q hn] at hh
      exact hh
    let β := slabBrokenLine t c n b Q hQ ⟨j.val, j.property.1, hj⟩
    refine ⟨β, SlabBrokenLine.ext ?_⟩
    have he := (slabBrokenLineEquiv t c n (b + r * n) (Q.1, Q.2 + r * Q.1) hQ).apply_symm_apply γ
    rw [slabBrokenLineEquiv_apply] at he
    have hd := congrArg SlabBrokenLine.degree he
    rw [degree_slabBrokenLine] at hd
    rw [degree_shear]
    dsimp only [β]
    rw [degree_slabBrokenLine, ← hd]
    dsimp only [j]
    congr 1
    omega⟩

/-- The forward fiber equivalence is the geometric shear. -/
@[simp]
theorem shearEquiv_apply (r : ℤ) (β : SlabBrokenLine t c n b Q) :
    shearEquiv (t := t) (c := c) (n := n) (b := b) (Q := Q) r β = β.shear r := (rfl)

/-- The inverse fiber comparison recovers the unsheared outgoing degree. -/
@[simp]
theorem degree_shearEquiv_symm (r : ℤ)
    (γ : SlabBrokenLine t c n (b + r * n) (Q.1, Q.2 + r * Q.1)) :
    ((shearEquiv (t := t) (c := c) (n := n) (b := b) (Q := Q) r).symm γ).degree =
      (γ.degree.1, γ.degree.2 - r * n) := by
  have he := congrArg SlabBrokenLine.degree
    ((shearEquiv (t := t) (c := c) (n := n) (b := b) (Q := Q) r).apply_symm_apply γ)
  simp only [shearEquiv_apply, degree_shear] at he
  have hf := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  exact Prod.ext hf (by dsimp at hs; omega)

/-- The inverse equivalence unshears the entire path, including its incoming tail. -/
@[simp]
theorem shearEquiv_symm_apply_ray (r : ℤ)
    (γ : SlabBrokenLine t c n (b + r * n) (Q.1, Q.2 + r * Q.1)) (s : ℝ) :
    ((shearEquiv (t := t) (c := c) (n := n) (b := b) (Q := Q) r).symm γ).ray s =
      ((γ.ray s).1, (γ.ray s).2 - r * (γ.ray s).1) := by
  have he := congrArg (fun β => β.ray s)
    ((shearEquiv (t := t) (c := c) (n := n) (b := b) (Q := Q) r).apply_symm_apply γ)
  simp only [shearEquiv_apply, ray_shear, FiniteAffineRay.map_apply] at he
  simp only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe, LinearEquiv.skewProd_apply,
    LinearEquiv.refl_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul] at he
  have hf := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  dsimp only [Prod.fst, Prod.snd] at hf hs
  apply Prod.ext
  · exact hf
  · dsimp only [Prod.snd]
    rw [← hf]
    linarith

end SlabBrokenLine

/-- The finite crossing sum commutes with the integral shear even at exceptional
endpoints. Singular branches are absent from both evaluation fibers. -/
theorem slabWeightedEvaluation_shear (t c : R) (n b r : ℤ) (Q : ℝ × ℝ) :
    slabWeightedEvaluation t c n (b + r * n) (Q.1, Q.2 + r * Q.1) =
      mapDomainLinearMap R R (fun q : ℤ × ℤ => (q.1, q.2 + r * n))
        (slabWeightedEvaluation t c n b Q) := by
  classical
  rw [slabWeightedEvaluation_def, slabWeightedEvaluation_def, _root_.map_sum]
  exact (Fintype.sum_equiv
    (SlabBrokenLine.shearEquiv (t := t) (c := c) (n := n) (b := b) (Q := Q) r) _ _
      (fun β => by simp)).symm

namespace IncomingSlabBrokenLine

variable {S : Type*} [Zero S] {c : S}

/-- The same shear transports the actual incoming-ray fibers. This includes
invariant vertical rays; zero coefficients and zero direction give empty fibers. -/
def shearEquiv (r : ℤ) :
    IncomingSlabBrokenLine c n b Q ≃
      IncomingSlabBrokenLine c n (b + r * n) (Q.1, Q.2 + r * Q.1) := by
  have hv : (n, b + r * n) ≠ (0 : ℤ × ℤ) ↔ (n, b) ≠ 0 := by
    simp only [ne_eq, Prod.mk_eq_zero, not_and_or]
    by_cases hn : n = 0 <;> simp [hn]
  exact equivOfSubsingletonOfSubsingleton
    (fun β => incomingSlabBrokenLine c n (b + r * n) _ β.coefficient_ne_zero
      (hv.mpr β.exponent_ne_zero) β.off_slab β.incoming_side)
    (fun γ => incomingSlabBrokenLine c n b Q γ.coefficient_ne_zero
      (hv.mp γ.exponent_ne_zero) γ.off_slab γ.incoming_side)

/-- The incoming-ray comparison shears every point of its affine tail. -/
theorem shearEquiv_apply_ray (r : ℤ) (β : IncomingSlabBrokenLine c n b Q) (s : ℝ) :
    (shearEquiv (c := c) (n := n) (b := b) (Q := Q) r β).ray s =
      ((β.ray s).1, (β.ray s).2 + r * (β.ray s).1) := by
  simp only [ray_eq_straight, FiniteAffineRay.straight_apply]
  apply Prod.ext <;> simp [smul_eq_mul]; ring

/-- The inverse comparison also recovers the complete incoming affine tail. -/
theorem shearEquiv_symm_apply_ray (r : ℤ)
    (γ : IncomingSlabBrokenLine c n (b + r * n) (Q.1, Q.2 + r * Q.1)) (s : ℝ) :
    ((shearEquiv (c := c) (n := n) (b := b) (Q := Q) r).symm γ).ray s =
      ((γ.ray s).1, (γ.ray s).2 - r * (γ.ray s).1) := by
  simp only [ray_eq_straight, FiniteAffineRay.straight_apply]
  apply Prod.ext <;> simp [smul_eq_mul]; ring

end IncomingSlabBrokenLine

/-- Incoming weighted sums obey the same exponent translation, including invariant
vertical rays. Zero spatial degree has empty ray fibers and contributes zero here;
its constant section occurs only in `slabThetaEvaluation`. -/
theorem incomingSlabWeightedEvaluation_shear {S : Type*} [Semiring S]
    (c : S) (n b r : ℤ) (Q : ℝ × ℝ) :
    incomingSlabWeightedEvaluation c n (b + r * n) (Q.1, Q.2 + r * Q.1) =
      mapDomainLinearMap S S (fun q : ℤ × ℤ => (q.1, q.2 + r * n))
        (incomingSlabWeightedEvaluation c n b Q) := by
  classical
  have hv : (n, b + r * n) ≠ (0 : ℤ × ℤ) ↔ (n, b) ≠ 0 := by
    simp only [ne_eq, Prod.mk_eq_zero, not_and_or]
    by_cases hn : n = 0 <;> simp [hn]
  simp only [incomingSlabWeightedEvaluation_eq, hv]
  split_ifs <;> simp

/-- Full weighted evaluation commutes with the shear: incoming rays, crossing
rays, and the constant incoming section all transform together. No endpoint
exception beyond the existing ray definitions is imposed. -/
theorem slabThetaEvaluation_shear (t c : R) (n b r : ℤ) (Q : ℝ × ℝ) :
    slabThetaEvaluation t c n (b + r * n) (Q.1, Q.2 + r * Q.1) =
      mapDomainLinearMap R R (fun q : ℤ × ℤ => (q.1, q.2 + r * n))
        (slabThetaEvaluation t c n b Q) := by
  classical
  rw [slabThetaEvaluation_def, slabThetaEvaluation_def,
    incomingSlabWeightedEvaluation_shear, slabWeightedEvaluation_shear]
  simp only [map_add]
  congr 1
  by_cases hn : n = 0
  · simp only [hn, mul_zero, add_zero]
    split_ifs <;> simp
  · have hv : ∀ a : ℤ, (n, a) ≠ (0 : ℤ × ℤ) := by simp [hn]
    simp [hv]

end Mei.FocusFocus
