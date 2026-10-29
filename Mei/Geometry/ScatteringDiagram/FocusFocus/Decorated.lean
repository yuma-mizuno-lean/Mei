/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Exhaustion
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Transfer

/-!
# Decorated crossing rays for the focus-focus slab

We identify the evaluation fiber of decorated transverse slab rays with the
surviving binomial indices whose crossing heights are nonzero. The geometric
conditions require all bends to lie on the slab, preservation of the horizontal
velocity, and avoidance of the singular origin. They do not assume a bound on
the number of encounters. The entire nonzero homogeneous transfer determines
the outgoing decoration. Consequently endpoint and outgoing degree determine
the ray, and every evaluation fiber is finite.

The signed spatial exponent `n` treats incoming `X` (`n < 0`) and `Y` (`n > 0`)
uniformly. The normal Laurent exponent in the incoming chamber is `|n|`,
and in the outgoing chamber it is `-|n|`. The two slab transfers have the same
formula; the spatial horizontal exponent remains `n`. Development uses incoming
vertical exponent `b` below the origin and `b+|n|` above it; the upper transfer
has the same decoration by binomial reflection. At endpoints avoiding
all binomial crossing-height hyperplanes, the sum of the final decorations is
exactly the image of the incoming lift in the opposite Laurent chamber.

The slab interpretation is that of
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, §3 (arXiv:1601.07081v4).
The central formal references are `eq_slabBranch` and `slabTransferEquiv`.
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra

variable {R : Type*} [CommRing R] (t c : R) (n b : ℤ) (Q : ℝ × ℝ)

/-- The incoming tangential exponent after developing into the outgoing chart.
Below the origin the transition is the identity. Above it the shear adds `|n|`
for either crossing direction. Height zero has no nonsingular crossing ray. -/
def slabIncomingExponent (n b q : ℤ) (Q : ℝ × ℝ) : ℤ :=
  if Q.2 - (q : ℝ) * Q.1 / n < 0 then b else b + n.natAbs

@[simp]
theorem slabIncomingExponent_of_neg (n b q : ℤ) (Q : ℝ × ℝ)
    (h : Q.2 - (q : ℝ) * Q.1 / n < 0) : slabIncomingExponent n b q Q = b := by
  simp [slabIncomingExponent, h]

@[simp]
theorem slabIncomingExponent_of_pos (n b q : ℤ) (Q : ℝ × ℝ)
    (h : 0 < Q.2 - (q : ℝ) * Q.1 / n) :
    slabIncomingExponent n b q Q = b + n.natAbs := by
  simp [slabIncomingExponent, not_lt_of_ge h.le]

/-- A decorated ray crossing the slab in a developed chart. Its output degree
selects the entire homogeneous transfer, including its scalar coefficient.
Only local bend conditions are imposed on the underlying finite affine ray. -/
structure SlabBrokenLine where
  /-- The normal and tangential exponents in the outgoing Laurent chamber. -/
  degree : ℤ × ℤ
  /-- The continuous finitely bent geometric realization. -/
  ray : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)
  /-- The endpoint is in the chamber opposite the incoming direction. -/
  opposite : Q.1 / (n : ℝ) < 0
  /-- The selected transfer is a whole nonzero homogeneous component. -/
  transfer_ne_zero :
    (exponentCorrespondence (single 0 t + single 1 t)).transfer
      ⟨((n.natAbs : ℤ), b), by simp⟩ degree
      ⟨single (n.natAbs, b) c, single_mem_grade _ _⟩ ≠ 0
  /-- The realized endpoint is the evaluation point. -/
  endpoint_eq : ray.endpoint = Q
  /-- The outgoing decoration determines the terminal spatial direction. -/
  direction_eq : ray.direction = ((n : ℝ), (degree.2 : ℝ))
  /-- The incoming monomial is developed using the lower or upper chart transition. -/
  incomingDirection_eq : ray.incomingDirection =
    ((n : ℝ), (slabIncomingExponent n b degree.2 Q : ℝ))
  /-- Crossing the slab preserves the horizontal direction. -/
  vertical_bends : ∀ s ∈ ray.bends.support, (ray.bends s).1 = 0
  /-- Bends occur only at encounters with the slab. -/
  slab_bends : ∀ s ∈ ray.bends.support, (ray s).1 = 0
  /-- The incoming half-line stays in the nonsingular base. -/
  avoids_origin : ∀ s ≤ 0, ray s ≠ 0

namespace SlabBrokenLine

variable {t c n b Q}

/-- The local bend and propagation conditions force the explicit one-crossing ray. -/
theorem ray_eq_slabBranch (β : SlabBrokenLine t c n b Q) :
    β.ray = slabBranch n (slabIncomingExponent n b β.degree.2 Q) β.degree.2 Q β.opposite :=
  eq_slabBranch β.ray β.vertical_bends β.slab_bends n
    (slabIncomingExponent n b β.degree.2 Q) β.degree.2 Q β.opposite
    β.endpoint_eq β.direction_eq β.incomingDirection_eq

/-- A decorated ray is determined by its output degree at the fixed endpoint. -/
@[ext]
theorem ext {β γ : SlabBrokenLine t c n b Q} (h : β.degree = γ.degree) : β = γ := by
  have hr : β.ray = γ.ray := by
    rw [β.ray_eq_slabBranch, γ.ray_eq_slabBranch]
    rw [h]
  cases β
  cases γ
  congr

/-- Singular avoidance is exactly nonvanishing of the crossing height. -/
theorem snd_sub_mul_fst_div_ne_zero (β : SlabBrokenLine t c n b Q) :
    Q.2 - (β.degree.2 : ℝ) * Q.1 / n ≠ 0 := by
  have h := β.avoids_origin
  rw [β.ray_eq_slabBranch] at h
  exact (slabBranch_avoids_origin_iff n
    (slabIncomingExponent n b β.degree.2 Q) β.degree.2 Q β.opposite).mp h

/-- Every decorated ray is proper on a closed incoming half-line. -/
theorem isProperMap (β : SlabBrokenLine t c n b Q) (a : ℝ) :
    IsProperMap (fun s : Set.Iic a => β.ray s) := by
  rw [β.ray_eq_slabBranch]
  exact isProperMap_slabBranch n (slabIncomingExponent n b β.degree.2 Q) β.degree.2 Q β.opposite a

/-- The final decoration is the selected entire homogeneous transfer. -/
def decoration (β : SlabBrokenLine t c n b Q) : R[ℤ × ℤ] :=
  (exponentCorrespondence (single 0 t + single 1 t)).transfer
    ⟨((n.natAbs : ℤ), b), by simp⟩ β.degree
    ⟨single (n.natAbs, b) c, single_mem_grade _ _⟩

/-- The final decoration is the whole transfer at the selected outgoing degree. -/
theorem decoration_def (β : SlabBrokenLine t c n b Q) :
    β.decoration =
      ((exponentCorrespondence (single 0 t + single 1 t)).transfer
        ⟨((n.natAbs : ℤ), b), by simp⟩ β.degree
        ⟨single (n.natAbs, b) c, single_mem_grade _ _⟩ : R[ℤ × ℤ]) := (rfl)

/-- The final decoration is nonzero as an element of the outgoing chamber algebra. -/
@[simp]
theorem decoration_ne_zero (β : SlabBrokenLine t c n b Q) : β.decoration ≠ 0 := by
  intro h
  exact β.transfer_ne_zero (Subtype.ext h)

/-- The upper chart, with incoming exponent `b+|n|` and parameter `t(1+w⁻¹)`,
gives the same entire decoration at every output degree. -/
theorem decoration_eq_upper (β : SlabBrokenLine t c n b Q) :
    β.decoration =
      ((exponentCorrespondence (single 0 t + single (-1) t)).transfer
        ⟨((n.natAbs : ℤ), b + n.natAbs), by simp⟩ β.degree
        ⟨single (n.natAbs, b + n.natAbs) c, single_mem_grade _ _⟩ : R[ℤ × ℤ]) :=
  slab_transfer_eq_upper t c n.natAbs b β.degree

end SlabBrokenLine

/-- The finite branch indices retain precisely the nonzero coefficients and the
branches avoiding the singular origin at the specified endpoint. -/
abbrev SlabBranchIndex :=
  {j : Fin (n.natAbs + 1) //
    c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 ∧
      Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0}

/-- Construct the decorated ray from a surviving binomial term. -/
def slabBrokenLine (hQ : Q.1 / (n : ℝ) < 0) (j : SlabBranchIndex t c n b Q) :
    SlabBrokenLine t c n b Q where
  degree := (-(n.natAbs : ℤ), b + j.val.val)
  ray := slabBranch n (slabIncomingExponent n b (b + j.val.val) Q) (b + j.val.val) Q hQ
  opposite := hQ
  transfer_ne_zero := by
    rw [← slabTransferEquiv_apply t c n.natAbs b ⟨j.val, j.property.1⟩]
    exact (slabTransferEquiv t c n.natAbs b ⟨j.val, j.property.1⟩).property
  endpoint_eq := endpoint_slabBranch _ _ _ _ _
  direction_eq := direction_slabBranch _ _ _ _ _
  incomingDirection_eq := incomingDirection_slabBranch _ _ _ _ _
  vertical_bends := by
    intro s hs
    rw [bends_slabBranch] at hs ⊢
    have he := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
    simp [he]
  slab_bends := by
    intro s hs
    rw [bends_slabBranch] at hs
    have he := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
    simp [he]
  avoids_origin := (slabBranch_avoids_origin_iff _ _ _ _ _).mpr j.property.2

@[simp]
theorem degree_slabBrokenLine (hQ : Q.1 / (n : ℝ) < 0) (j : SlabBranchIndex t c n b Q) :
    (slabBrokenLine t c n b Q hQ j).degree = (-(n.natAbs : ℤ), b + j.val.val) := (rfl)

@[simp]
theorem ray_slabBrokenLine (hQ : Q.1 / (n : ℝ) < 0) (j : SlabBranchIndex t c n b Q) :
    (slabBrokenLine t c n b Q hQ j).ray =
      slabBranch n (slabIncomingExponent n b (b + j.val.val) Q) (b + j.val.val) Q hQ := (rfl)

/-- The `j`-th line has exactly its binomial monomial decoration. -/
@[simp]
theorem decoration_slabBrokenLine (hQ : Q.1 / (n : ℝ) < 0)
    (j : SlabBranchIndex t c n b Q) :
    (slabBrokenLine t c n b Q hQ j).decoration =
      single (-(n.natAbs : ℤ), b + j.val.val)
        (c * t ^ n.natAbs * (n.natAbs.choose j.val.val : R)) := by
  rw [SlabBrokenLine.decoration_def, degree_slabBrokenLine]
  have h := exponentCorrespondence_transfer_binomial t c n.natAbs b 1 (by decide) j.val.val
  rw [mul_one] at h
  exact h

/-- Every decorated crossing ray is exactly one surviving binomial branch.
This is an equivalence of actual evaluation fibers, not just of formal degrees. -/
def slabBrokenLineEquiv (hQ : Q.1 / (n : ℝ) < 0) :
    SlabBranchIndex t c n b Q ≃ SlabBrokenLine t c n b Q where
  toFun := slabBrokenLine t c n b Q hQ
  invFun β := by
    let j := (slabTransferEquiv t c n.natAbs b).symm ⟨β.degree, β.transfer_ne_zero⟩
    have he : (-(n.natAbs : ℤ), b + j.val.val) = β.degree :=
      slabTransferEquiv_symm_degree t c n.natAbs b ⟨β.degree, β.transfer_ne_zero⟩
    exact ⟨j.val, j.property, by
      simpa only [← he] using β.snd_sub_mul_fst_div_ne_zero⟩
  left_inv j := by
    have he := (Equiv.symm_apply_eq (slabTransferEquiv t c n.natAbs b)
      (x := ⟨(slabBrokenLine t c n b Q hQ j).degree,
        (slabBrokenLine t c n b Q hQ j).transfer_ne_zero⟩)
      (y := ⟨j.val, j.property.1⟩)).mpr
        (by
          apply Subtype.ext
          simp only [Subtype.coe_mk, degree_slabBrokenLine, slabTransferEquiv_apply])
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun i => i.val.val) he
  right_inv β := by
    apply SlabBrokenLine.ext
    dsimp only [slabBrokenLine]
    exact slabTransferEquiv_symm_degree t c n.natAbs b ⟨β.degree, β.transfer_ne_zero⟩

@[simp]
theorem slabBrokenLineEquiv_apply (hQ : Q.1 / (n : ℝ) < 0)
    (j : SlabBranchIndex t c n b Q) :
    slabBrokenLineEquiv t c n b Q hQ j = slabBrokenLine t c n b Q hQ j := (rfl)

/-- The inverse enumeration recovers the branch index from its tangential exponent. -/
@[simp]
theorem slabBrokenLineEquiv_symm_apply_val (hQ : Q.1 / (n : ℝ) < 0)
    (β : SlabBrokenLine t c n b Q) :
    ((slabBrokenLineEquiv t c n b Q hQ).symm β).val.val =
      (β.degree.2 - b).toNat :=
  slabTransferEquiv_symm_apply_val t c n.natAbs b ⟨β.degree, β.transfer_ne_zero⟩

/-- Every evaluation fiber is finite, even when the coefficient ring is infinite. -/
instance : Finite (SlabBrokenLine t c n b Q) := by
  classical
  by_cases hQ : Q.1 / (n : ℝ) < 0
  · exact Finite.of_equiv _ (slabBrokenLineEquiv t c n b Q hQ)
  · have : IsEmpty (SlabBrokenLine t c n b Q) := ⟨fun β => hQ β.opposite⟩
    infer_instance

/-- A finite enumeration of the actual decorated rays for weighted evaluation. -/
instance : Fintype (SlabBrokenLine t c n b Q) := Fintype.ofFinite _

/-- Sum the final decorations over the evaluation fiber. -/
def slabWeightedEvaluation : R[ℤ × ℤ] :=
  ∑ β : SlabBrokenLine t c n b Q, β.decoration

/-- Weighted evaluation sums the final decorations of the actual evaluation fiber. -/
theorem slabWeightedEvaluation_def :
    slabWeightedEvaluation t c n b Q =
      ∑ β : SlabBrokenLine t c n b Q, β.decoration := (rfl)

/-- No crossing ray ends outside the chamber opposite the incoming direction. -/
@[simp]
theorem slabWeightedEvaluation_of_not_neg (hQ : ¬ Q.1 / (n : ℝ) < 0) :
    slabWeightedEvaluation t c n b Q = 0 := by
  have : IsEmpty (SlabBrokenLine t c n b Q) := ⟨fun β => hQ β.opposite⟩
  simp [slabWeightedEvaluation_def]

/-- Zero incoming coefficient gives an empty evaluation fiber and hence zero weight. -/
@[simp]
theorem slabWeightedEvaluation_zero : slabWeightedEvaluation t (0 : R) n b Q = 0 := by
  have : IsEmpty (SlabBrokenLine t (0 : R) n b Q) := ⟨fun β =>
    β.transfer_ne_zero (by simp)⟩
  simp [slabWeightedEvaluation_def]

/-- Weighted evaluation is the finite sum of the surviving, nonsingular branches. -/
theorem slabWeightedEvaluation_eq_sum [Fintype (SlabBranchIndex t c n b Q)]
    (hQ : Q.1 / (n : ℝ) < 0) :
    slabWeightedEvaluation t c n b Q =
      ∑ j : SlabBranchIndex t c n b Q,
        single (-(n.natAbs : ℤ), b + j.val.val)
          (c * t ^ n.natAbs * (n.natAbs.choose j.val.val : R)) := by
  classical
  exact (Fintype.sum_equiv (slabBrokenLineEquiv t c n b Q hQ) _ _
    (fun j => (decoration_slabBrokenLine t c n b Q hQ j).symm)).symm

/-- Away from the surviving binomial crossing-height hyperplanes, weighted evaluation
is the full slab crossing. Terms killed by the scalar ring or smoothing parameter
are discarded from the fiber and contribute zero to the algebraic expansion. -/
theorem slabWeightedEvaluation_eq_exponentRightMap_exponentIncomingLift (hQ : Q.1 / (n : ℝ) < 0)
    (hgeneric : ∀ j : Fin (n.natAbs + 1),
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 →
        Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0) :
    slabWeightedEvaluation t c n b Q =
      exponentRightMap (single 0 t + single 1 t)
        (exponentIncomingLift (single 0 t + single 1 t) 0
          ⟨((n.natAbs : ℤ), b), by simp⟩
          ⟨single (n.natAbs, b) c, single_mem_grade _ _⟩) := by
  classical
  rw [slabWeightedEvaluation_eq_sum t c n b Q hQ,
    exponentRightMap_exponentIncomingLift_binomial]
  simp only [nsmul_eq_mul, mul_one]
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_congr_set
    {j : Fin (n.natAbs + 1) |
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 ∧
        Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0}
  · intro j _
    rfl
  · intro j hj
    have hc : c * t ^ n.natAbs * (n.natAbs.choose j.val : R) = 0 := by
      by_contra hc
      exact hj ⟨hc, hgeneric j hc⟩
    simp only [hc, single_zero]

/-- The same evaluation is the reverse slab crossing for incoming `Y` powers.
The two normal Laurent coordinates both give positive incoming exponent `|n|`. -/
theorem slabWeightedEvaluation_eq_exponentLeftMap_exponentIncomingLift (hQ : Q.1 / (n : ℝ) < 0)
    (hgeneric : ∀ j : Fin (n.natAbs + 1),
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 →
        Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0) :
    slabWeightedEvaluation t c n b Q =
      exponentLeftMap (single 0 t + single 1 t)
        (exponentIncomingLift (single 0 t + single 1 t) 1
          ⟨((n.natAbs : ℤ), b), by simp⟩
          ⟨single (n.natAbs, b) c, single_mem_grade _ _⟩) := by
  rw [slabWeightedEvaluation_eq_exponentRightMap_exponentIncomingLift t c n b Q hQ hgeneric,
    exponentRightMap_exponentIncomingLift_binomial,
    exponentLeftMap_exponentIncomingLift_binomial]

end Mei.FocusFocus
