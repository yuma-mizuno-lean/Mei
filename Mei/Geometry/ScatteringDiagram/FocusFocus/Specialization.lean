/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Evaluation

/-!
# Coefficient specialization of decorated focus-focus rays

A coefficient homomorphism retains exactly the crossing rays whose entire
decorations survive. The surviving source fiber is equivalent to the target
fiber, with the same degrees, geometric paths and incoming tails. In particular,
specialization commutes with the actual finite weighted evaluation, even at
endpoints on some crossing-height exceptions. No injectivity or characteristic
assumption is imposed on the coefficients or the smoothing parameter.

We use the existing exhaustive binomial enumeration `slabBrokenLineEquiv`,
`NodeAlgebra.exponentCorrespondence_transfer_ne_zero_iff` and Mathlib's
coefficient homomorphism `AddMonoidAlgebra.mapRingHom`. The geometric and slab
conventions follow Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.2–2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  {t c : R} {n b : ℤ} {Q : ℝ × ℝ}

namespace SlabBrokenLine

private theorem map_transfer (φ : R →+* S) (β : SlabBrokenLine t c n b Q) :
    mapRingHom (ℤ × ℤ) φ β.decoration =
      ((exponentCorrespondence (single 0 (φ t) + single 1 (φ t))).transfer
        ⟨((n.natAbs : ℤ), b), by simp⟩ β.degree
        ⟨single (n.natAbs, b) (φ c), single_mem_grade _ _⟩ : S[ℤ × ℤ]) := by
  obtain ⟨j, _, he, _⟩ := (exponentCorrespondence_transfer_ne_zero_iff
    t c n.natAbs b 1 (by decide) β.degree).mp β.transfer_ne_zero
  rw [decoration_def, he]
  rw [exponentCorrespondence_transfer_binomial t c n.natAbs b 1 (by decide) j,
    exponentCorrespondence_transfer_binomial (φ t) (φ c) n.natAbs b 1 (by decide) j]
  simp

/-- Specialize a crossing ray when its entire output decoration survives.
The geometric ray and its developed incoming germ are retained verbatim. -/
def mapCoefficients (β : SlabBrokenLine t c n b Q) (φ : R →+* S)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0) :
    SlabBrokenLine (φ t) (φ c) n b Q where
  degree := β.degree
  ray := β.ray
  opposite := β.opposite
  transfer_ne_zero := by
    intro hz
    apply h
    rw [map_transfer φ β, hz]
    rfl
  endpoint_eq := β.endpoint_eq
  direction_eq := β.direction_eq
  incomingDirection_eq := β.incomingDirection_eq
  vertical_bends := β.vertical_bends
  slab_bends := β.slab_bends
  avoids_origin := β.avoids_origin

/-- Specialization does not change the selected output degree. -/
@[simp]
theorem degree_mapCoefficients (β : SlabBrokenLine t c n b Q) (φ : R →+* S)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0) :
    (β.mapCoefficients φ h).degree = β.degree := (rfl)

/-- Specialization retains the whole geometric path, including its incoming tail. -/
@[simp]
theorem ray_mapCoefficients (β : SlabBrokenLine t c n b Q) (φ : R →+* S)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0) :
    (β.mapCoefficients φ h).ray = β.ray := (rfl)

/-- The decoration of the specialized ray is the coefficientwise image of the
whole source decoration. -/
@[simp]
theorem decoration_mapCoefficients (β : SlabBrokenLine t c n b Q) (φ : R →+* S)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0) :
    (β.mapCoefficients φ h).decoration = mapRingHom (ℤ × ℤ) φ β.decoration := by
  rw [decoration_def, degree_mapCoefficients]
  exact (map_transfer φ β).symm

/-- Every target ray comes from a surviving source ray, even when specialization
kills other binomial terms or the smoothing parameter. -/
private theorem exists_mapCoefficients (φ : R →+* S)
    (γ : SlabBrokenLine (φ t) (φ c) n b Q) :
    ∃ (β : SlabBrokenLine t c n b Q)
      (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0), β.mapCoefficients φ h = γ := by
  let j := (slabBrokenLineEquiv (φ t) (φ c) n b Q γ.opposite).symm γ
  have hj : c * t ^ n.natAbs * (n.natAbs.choose j.val.val : R) ≠ 0 := by
    intro hz
    apply j.property.1
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg φ hz
  let i : SlabBranchIndex t c n b Q := ⟨j.val, hj, j.property.2⟩
  let β := slabBrokenLine t c n b Q γ.opposite i
  have hβ : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0 := by
    rw [decoration_slabBrokenLine, mapRingHom_single]
    intro hz
    apply j.property.1
    simpa only [map_mul, map_pow, map_natCast] using (single_eq_zero.mp hz)
  refine ⟨β, hβ, ?_⟩
  apply SlabBrokenLine.ext
  have he := congrArg SlabBrokenLine.degree
    ((slabBrokenLineEquiv (φ t) (φ c) n b Q γ.opposite).apply_symm_apply γ)
  simpa only [degree_mapCoefficients, β, degree_slabBrokenLine,
    slabBrokenLineEquiv_apply] using he

/-- The surviving source fiber is exactly the specialized fiber. This records
deletion of zero decorations, rather than requiring a bijection of all rays. -/
def coefficientEquiv (φ : R →+* S) :
    {β : SlabBrokenLine t c n b Q // mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0} ≃
      SlabBrokenLine (φ t) (φ c) n b Q :=
  Equiv.ofBijective (fun β => β.val.mapCoefficients φ β.property) ⟨by
    intro β γ he
    apply Subtype.ext
    apply SlabBrokenLine.ext
    simpa only [degree_mapCoefficients] using congrArg SlabBrokenLine.degree he, by
    intro γ
    obtain ⟨β, h, he⟩ := exists_mapCoefficients φ γ
    exact ⟨⟨β, h⟩, he⟩⟩

/-- The fiber comparison uses coefficient specialization on each surviving ray. -/
@[simp]
theorem coefficientEquiv_apply (φ : R →+* S)
    (β : {β : SlabBrokenLine t c n b Q // mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0}) :
    coefficientEquiv φ β = β.val.mapCoefficients φ β.property := (rfl)

/-- The inverse comparison recovers the same outgoing degree in the source. -/
@[simp]
theorem degree_coefficientEquiv_symm (φ : R →+* S)
    (γ : SlabBrokenLine (φ t) (φ c) n b Q) :
    ((coefficientEquiv φ).symm γ).val.degree = γ.degree := by
  simpa only [coefficientEquiv_apply, degree_mapCoefficients] using
    congrArg SlabBrokenLine.degree ((coefficientEquiv φ).apply_symm_apply γ)

/-- The inverse comparison recovers the identical geometric ray in the source. -/
@[simp]
theorem ray_coefficientEquiv_symm (φ : R →+* S)
    (γ : SlabBrokenLine (φ t) (φ c) n b Q) :
    ((coefficientEquiv φ).symm γ).val.ray = γ.ray := by
  simpa only [coefficientEquiv_apply, ray_mapCoefficients] using
    congrArg SlabBrokenLine.ray ((coefficientEquiv φ).apply_symm_apply γ)

/-- The inverse comparison lifts the entire target decoration. -/
@[simp]
theorem map_decoration_coefficientEquiv_symm (φ : R →+* S)
    (γ : SlabBrokenLine (φ t) (φ c) n b Q) :
    mapRingHom (ℤ × ℤ) φ ((coefficientEquiv φ).symm γ).val.decoration = γ.decoration := by
  simpa only [coefficientEquiv_apply, decoration_mapCoefficients] using
    congrArg SlabBrokenLine.decoration ((coefficientEquiv φ).apply_symm_apply γ)

/-- Identity specialization fixes every ray. -/
@[simp]
theorem mapCoefficients_id (β : SlabBrokenLine t c n b Q)
    (h : mapRingHom (ℤ × ℤ) (RingHom.id R) β.decoration ≠ 0) :
    β.mapCoefficients (RingHom.id R) h = β := by
  apply SlabBrokenLine.ext
  rfl

/-- Successive specializations agree with their composite on surviving rays. -/
theorem mapCoefficients_comp (β : SlabBrokenLine t c n b Q)
    (φ : R →+* S) (ψ : S →+* T)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0)
    (h' : mapRingHom (ℤ × ℤ) ψ (β.mapCoefficients φ h).decoration ≠ 0) :
    (β.mapCoefficients φ h).mapCoefficients ψ h' =
      β.mapCoefficients (ψ.comp φ) (by
        simpa only [decoration_mapCoefficients, mapRingHom_comp, RingHom.comp_apply]
          using h') := by
  apply SlabBrokenLine.ext
  rfl

end SlabBrokenLine

/-- Coefficient specialization commutes with the sum over actual crossing rays.
This holds at every endpoint: singular branches are omitted on both sides,
and branches killed by specialization contribute zero. -/
@[simp]
theorem map_slabWeightedEvaluation (φ : R →+* S) (t c : R) (n b : ℤ) (Q : ℝ × ℝ) :
    mapRingHom (ℤ × ℤ) φ (slabWeightedEvaluation t c n b Q) =
      slabWeightedEvaluation (φ t) (φ c) n b Q := by
  classical
  rw [slabWeightedEvaluation_def, map_sum, slabWeightedEvaluation_def]
  apply Finset.sum_bij_ne_zero (fun β _ h => β.mapCoefficients φ h)
  · intro β _ h
    exact Finset.mem_univ _
  · intro β _ hβ γ _ hγ he
    apply SlabBrokenLine.ext
    simpa only [SlabBrokenLine.degree_mapCoefficients] using
      congrArg SlabBrokenLine.degree he
  · intro γ _ _
    obtain ⟨β, he⟩ := (SlabBrokenLine.coefficientEquiv
      (t := t) (c := c) (n := n) (b := b) (Q := Q) φ).surjective γ
    exact ⟨β.val, Finset.mem_univ _, β.property, he⟩
  · intro β _ h
    exact (SlabBrokenLine.decoration_mapCoefficients β φ h).symm

/-- Incoming proper rays specialize coefficientwise, including when the
specialization kills the incoming coefficient. -/
theorem map_incomingSlabWeightedEvaluation (φ : R →+* S) (c : R) (n b : ℤ)
    (Q : ℝ × ℝ) :
    mapRingHom (ℤ × ℤ) φ (incomingSlabWeightedEvaluation c n b Q) =
      incomingSlabWeightedEvaluation (φ c) n b Q := by
  simp only [incomingSlabWeightedEvaluation_eq]
  split_ifs <;> simp

/-- The full geometric theta evaluation commutes with specialization, including
the stationary incoming section and both crossing directions. -/
@[simp]
theorem map_slabThetaEvaluation (φ : R →+* S) (t c : R) (n b : ℤ) (Q : ℝ × ℝ) :
    mapRingHom (ℤ × ℤ) φ (slabThetaEvaluation t c n b Q) =
      slabThetaEvaluation (φ t) (φ c) n b Q := by
  simp only [slabThetaEvaluation_def, map_add, map_slabWeightedEvaluation,
    map_incomingSlabWeightedEvaluation]
  split_ifs <;> simp

end Mei.FocusFocus
