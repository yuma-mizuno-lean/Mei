/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Evaluation
public import Mei.RingTheory.Node.ExponentMap

/-!
# Specializing decorated focus-focus rays

A coefficient homomorphism retains exactly those slab rays whose whole decoration
has nonzero image. It changes neither their degrees nor their geometric paths.
Every ray over the target coefficients comes from a unique surviving source ray.
Consequently finite weighted evaluation commutes with specialization, including
at nongeneric endpoints, where rays through the singular origin are absent on
both sides. The full evaluation also includes the incoming and stationary sectors.
In particular these results apply to reductions of truncated smoothing rings;
no injectivity of the coefficient map or regularity of the smoothing parameter
is required.

The construction uses `SlabBrokenLine.ext`, the binomial transfer enumeration,
`NodeAlgebra.exponentCorrespondenceMap` and transfer naturality,
and `Finset.sum_congr_set` to discard zero image decorations. The geometric and
coefficient conventions follow Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3
(arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  {t c : R} {n b : ℤ} {Q : ℝ × ℝ}

namespace SlabBrokenLine

open scoped AlgebraMonoidAlgebra in
/-- Coefficient change sends a ray's whole decoration to the transfer at the
same degree in the target slab, whether or not that transfer survives. -/
theorem map_decoration_eq_transfer (β : SlabBrokenLine t c n b Q) (φ : R →+* S) :
    mapRingHom (ℤ × ℤ) φ β.decoration =
      ((exponentCorrespondence (single 0 (φ t) + single 1 (φ t))).transfer
        ⟨((n.natAbs : ℤ), b), by simp⟩ β.degree
        ⟨single (n.natAbs, b) (φ c), single_mem_grade _ _⟩ : S[ℤ × ℤ]) := by
  let := φ.toAlgebra
  have hφ : algebraMap R S = φ := RingHom.algebraMap_toAlgebra φ
  have h := (exponentCorrespondenceMap (S := S) (single 0 t + single 1 t)).transfer_map_of_injective
      Function.injective_id
      ⟨((n.natAbs : ℤ), b), by simp⟩
      ⟨single (n.natAbs, b) c, single_mem_grade _ _⟩ β.degree
  -- First forget the restricted scalar action, then normalize the slab parameter.
  have h' : mapRingHom (ℤ × ℤ) φ β.decoration =
      ((exponentCorrespondence (algebraMap R[ℤ] S[ℤ] (single 0 t + single 1 t))).transfer
        ⟨((n.natAbs : ℤ), b), by simp⟩ β.degree
        ⟨single (n.natAbs, b) (φ c), single_mem_grade _ _⟩ : S[ℤ × ℤ]) := by
    ext p
    have hp := congrArg (fun x : S[ℤ × ℤ] => x.coeff p) h.symm
    simp only [decoration_def, exponentCorrespondenceMap_left,
      exponentCorrespondenceMap_right, AlgHom.toLinearMap_apply, id_eq,
      ← AlgHom.coe_toRingHom, toRingHom_mapAlgHom, AlgHom.toRingHom_eq_coe,
      Algebra.toRingHom_ofId, hφ, mapRingHom_single, GradedCorrespondence.transfer_apply,
      GradedCorrespondence.restrictScalars_right,
      GradedCorrespondence.restrictScalars_liftLeft_apply, LinearMap.restrictScalars_apply,
      DirectSum.coe_decompose_restrictScalars, coeff_mapRingHom] at hp ⊢
    convert hp using 1
    congr 6
  refine h'.trans ?_
  exact congrArg (fun a : S[ℤ] =>
    ((exponentCorrespondence a).transfer ⟨((n.natAbs : ℤ), b), by simp⟩ β.degree
      ⟨single (n.natAbs, b) (φ c), single_mem_grade _ _⟩ : S[ℤ × ℤ]))
    (by simp only [AddMonoidAlgebra.algebraMap_def, hφ, map_add, mapRingHom_single])

/-- Specialize a ray whose entire decoration has nonzero image. The geometric
ray and both developed directions are retained verbatim. -/
def map (β : SlabBrokenLine t c n b Q) (φ : R →+* S)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0) :
    SlabBrokenLine (φ t) (φ c) n b Q where
  degree := β.degree
  ray := β.ray
  opposite := β.opposite
  transfer_ne_zero := by
    intro hz
    apply h
    rw [β.map_decoration_eq_transfer φ]
    exact congrArg Subtype.val hz
  endpoint_eq := β.endpoint_eq
  direction_eq := β.direction_eq
  incomingDirection_eq := β.incomingDirection_eq
  vertical_bends := β.vertical_bends
  slab_bends := β.slab_bends
  avoids_origin := β.avoids_origin

/-- Specialization preserves the full outgoing Laurent degree. -/
@[simp]
theorem degree_map (β : SlabBrokenLine t c n b Q) (φ : R →+* S)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0) :
    (β.map φ h).degree = β.degree := (rfl)

/-- Specialization preserves the actual finite affine ray, including its tail. -/
@[simp]
theorem ray_map (β : SlabBrokenLine t c n b Q) (φ : R →+* S)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0) :
    (β.map φ h).ray = β.ray := (rfl)

/-- The retained ray carries the image of the entire source decoration. -/
@[simp]
theorem decoration_map (β : SlabBrokenLine t c n b Q) (φ : R →+* S)
    (h : mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0) :
    (β.map φ h).decoration = mapRingHom (ℤ × ℤ) φ β.decoration := by
  rw [β.map_decoration_eq_transfer φ, decoration_def, degree_map]

/-- Changing no coefficients fixes every decorated ray. -/
@[simp]
theorem map_id (β : SlabBrokenLine t c n b Q) :
    β.map (RingHom.id R) (by simp) = β := by
  apply SlabBrokenLine.ext
  rfl

/-- Successive specializations agree with their composite. Survival of the final
image already implies survival at the intermediate coefficient ring. -/
theorem map_map (β : SlabBrokenLine t c n b Q) (φ : R →+* S) (ψ : S →+* T)
    (h : mapRingHom (ℤ × ℤ) (ψ.comp φ) β.decoration ≠ 0) :
    (β.map φ (by
      intro hz
      apply h
      rw [mapRingHom_comp, RingHom.comp_apply, hz, map_zero])).map ψ
        (by simpa only [decoration_map, mapRingHom_comp, RingHom.comp_apply] using h) =
      β.map (ψ.comp φ) h := by
  apply SlabBrokenLine.ext
  rfl

/-- Every ray after specialization has a unique source ray with nonzero image
decoration. This equivalence discards exactly the decorations killed by the map. -/
def mapEquiv (φ : R →+* S) :
    {β : SlabBrokenLine t c n b Q // mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0} ≃
      SlabBrokenLine (φ t) (φ c) n b Q where
  toFun β := β.val.map φ β.property
  invFun γ := by
    let β : SlabBrokenLine t c n b Q := {
      degree := γ.degree
      ray := γ.ray
      opposite := γ.opposite
      transfer_ne_zero := by
        obtain ⟨j, hj, he, hc⟩ :=
          (exponentCorrespondence_transfer_ne_zero_iff (φ t) (φ c) n.natAbs b 1
            (by decide) γ.degree).mp γ.transfer_ne_zero
        refine (exponentCorrespondence_transfer_ne_zero_iff t c n.natAbs b 1
          (by decide) γ.degree).mpr ⟨j, hj, he, ?_⟩
        intro hz
        apply hc
        simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg φ hz
      endpoint_eq := γ.endpoint_eq
      direction_eq := γ.direction_eq
      incomingDirection_eq := γ.incomingDirection_eq
      vertical_bends := γ.vertical_bends
      slab_bends := γ.slab_bends
      avoids_origin := γ.avoids_origin }
    exact ⟨β, by
      rw [β.map_decoration_eq_transfer φ]
      exact fun hz => γ.transfer_ne_zero (Subtype.ext hz)⟩
  left_inv β := by
    apply Subtype.ext
    apply SlabBrokenLine.ext
    rfl
  right_inv γ := by
    apply SlabBrokenLine.ext
    rfl

/-- The specialization equivalence is the coefficient map on surviving rays. -/
@[simp]
theorem mapEquiv_apply (φ : R →+* S)
    (β : {β : SlabBrokenLine t c n b Q // mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0}) :
    mapEquiv φ β = β.val.map φ β.property := (rfl)

/-- Recovering the source of a target ray retains its full degree. -/
@[simp]
theorem degree_mapEquiv_symm (φ : R →+* S)
    (γ : SlabBrokenLine (φ t) (φ c) n b Q) :
    ((mapEquiv φ).symm γ).val.degree = γ.degree := (rfl)

/-- Recovering the source retains the whole geometric path. -/
@[simp]
theorem ray_mapEquiv_symm (φ : R →+* S)
    (γ : SlabBrokenLine (φ t) (φ c) n b Q) :
    ((mapEquiv φ).symm γ).val.ray = γ.ray := (rfl)

/-- The recovered source decoration specializes to the prescribed target decoration. -/
@[simp]
theorem map_decoration_mapEquiv_symm (φ : R →+* S)
    (γ : SlabBrokenLine (φ t) (φ c) n b Q) :
    mapRingHom (ℤ × ℤ) φ ((mapEquiv φ).symm γ).val.decoration = γ.decoration := by
  have he := congrArg SlabBrokenLine.decoration ((mapEquiv φ).apply_symm_apply γ)
  simpa only [mapEquiv_apply, decoration_map] using he

end SlabBrokenLine

/-- The sum over actual crossing rays commutes with any coefficient specialization.
No genericity assumption on the endpoint is needed. -/
@[simp]
theorem mapRingHom_slabWeightedEvaluation (φ : R →+* S) (t c : R)
    (n b : ℤ) (Q : ℝ × ℝ) :
    mapRingHom (ℤ × ℤ) φ (slabWeightedEvaluation t c n b Q) =
      slabWeightedEvaluation (φ t) (φ c) n b Q := by
  classical
  rw [slabWeightedEvaluation_def, map_sum, slabWeightedEvaluation_def]
  let survivors := {β : SlabBrokenLine t c n b Q |
    mapRingHom (ℤ × ℤ) φ β.decoration ≠ 0}
  calc
    _ = ∑ β : survivors, mapRingHom (ℤ × ℤ) φ β.val.decoration :=
      Finset.sum_congr_set survivors _ _ (fun _ _ => rfl) (fun _ h => not_ne_iff.mp h)
    _ = _ := Fintype.sum_equiv (SlabBrokenLine.mapEquiv φ) _ _
      (fun β => (β.val.decoration_map φ β.property).symm)

/-- The complete focus-focus evaluation, with its incoming, crossing and stationary
sectors, commutes with coefficient maps and hence with smoothing-order reduction. -/
@[simp]
theorem mapRingHom_slabThetaEvaluation (φ : R →+* S) (t c : R)
    (n b : ℤ) (Q : ℝ × ℝ) :
    mapRingHom (ℤ × ℤ) φ (slabThetaEvaluation t c n b Q) =
      slabThetaEvaluation (φ t) (φ c) n b Q := by
  simp only [slabThetaEvaluation_def, map_add, map_incomingSlabWeightedEvaluation,
    mapRingHom_slabWeightedEvaluation]
  split_ifs <;> simp

end Mei.FocusFocus
