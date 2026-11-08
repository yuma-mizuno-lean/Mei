/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Incoming.Family
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Basic
public import Mei.Geometry.Convex.Sweep.Admissible.SingleFace

/-!
# Incoming focus-focus rays in the shared decorated fiber

An incoming chart uses the empty path of the one-object quiver on `Unit`, the full slab as a wall
obstacle, the singular origin, and its full open half-plane as incoming source.
The common decorated rays are exactly the explicit incoming rays, including
vertical rays on either side. Their whole paths and homogeneous decorations agree.
Zero coefficients and zero spatial direction have no proper incoming chart;
stationary incoming sections remain a separate sector of the theta family.

The comparison uses the shared single-face encounter bound and the existing
incoming chart classification. It does not infer straightness from a desired
weighted sum. Slab conventions follow Gross–Siebert, *An Invitation to Toric
Degenerations*, §§2.2–2.3 (arXiv:0808.2749v2), and whole-component decorations
follow Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Filter AddMonoidAlgebra Mei.Convex Quiver

namespace Mei.FocusFocus

variable {R : Type*} [CommSemiring R] (c : R) (n b : ℤ)

local notation "ν" => ContinuousLinearMap.fst ℝ ℝ ℝ
local notation "p" => ((n.natAbs : ℤ), b)
local notation "a" => (Subtype.mk (single p c) (single_mem_grade _ _) : grade R p)
local notation "v" => fun q : ℤ × ℤ => ((n : ℝ), ((Prod.snd q : ℤ) : ℝ))

/-- A common empty-itinerary decorated ray with the full incoming half-plane
of its admitted chart. Vertical incoming degrees admit both chart labels. -/
abbrev IncomingSlabChartRay (α : IncomingSlabChartIndex c n b) (Q : ℝ × ℝ) :=
  PathDecoratedRay (Q := SingleObj Unit) (M := fun _ => R[ℤ × ℤ]) (ι := fun _ => ℤ × ℤ)
    (fun _ => LinearMap.id) (fun _ => (grade R : ℤ × ℤ → Submodule R R[ℤ × ℤ])) p a (fun _ => v)
    (fun _ => ν) (fun _ => 0) (fun _ => 0) (fun _ => {x : ℝ × ℝ | x.1 = 0})
    (fun _ : Unit => {x : ℝ × ℝ | x.1 = 0}) (fun _ : Unit => ({0} : Set (ℝ × ℝ)))
    (incomingSlabDomain α.val) (Path.nil : Path (SingleObj.star Unit) (SingleObj.star Unit)) Q

/-- The empty-path data of an incoming chart ray are the constant single-face data with
the incoming velocity. -/
private theorem incomingRay_data :
    ((Path.nil : Path (SingleObj.star Unit) (SingleObj.star Unit)).reverseArrowLabels
        fun _ => ν) = (fun _ : Fin 0 => ν) ∧
      ((Path.nil : Path (SingleObj.star Unit) (SingleObj.star Unit)).reverseArrowLabels
        fun _ => (0 : ℝ)) = (fun _ : Fin 0 => 0) ∧
      ((Path.nil : Path (SingleObj.star Unit) (SingleObj.star Unit)).reverseArrowLabels
        fun _ => {x : ℝ × ℝ | x.1 = 0}) = (fun _ : Fin 0 => {x : ℝ × ℝ | x.1 = 0}) ∧
      Path.Degrees.reverseVertexLabels (fun _ => v) p
        (Path.nil : Path (SingleObj.star Unit) (SingleObj.star Unit)) PUnit.unit =
        fun _ => ((n : ℝ), (b : ℝ)) :=
  ⟨funext fun j => j.elim0, funext fun j => j.elim0, funext fun j => j.elim0,
    Path.Degrees.reverseVertexLabels_nil _ _ _⟩

/-- With no recorded encounters, the common path is the straight incoming path.
This equality retains the whole incoming half-line, not only its endpoint. -/
@[simp]
theorem IncomingSlabChartRay.ray_eq_straight (α : IncomingSlabChartIndex c n b)
    (Q : ℝ × ℝ) (r : IncomingSlabChartRay c n b α Q) :
    r.2.ray = FiniteAffineRay.straight Q ((n : ℝ), (b : ℝ)) := by
  obtain ⟨hf, hc, hP, hv⟩ := incomingRay_data n b
  obtain ⟨_, _, hr⟩ := (r.2.congrData hf hc hv hP).eq_backwardRay
  have hr' : (r.2.congrData hf hc hv hP).ray = r.2.ray :=
    AdmissibleRayRealization.ray_congrData _ _ _ _ _
  rw [hr'] at hr
  rw [hr]
  exact backwardRay_zero _ _ _ _ _

/-- The global incoming-source and wall-avoidance conditions force the endpoint
to lie in the same open half-plane, also for zero normal velocity. -/
theorem IncomingSlabChartRay.endpoint_mem (α : IncomingSlabChartIndex c n b)
    (Q : ℝ × ℝ) (r : IncomingSlabChartRay c n b α Q) :
    Q ∈ incomingSlabDomain α.val := by
  by_cases hn : n = 0
  · obtain ⟨s, hs⟩ := r.2.incoming.exists
    rw [r.ray_eq_straight c n b α Q, mem_incomingSlabDomain] at hs
    simpa [hn, FiniteAffineRay.straight_apply] using hs
  · obtain ⟨hf, hc, hP, hv⟩ := incomingRay_data n b
    have he := (r.2.congrData hf hc hv hP).encounter_count_eq_zero_iff_singleFace
      (fun j => j.elim0) (by simpa using (Int.cast_ne_zero.mpr hn : (n : ℝ) ≠ 0))
      () Set.Subset.rfl
    have ht : 0 < Q.1 / (n : ℝ) := by simpa using he.mp rfl
    have hsign := α.property.2.2
    rw [mem_incomingSlabDomain]
    cases ha : α.val <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at hsign ⊢
    · have hn' : (n : ℝ) < 0 := by exact_mod_cast lt_of_le_of_ne hsign hn
      exact (div_pos_iff.mp ht).resolve_left (fun h => (not_lt_of_ge hn'.le) h.2) |>.1
    · have hn' : 0 < (n : ℝ) := by exact_mod_cast lt_of_le_of_ne hsign (Ne.symm hn)
      exact (div_pos_iff.mp ht).resolve_right (fun h => (not_lt_of_ge hn'.le) h.2) |>.1

private def incomingSlabChartRay (α : IncomingSlabChartIndex c n b) (Q : ℝ × ℝ)
    (hQ : Q ∈ incomingSlabDomain α.val) : IncomingSlabChartRay c n b α Q := by
  let β := incomingSlabChartEquiv c n b Q ⟨α, hQ⟩
  obtain ⟨hf, hc, hP, hv⟩ := incomingRay_data n b
  refine ⟨⟨PUnit.unit, ?_⟩, AdmissibleRayRealization.congrData {
    ray := β.ray
    parameter := fun _ => 0
    parameter_zero := rfl
    strictAnti_parameter := by
      intro i j hij
      have := Fin.eq_zero i
      have := Fin.eq_zero j
      omega
    transverse := fun j => j.elim0
    endpoint_eq := β.endpoint_eq
    directionAt_eq := ?_
    bends_recorded := ?_
    height_eq := fun j => j.elim0
    incidence := fun j => j.elim0
    avoids_walls := fun _ s hs _ => β.fst_ne_zero s hs.le
    incoming := ?_
    avoids_singular := fun _ s hs => β.avoids_origin s hs
    off_walls := fun _ => β.off_slab } hf.symm hc.symm hv.symm hP.symm⟩
  · rw [mem_pathDecoratedHistorySupport, Path.homogeneousHistory_nil, LinearMap.id_apply]
    exact ⟨by simp [α.property.1], fun j => j.elim0⟩
  · intro j
    rw [β.ray_eq_straight]
    simp
  · simp
  · filter_upwards [eventually_le_atBot (0 : ℝ)] with s hs
    rw [β.ray_eq_straight, FiniteAffineRay.straight_apply, mem_incomingSlabDomain]
    have hside := (mem_incomingSlabDomain α.val Q).mp hQ
    have hsign := α.property.2.2
    cases ha : α.val <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at hside hsign ⊢
    · have hn : (n : ℝ) ≤ 0 := by exact_mod_cast hsign
      exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hs) hn)
        hside
    · have hn : 0 ≤ (n : ℝ) := by exact_mod_cast hsign
      exact add_pos_of_nonneg_of_pos (mul_nonneg (neg_nonneg.mpr hs) hn) hside

private def incomingSlabChartEndpointEquiv (Q : ℝ × ℝ) :
    (Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q) ≃
      {α : IncomingSlabChartIndex c n b // Q ∈ incomingSlabDomain α.val} where
  toFun r := ⟨r.1, r.2.endpoint_mem c n b r.1 Q⟩
  invFun α := ⟨α.val, incomingSlabChartRay c n b α.val Q α.property⟩
  left_inv r := by
    rcases r with ⟨α, r⟩
    exact congrArg (Sigma.mk α)
      (PathDecoratedRay.ext_history _ _ (Subsingleton.elim _ _))
  right_inv _ := Subtype.ext rfl

/-- Shared incoming decorated rays, partitioned by their source half-plane,
are exactly the explicit incoming fiber over an arbitrary commutative semiring.
Ray existence requires a nonzero coefficient and nonzero spatial degree. Vertical
incoming degrees are included; stationary sections remain separate. -/
def incomingSlabChartRayEquiv (Q : ℝ × ℝ) :
    (Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q) ≃
      IncomingSlabBrokenLine c n b Q :=
  (incomingSlabChartEndpointEquiv c n b Q).trans (incomingSlabChartEquiv c n b Q)

/-- The incoming comparison preserves the entire affine ray and incoming tail. -/
theorem incomingSlabChartRayEquiv_ray (Q : ℝ × ℝ)
    (z : Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q) :
    (incomingSlabChartRayEquiv c n b Q z).ray = z.2.2.ray := by
  rw [IncomingSlabBrokenLine.ray_eq_straight, z.2.ray_eq_straight]

/-- The common ray carries the original whole incoming homogeneous monomial. -/
theorem IncomingSlabChartRay.decoration_zero (α : IncomingSlabChartIndex c n b)
    (Q : ℝ × ℝ) (r : IncomingSlabChartRay c n b α Q) :
    r.decoration = single ((n.natAbs : ℤ), b) c := by
  rw [PathDecoratedRay.decoration_def, Path.homogeneousHistory_nil, LinearMap.id_apply]

open Classical in
/-- Reindexing the explicit incoming sum gives the evaluation over the actual
common decorated fibers, with whole coefficients and no spurious zero rays. -/
theorem incomingSlabWeightedEvaluation_eq_sum_decoratedRays (Q : ℝ × ℝ) :
    incomingSlabWeightedEvaluation c n b Q =
      let := Fintype.ofFinite
        (Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q)
      ∑ z : Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q,
        z.2.decoration := by
  classical
  let := Fintype.ofFinite
    (Σ α : IncomingSlabChartIndex c n b, IncomingSlabChartRay c n b α Q)
  rw [incomingSlabWeightedEvaluation_def]
  exact (Fintype.sum_equiv (incomingSlabChartRayEquiv c n b Q) _ _
    (fun z => z.2.decoration_zero c n b z.1 Q)).symm

end Mei.FocusFocus
