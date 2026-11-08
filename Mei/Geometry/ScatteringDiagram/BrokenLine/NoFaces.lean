/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Basic
public import Mei.Geometry.Affine.FiniteRay.Basic

/-!
# Broken lines in a diagram without faces

In a single chart on a real normed space `V` with no faces, every broken line is
straight: it has no crossings, and its path is the half-line `t ↦ Q - t • μ` ending at
`Q` with the momentum `μ` of its degree. For a nonzero homogeneous incoming coefficient
of nonzero momentum whose half-line avoids the singular set there is exactly one broken
line at `Q` with this incoming datum, and its final decoration is the incoming
coefficient.

This is the empty-diagram example of Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, Definition 2.10 (arXiv:1503.06183v5), for the common
carrier `BrokenLine`.
-/

public section

open Set

universe uS uD uM uF

namespace Mei.BrokenLine

variable {R V : Type*} [Semiring R] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {D : BrokenLineData.{uS, uD, uM, uF} R V V}

section

variable (hF : ∀ u v, IsEmpty (D.Face u v)) (hchart : ∀ u x, D.chart u x = x)
  (hregion : ∀ u, D.region u = univ)

include hF in
/-- Without faces no point lies on a face. -/
theorem _root_.Mei.BrokenLineData.faceSupport_eq_empty : D.faceSupport = ∅ :=
  eq_empty_of_forall_notMem fun _ h => by
    obtain ⟨u, v, e, -⟩ := BrokenLineData.mem_faceSupport.mp h
    exact (hF u v).false e

include hF in
/-- Without faces a broken line has no crossings. -/
theorem numEvents_eq_zero_of_noFaces (b : BrokenLine D) : b.numEvents = 0 := by
  by_contra h
  exact (hF _ _).false (b.face ⟨0, Nat.pos_of_ne_zero h⟩)

include hF hchart in
/-- Without faces and with identity charts, a broken line with endpoint `Q` and last momentum
`μ` is the half-line `t ↦ Q - t • μ`. -/
theorem path_eq_of_noFaces (b : BrokenLine D) (t : Iic (0 : ℝ)) :
    b.path t = b.endpoint - (t : ℝ) • D.momentum b.finalState b.finalDegree := by
  set μ := D.momentum (b.state (Fin.last b.numEvents))
    (b.degree (Fin.last b.numEvents)) with hμ
  have hfinal : μ = D.momentum b.finalState b.finalDegree :=
    hμ.trans b.momentum_final_def.symm
  have : IsEmpty (Fin b.numEvents) := by
    rw [numEvents_eq_zero_of_noFaces hF b]
    infer_instance
  have hint (s : Iic (0 : ℝ)) (hs : (s : ℝ) < 0) :
      (s : ℝ) ∈ segmentInterior b.eventTime (Fin.last b.numEvents) :=
    mem_segmentInterior.mpr ⟨hs, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  have haff (s t : Iic (0 : ℝ)) (hs : (s : ℝ) < 0) (ht : (t : ℝ) < 0) :
      b.path t = b.path s - ((t : ℝ) - s) • μ := by
    have h := b.interior_affine _ s t (hint s hs) (hint t ht)
    simpa only [hchart] using h
  let c : V := b.path ⟨-1, by norm_num⟩ + (-1 : ℝ) • μ
  have hc (s : ℝ) (hs : s < 0) : b.path ⟨s, hs.le⟩ + s • μ = c := by
    rw [haff ⟨-1, by norm_num⟩ ⟨s, hs.le⟩ (by norm_num) hs]
    simp only [c, sub_smul]
    abel
  let φ : ℝ → V := fun s => b.path ⟨min s 0, min_le_right _ _⟩ + min s 0 • μ
  have hφ : Continuous φ :=
    (b.proper.continuous.comp
      ((continuous_id.min continuous_const).subtype_mk fun _ => min_le_right _ _)).add
      ((continuous_id.min continuous_const).smul continuous_const)
  have hφc : EqOn φ (fun _ => c) (closure (Iio (0 : ℝ))) := by
    refine EqOn.closure (s := Iio 0) (fun s hs => ?_) hφ continuous_const
    have hs' : s < 0 := hs
    simp only [φ, min_eq_left hs'.le]
    exact hc s hs'
  have h0 : b.endpoint = c := by
    have := hφc (show (0 : ℝ) ∈ closure (Iio (0 : ℝ)) by rw [closure_Iio]; exact le_rfl)
    rw [b.endpoint_def]
    simpa only [φ, min_self, zero_smul, add_zero] using this
  rw [← hfinal]
  rcases t.property.lt_or_eq with ht | ht
  · rw [← h0] at hc
    rw [eq_sub_iff_add_eq]
    exact hc t ht
  · rw [ht, zero_smul, sub_zero, b.endpoint_def]
    exact congrArg b.path (Subtype.ext ht)

variable (u : D.State) (p : D.Degree u) (a : D.coefficient u) (hp : a ∈ D.grading u p)
  (ha : a ≠ 0) (hμ : D.momentum u p ≠ 0) (Q : V)
  (hQ : ∀ t : ℝ, t ≤ 0 → Q - t • D.momentum u p ∉ D.singular)

include hF hchart hregion hp ha hμ hQ in
/-- In a single chart without faces, the straight half-line ending at `Q` with the momentum of a
nonzero homogeneous incoming coefficient avoiding the singular set is the unique broken line at
`Q` with that incoming datum. -/
theorem existsUnique_of_noFaces :
    ∃! b : BrokenLine D, b.endpoint = Q ∧ b.incoming = ⟨u, p, a⟩ := by
  let μ := D.momentum u p
  have hvelocity : (FiniteAffineRay.straight Q μ).incomingDirection ≠ 0 := by
    simpa only [FiniteAffineRay.incomingDirection_straight] using hμ
  have hpath (t : ℝ) : FiniteAffineRay.straight Q μ t = Q - t • μ := by
    rw [FiniteAffineRay.straight_apply, vadd_eq_add, neg_smul, add_comm, sub_eq_add_neg]
  let b : BrokenLine D :=
    { numEvents := 0
      eventTime := Fin.elim0
      eventTime_strictMono := fun i => i.elim0
      eventTime_neg := fun i => i.elim0
      state := fun _ => u
      degree := fun _ => p
      decoration := fun _ => a
      decoration_mem := fun _ => hp
      decoration_ne_zero := fun _ => ha
      momentum_ne_zero := fun _ => hμ
      path := fun t => FiniteAffineRay.straight Q μ t
      proper := (FiniteAffineRay.straight Q μ).isProperMap_restrict_Iic hvelocity 0
      path_zero_off_faces := by
        rw [BrokenLineData.faceSupport_eq_empty hF]
        exact notMem_empty _
      path_zero_mem_region := by rw [hregion]; trivial
      avoids_singular := fun t => by
        rw [hpath]
        exact hQ t t.property
      interior_mem_region := fun _ _ _ => by rw [hregion]; trivial
      interior_affine := fun _ s t _ _ => by
        rw [hchart, hchart, hpath, hpath]
        module
      interior_off_faces := fun _ _ _ => by
        rw [BrokenLineData.faceSupport_eq_empty hF]
        exact notMem_empty _
      face := fun j => j.elim0
      event_mem_support := fun j => j.elim0
      transverse := fun j => j.elim0
      normal_velocity := fun j => j.elim0
      admissible := fun j => j.elim0
      propagate := fun j => j.elim0 }
  have hbinc : b.incoming = ⟨u, p, a⟩ := b.incoming_def
  refine ⟨b, ⟨?_, hbinc⟩, fun c ⟨hc, hinc⟩ => ?_⟩
  · simp [b, BrokenLine.endpoint_def]
  · have hmom := c.momentum_final_eq_of_numEvents_eq_zero (numEvents_eq_zero_of_noFaces hF c) hinc
    refine ext_of_numEvents_eq_zero (numEvents_eq_zero_of_noFaces hF c) rfl (funext fun t => ?_)
      (hinc.trans hbinc.symm)
    rw [path_eq_of_noFaces hF hchart c t, hc, hmom]
    exact (hpath t).symm

include hF in
/-- At a fixed incoming datum, a single broken line in a diagram without faces whose final
state is `u` (hypothesis `hu`) evaluates to its incoming coefficient. -/
theorem weightedEvaluation_eq_of_noFaces {ι : Type*} [Unique ι] (family : ι → BrokenLine D)
    {u : D.State} {p : D.Degree u} {a : D.coefficient u}
    (hfam : ∀ j, (family j).incoming = ⟨u, p, a⟩) (hu : ∀ j, (family j).finalState = u) :
    weightedEvaluation family u hu = a := by
  rw [weightedEvaluation_unique]
  obtain ⟨h, ha⟩ := (family default).exists_decorationIn_eq_of_numEvents_eq_zero
    (numEvents_eq_zero_of_noFaces hF _) (hfam default)
  exact ha

end

end Mei.BrokenLine
