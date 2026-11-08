/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Basic

/-!
# Constant incoming sections

A zero-momentum incoming coefficient contributes a constant incoming section, rather than a proper
path on the noncompact half-line. A `ConstantIncomingSection` is a homogeneous matching family of
the chamber coefficients whose momenta all vanish. Matching at a face uses the chosen total lift of
its graded correspondence; inadmissible input would be discarded by that lift, so every source
degree is required to be admissible.

At an endpoint in a chamber's region, off every face and away from the singular set, `stationary`
realizes the section by the constant path on `Iic 0`. Unlike `BrokenLine`, this presentation has no
properness field: a nonempty constant-valued path into a T1 base is proper only when its source is
compact. Its weighted evaluation is the corresponding chamber coefficient. Compatibility with the
face transfer follows from the matching condition.

The construction implements the separate constant-section case of Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public section

open Set

universe uS uD uM uF

namespace Mei

variable {R B V : Type*} [Semiring R] [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {D : BrokenLineData.{uS, uD, uM, uF} R B V}

/-- A homogeneous matching family of chamber coefficients with zero spatial velocity. This is the
stationary counterpart of a proper incoming tail. Zero coefficients are allowed. -/
structure ConstantIncomingSection (D : BrokenLineData.{uS, uD, uM, uF} R B V) where
  /-- The homogeneous degree in each chamber. -/
  degree : ∀ u, D.Degree u
  /-- The coefficient in each chamber. -/
  decoration : ∀ u, D.coefficient u
  /-- Every coefficient is homogeneous of its chamber's degree. -/
  decoration_mem : ∀ u, decoration u ∈ D.grading u (degree u)
  /-- Every chamber's degree has zero spatial velocity. -/
  momentum_eq_zero : ∀ u, D.momentum u (degree u) = 0
  /-- Every source degree is admitted by every face, so its chosen lift is not discarded. -/
  admissible : ∀ {u v} (e : D.Face u v), degree u ∈ D.admissibleLeft e
  /-- The coefficients match under the total transfer of every face correspondence. -/
  matching : ∀ {u v} (e : D.Face u v),
    (D.span e).totalTransfer (decoration u) = decoration v

namespace ConstantIncomingSection

variable (s : ConstantIncomingSection D)

/-- Evaluation of a constant incoming section in a chamber. -/
def weightedEvaluation (u : D.State) : D.coefficient u := s.decoration u

/-- The chamber evaluations of a constant incoming section match across every face. -/
theorem totalTransfer_weightedEvaluation {u v : D.State} (e : D.Face u v) :
    (D.span e).totalTransfer (s.weightedEvaluation u) = s.weightedEvaluation v :=
  s.matching e

/-- a constant realization of `s` at an endpoint admitted by a chamber. No properness condition is
imposed on the constant path. -/
structure Realization (s : ConstantIncomingSection D) where
  /-- The chamber containing the endpoint. -/
  state : D.State
  /-- The common value of the constant path. -/
  endpoint : B
  /-- The endpoint lies in the region of its chamber. -/
  endpoint_mem_region : endpoint ∈ D.region state
  /-- The endpoint lies off every face. -/
  endpoint_off_faces : endpoint ∉ D.faceSupport
  /-- The endpoint avoids the singular set. -/
  endpoint_not_mem_singular : endpoint ∉ D.singular

/-- The constant path representing a stationary realization. -/
def Realization.path {s : ConstantIncomingSection D} (r : s.Realization) :
    Iic (0 : ℝ) → B := fun _ => r.endpoint

theorem Realization.path_apply (r : s.Realization) (t : Iic (0 : ℝ)) : r.path t = r.endpoint := by
  simp [Realization.path]

/-- The constant path is continuous, but is deliberately not required to be proper. -/
theorem Realization.continuous_path {s : ConstantIncomingSection D} (r : s.Realization) :
    Continuous r.path := continuous_const

/-- The whole constant path lies in the source of the chamber's chart. -/
theorem Realization.path_mem_chart_source (r : s.Realization) (t : Iic (0 : ℝ)) :
    r.path t ∈ (D.chart r.state).source :=
  D.region_subset_source _ r.endpoint_mem_region

/-- A constant realization has zero affine velocity. -/
theorem Realization.chart_path_sub_velocity (r : s.Realization) (t t' : Iic (0 : ℝ)) :
    D.chart r.state (r.path t) = D.chart r.state (r.path t') -
      ((t : ℝ) - t') • D.momentum r.state (s.degree r.state) := by
  simp [Realization.path_apply, s.momentum_eq_zero]

/-- The weighted evaluation of a constant realization is the section's coefficient in its
chamber. -/
def Realization.weightedEvaluation (r : s.Realization) : D.coefficient r.state :=
  s.weightedEvaluation r.state

/-- Realize a constant incoming section by the constant path at an admitted endpoint. -/
def stationary (u : D.State) (Q : B) (hQ : Q ∈ D.region u)
    (hF : Q ∉ D.faceSupport) (hS : Q ∉ D.singular) : s.Realization where
  state := u
  endpoint := Q
  endpoint_mem_region := hQ
  endpoint_off_faces := hF
  endpoint_not_mem_singular := hS

/-- The stationary realization lies in the prescribed chamber. -/
@[simp]
theorem state_stationary (u : D.State) (Q : B) (hQ : Q ∈ D.region u)
    (hF : Q ∉ D.faceSupport) (hS : Q ∉ D.singular) :
    (s.stationary u Q hQ hF hS).state = u := (rfl)

/-- The stationary realization has the prescribed endpoint. -/
@[simp]
theorem endpoint_stationary (u : D.State) (Q : B) (hQ : Q ∈ D.region u)
    (hF : Q ∉ D.faceSupport) (hS : Q ∉ D.singular) :
    (s.stationary u Q hQ hF hS).endpoint = Q := (rfl)

/-- The stationary constructor gives the prescribed constant path. -/
@[simp]
theorem path_stationary (u : D.State) (Q : B) (hQ : Q ∈ D.region u)
    (hF : Q ∉ D.faceSupport) (hS : Q ∉ D.singular) (t : Iic (0 : ℝ)) :
    (s.stationary u Q hQ hF hS).path t = Q := by
  simp only [Realization.path_apply, endpoint_stationary]

@[simp]
theorem weightedEvaluation_stationary (u : D.State) (Q : B) (hQ : Q ∈ D.region u)
    (hF : Q ∉ D.faceSupport) (hS : Q ∉ D.singular) :
    (state_stationary s u Q hQ hF hS) ▸
      (s.stationary u Q hQ hF hS).weightedEvaluation = s.decoration u := by
  unfold Realization.weightedEvaluation weightedEvaluation
  rfl

/-- In a presentation without faces, any zero-momentum family of homogeneous coefficients is a
constant incoming section, including a zero coefficient. -/
def ofNoFaces (hF : ∀ u v, IsEmpty (D.Face u v)) (degree : ∀ u, D.Degree u)
    (decoration : ∀ u, D.coefficient u)
    (decoration_mem : ∀ u, decoration u ∈ D.grading u (degree u))
    (momentum_eq_zero : ∀ u, D.momentum u (degree u) = 0) : ConstantIncomingSection D where
  degree := degree
  decoration := decoration
  decoration_mem := decoration_mem
  momentum_eq_zero := momentum_eq_zero
  admissible := fun {u v} => (hF u v).elim
  matching := fun {u v} => (hF u v).elim

/-- The face-free constructor has the prescribed chamber degrees. -/
@[simp]
theorem degree_ofNoFaces (hF : ∀ u v, IsEmpty (D.Face u v))
    (degree : ∀ u, D.Degree u) (decoration : ∀ u, D.coefficient u)
    (decoration_mem : ∀ u, decoration u ∈ D.grading u (degree u))
    (momentum_eq_zero : ∀ u, D.momentum u (degree u) = 0) (u : D.State) :
    (ofNoFaces hF degree decoration decoration_mem momentum_eq_zero).degree u = degree u := (rfl)

/-- The face-free constructor has the prescribed chamber decorations. -/
@[simp]
theorem decoration_ofNoFaces (hF : ∀ u v, IsEmpty (D.Face u v))
    (degree : ∀ u, D.Degree u) (decoration : ∀ u, D.coefficient u)
    (decoration_mem : ∀ u, decoration u ∈ D.grading u (degree u))
    (momentum_eq_zero : ∀ u, D.momentum u (degree u) = 0) (u : D.State) :
    (ofNoFaces hF degree decoration decoration_mem momentum_eq_zero).decoration u =
      decoration u := (rfl)

/-- Without faces, stationary weighted evaluation at a chamber is the prescribed coefficient. -/
@[simp]
theorem weightedEvaluation_ofNoFaces (hF : ∀ u v, IsEmpty (D.Face u v))
    (degree : ∀ u, D.Degree u) (decoration : ∀ u, D.coefficient u)
    (decoration_mem : ∀ u, decoration u ∈ D.grading u (degree u))
    (momentum_eq_zero : ∀ u, D.momentum u (degree u) = 0) (u : D.State) :
    (ofNoFaces hF degree decoration decoration_mem momentum_eq_zero).weightedEvaluation u =
      decoration u := by
  simp [weightedEvaluation, ofNoFaces]

end ConstantIncomingSection

end Mei
