/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Singular
public import Mei.Geometry.Affine.FiniteRay.Product

/-!
# Backward itineraries through cylinder walls

Pulling walls back along the first projection preserves the times of every
selected encounter. The forgotten coordinate directions can change independently,
including at encounters where the projected direction is unchanged. The endpoint
domains, finite-segment avoidance, incoming-source constraints and singular-set
avoidance are exactly the inverse images of the projected domains.

The realized cylinder ray projects to the original backward ray. Its forgotten
direction increments are integrated at these same encounter parameters. Thus the
projected itinerary, forgotten directions and endpoint specify its unique lift;
no nonzero projected increment or genericity assumption is needed.
Coefficient propagation and sums of degree refinements are separate questions.

We use the existing backward realization, `FiniteAffineRay.existsUnique_lift`,
and Mathlib's finite-sum evaluation API for `Finsupp`. The cylinder interpretation
follows Carl–Pumperla–Siebert, *A tropical view
on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set

variable {V W J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin n → V) (w : Fin n → W)

local notation "F" => fun j => ContinuousLinearMap.comp (f j) (ContinuousLinearMap.fst ℝ V W)
local notation "vw" => fun j => (v j, w j)

/-- The first coordinate of every cylinder encounter is the projected encounter.
The forgotten endpoint and directions do not affect it. -/
@[simp]
theorem backwardPoint_fst (j : Fin (n + 1)) (Q : V × W) :
    (backwardPoint F c vw j Q).1 = backwardPoint f c v j Q.1 := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    simp only [backwardPoint_succ_apply, Prod.fst_add, Prod.smul_fst,
      backwardTime_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ih]

/-- Cylinder and projected itineraries have the same elapsed times, also for
tangent steps and negative or zero elapsed times. -/
@[simp↓]
theorem backwardTime_fst (j : Fin n) (Q : V × W) :
    backwardTime F c vw j Q = backwardTime f c v j Q.1 := by
  simp only [backwardTime_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', backwardPoint_fst]

/-- Cylinder encounters occur at exactly the projected cumulative parameters. -/
@[simp]
theorem backwardParameter_fst (j : Fin (n + 1)) (Q : V × W) :
    backwardParameter F c vw j Q = backwardParameter f c v j Q.1 := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih => simp only [backwardParameter_succ, backwardTime_fst, ih]

/-- Pulling selected supports back to cylinders pulls back the entire strict
endpoint domain. No transversality assumption is needed for this identity. -/
@[simp]
theorem backwardDomain_cylinder (P : Fin n → Set V) :
    backwardDomain F c vw (fun j => Prod.fst ⁻¹' P j) =
      Prod.fst ⁻¹' backwardDomain f c v P := by
  ext Q
  simp only [mem_backwardDomain, mem_preimage, backwardTime_fst, backwardPoint_fst]

/-- Weak domains, including collapsed encounter intervals, also pull back exactly. -/
@[simp]
theorem weakBackwardDomain_cylinder (P : Fin n → Set V) :
    weakBackwardDomain F c vw (fun j => Prod.fst ⁻¹' P j) =
      Prod.fst ⁻¹' weakBackwardDomain f c v P := by
  ext Q
  simp only [mem_weakBackwardDomain, mem_preimage, backwardTime_fst, backwardPoint_fst]

/-- Absence of unrecorded cylinder encounters on every open finite segment is
equivalent to absence of unrecorded encounters after projection. -/
@[simp]
theorem backwardAvoidanceDomain_cylinder (P : Fin n → Set V) (S : J → Set V) :
    backwardAvoidanceDomain F c vw (fun j => Prod.fst ⁻¹' P j)
        (fun a => Prod.fst ⁻¹' S a) =
      Prod.fst ⁻¹' backwardAvoidanceDomain f c v P S := by
  ext Q
  simp only [mem_backwardAvoidanceDomain, backwardDomain_cylinder, mem_preimage,
    backwardTime_fst, Prod.fst_add, Prod.smul_fst, backwardPoint_fst]

/-- Incoming wall avoidance and eventual admission to a cylinder source are
exactly their projected conditions, with unrestricted forgotten incoming direction. -/
@[simp]
theorem backwardIncomingDomain_cylinder (P : Fin n → Set V) (S : J → Set V)
    (C : Set V) (a : V) (b : W) :
    backwardIncomingDomain F c vw (fun j => Prod.fst ⁻¹' P j) (a, b)
        (Prod.fst ⁻¹' C) (fun j => Prod.fst ⁻¹' S j) =
      Prod.fst ⁻¹' backwardIncomingDomain f c v P a C S := by
  ext Q
  simp only [mem_backwardIncomingDomain, backwardDomain_cylinder, mem_preimage,
    Prod.fst_add, Prod.smul_fst, backwardPoint_fst]

variable (u : Fin (n + 1) → V) (z : Fin (n + 1) → W)

/-- Avoiding cylinder singular sets along the whole negative half-line, including
the endpoint and recorded encounters, is equivalent to projected avoidance. -/
@[simp]
theorem backwardSingularAvoidanceDomain_cylinder (P : Fin n → Set V) (S : J → Set V) :
    backwardSingularAvoidanceDomain F c (fun j => (u j, z j))
        (fun j => Prod.fst ⁻¹' P j) (fun a => Prod.fst ⁻¹' S a) =
      Prod.fst ⁻¹' backwardSingularAvoidanceDomain f c u P S := by
  ext Q
  simp only [mem_backwardSingularAvoidanceDomain, backwardAvoidanceDomain_cylinder,
    mem_backwardIncomingDomain, backwardDomain_cylinder, mem_preimage,
    Prod.fst_add, Prod.smul_fst, backwardPoint_fst, mem_univ]

variable (Q : V × W)
  -- Positivity is in simp normal form so the projection lemmas apply automatically.
  {hpos : ∀ j, 0 < (c j - f j (backwardPoint f c (fun j => u j.castSucc) j.castSucc Q.1)) /
    f j (u j.castSucc)}

/-- Projection commutes with realization of the cylinder itinerary. In particular,
a forgotten-coordinate bend may disappear under projection. -/
@[simp↓]
theorem backwardRay_map_fst :
    (backwardRay F c (fun j => (u j, z j)) Q
      (by
        simp only [backwardTime_fst]
        simpa only [backwardTime_apply] using hpos)).map
        (AffineMap.fst : V × W →ᵃ[ℝ] V) =
      backwardRay f c u Q.1 (by simpa only [backwardTime_apply] using hpos) := by
  apply FiniteAffineRay.ext
  · simp
  · simp
  · classical
    ext t
    simp only [FiniteAffineRay.bends_map_apply, bends_backwardRay,
      Finset.sum_apply', AffineMap.fst_linear, LinearMap.fst_apply,
      Prod.fst_sum, Finsupp.single_apply, backwardParameter_fst, apply_ite,
      Prod.fst_sub, Prod.fst_zero]

/-- The lifted ray has precisely the original path as its first coordinate,
at every time, including encounters and the incoming half-line. -/
@[simp↓]
theorem backwardRay_apply_fst (t : ℝ) :
    (backwardRay F c (fun j => (u j, z j)) Q
      (by
        simp only [backwardTime_fst]
        simpa only [backwardTime_apply] using hpos) t).1 =
        backwardRay f c u Q.1 (by simpa only [backwardTime_apply] using hpos) t := by
  simpa only [FiniteAffineRay.map_apply, AffineMap.coe_fst] using
    congrArg (fun β : FiniteAffineRay V V => β t)
      (backwardRay_map_fst f c u z Q (hpos := hpos))

/-- The forgotten-coordinate increments occur at the projected encounter times.
They remain present even when the corresponding projected increment is zero. -/
@[simp↓]
theorem backwardRay_map_snd_bends :
    ((backwardRay F c (fun j => (u j, z j)) Q
      (by
        simp only [backwardTime_fst]
        simpa only [backwardTime_apply] using hpos)).map
        (AffineMap.snd : V × W →ᵃ[ℝ] W)).bends =
      ∑ j : Fin n, Finsupp.single
        (backwardParameter f c (fun j => u j.castSucc) j.succ Q.1)
        (z j.succ - z j.castSucc) := by
  classical
  ext t
  simp only [FiniteAffineRay.bends_map_apply, bends_backwardRay,
    Finset.sum_apply', AffineMap.snd_linear, LinearMap.snd_apply,
    Prod.snd_sum, Finsupp.single_apply, backwardParameter_fst, apply_ite,
    Prod.snd_sub, Prod.snd_zero]

/-- A projected itinerary and a forgotten direction history integrate uniquely
with any prescribed forgotten endpoint. The bend formula retains all recorded
encounters, including ones erased by the first projection. -/
theorem existsUnique_backwardRay_cylinder_lift :
    ∃! δ : FiniteAffineRay (V × W) (V × W),
      δ.map (AffineMap.fst : V × W →ᵃ[ℝ] V) =
          backwardRay f c u Q.1 (by simpa only [backwardTime_apply] using hpos) ∧
        δ.endpoint.2 = Q.2 ∧ δ.direction.2 = z 0 ∧
        ∀ t, (δ.bends t).2 =
          (∑ j : Fin n, Finsupp.single
            (backwardParameter f c (fun j => u j.castSucc) j.succ Q.1)
            (z j.succ - z j.castSucc)) t := by
  let γ := (backwardRay F c (fun j => (u j, z j)) Q
    (by
        simp only [backwardTime_fst]
        simpa only [backwardTime_apply] using hpos)).map
      (AffineMap.snd : V × W →ᵃ[ℝ] W)
  have he : γ.bends = ∑ j : Fin n, Finsupp.single
      (backwardParameter f c (fun j => u j.castSucc) j.succ Q.1)
      (z j.succ - z j.castSucc) := backwardRay_map_snd_bends f c u z Q (hpos := hpos)
  simpa only [he] using
    (backwardRay f c u Q.1 (by simpa only [backwardTime_apply] using hpos)).existsUnique_lift
      Q.2 (z 0) γ.bends γ.bend_neg

end Mei.Convex
