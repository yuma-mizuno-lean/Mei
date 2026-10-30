/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Cylinder
public import Mei.Geometry.Convex.Sweep.Admissible

/-!
# Admissible rays through cylinder walls

Projection identifies the actual admissible ray fibers of a cylinder itinerary
with those of its projected itinerary, once all forgotten segment directions and
the forgotten endpoint are prescribed. The equivalence preserves the whole
projected path and every encounter parameter, including encounters whose bend
is invisible after projection. Wall avoidance, singular avoidance and eventual
incoming-source admission are retained.

This combines the cylinder endpoint-domain identities with
`AdmissibleRayRealization.eq_backwardRay`. The geometric comparison follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set

variable {V W J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (w : Fin (n + 1) → W)
  (P : Fin n → Set V) (A : J → Set V) (S : K → Set V) (C : Set V)

local notation "F" => fun j => ContinuousLinearMap.comp (f j) (ContinuousLinearMap.fst ℝ V W)
local notation "vw" => fun j => (v j, w j)
local notation "Pc" => fun j => Prod.fst ⁻¹' P j
local notation "Ac" => fun j => Prod.fst ⁻¹' A j
local notation "Sc" => fun j => Prod.fst ⁻¹' S j

/-- All admissibility constraints for cylinder walls and a cylinder source pull
back along projection, without restrictions on forgotten directions. -/
@[simp]
theorem admissibleBackwardDomain_cylinder :
    admissibleBackwardDomain F c vw Pc Ac Sc (Prod.fst ⁻¹' C) =
      Prod.fst ⁻¹' admissibleBackwardDomain f c v P A S C := by
  ext Q
  simp only [mem_admissibleBackwardDomain, backwardAvoidanceDomain_cylinder,
    backwardIncomingDomain_cylinder, backwardSingularAvoidanceDomain_cylinder, mem_preimage]

/-- Prescribing the forgotten directions and endpoint gives a unique admissible
cylinder lift of every projected transverse ray. Tangent or inadmissible
itineraries have empty fibers on both sides. -/
def admissibleRayCylinderEquiv (Q : V × W) :
    AdmissibleRayRealization F c vw Pc Ac Sc (Prod.fst ⁻¹' C) Q ≃
      AdmissibleRayRealization f c v P A S C Q.1 :=
  equivOfSubsingletonOfSubsingleton
    (fun r => admissibleRayRealization f c v P A S C Q.1
      (by simpa only [admissibleBackwardDomain_cylinder, mem_preimage] using
        r.mem_admissibleBackwardDomain))
    (fun r => admissibleRayRealization F c vw Pc Ac Sc (Prod.fst ⁻¹' C) Q
      (by simpa only [admissibleBackwardDomain_cylinder, mem_preimage] using
        r.mem_admissibleBackwardDomain))

/-- Projection of the actual continuous ray, including its incoming half-line,
is the ray of the projected realization. -/
@[simp]
theorem admissibleRayCylinderEquiv_ray (Q : V × W)
    (r : AdmissibleRayRealization F c vw Pc Ac Sc (Prod.fst ⁻¹' C) Q) :
    (admissibleRayCylinderEquiv f c v w P A S C Q r).ray =
      r.ray.map (AffineMap.fst : V × W →ᵃ[ℝ] V) := by
  obtain ⟨hpos, _, hr⟩ := r.eq_backwardRay
  obtain ⟨hp, _, he⟩ := (admissibleRayCylinderEquiv f c v w P A S C Q r).eq_backwardRay
  rw [hr, he]
  symm
  apply backwardRay_map_fst
  simpa only [backwardTime_apply] using hp

/-- The equivalence keeps the actual encounter times, also when projection
erases the corresponding change of direction. -/
@[simp]
theorem admissibleRayCylinderEquiv_parameter (Q : V × W)
    (r : AdmissibleRayRealization F c vw Pc Ac Sc (Prod.fst ⁻¹' C) Q) :
    (admissibleRayCylinderEquiv f c v w P A S C Q r).parameter = r.parameter := by
  obtain ⟨_, hr, _⟩ := r.eq_backwardRay
  obtain ⟨_, he, _⟩ := (admissibleRayCylinderEquiv f c v w P A S C Q r).eq_backwardRay
  funext j
  rw [he, hr, backwardParameter_fst]

end Mei.Convex
