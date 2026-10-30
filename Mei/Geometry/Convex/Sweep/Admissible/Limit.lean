/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Convex.Sweep.Degeneration

/-!
# Limits of admissible incoming rays

The compact-open closure of an admissible backward family consists exactly of
the extended paths at endpoints in the closure of its full admissible domain.
These paths retain their endpoints, all selected closed-support incidences and
nonnegative elapsed times. Their incoming tails remain admitted by a
rational-normal polyhedral source. In particular, taking a limit does not lose
the incoming source even though its admission threshold can depend on the path.

The path family over the closed endpoint domain is proper. Each individual
limiting half-line is also proper when its incoming direction is nonzero,
even if several encounters collapse. Boundary paths need not avoid the walls
or singular sets, and are not asserted to be transverse realizations.

We use `backwardPath`, the local characterization of
`AdmissibleRayRealization`, `backwardPath_eventually_mem_iff`, and
`IsRationalNormalPolyhedron.eventually_add_smul_mem`. Individual half-line
properness is supplied by `isProperMap_backwardPath_restrict_Iic`.
The backward parameterization is that of
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set Filter Topology

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V)
  (W : J → Set V) (S : K → Set V) (C : Set V)

/-- Closing the full admissible domain retains all selected closed supports
and weakens strict time order to nonnegative elapsed times. -/
theorem closure_admissibleBackwardDomain_subset_weakBackwardDomain
    (hP : ∀ j, IsClosed (P j)) :
    closure (admissibleBackwardDomain f c v P W S C) ⊆
      weakBackwardDomain f c (fun j => v j.castSucc) P :=
  closure_subset_weakBackwardDomain f c _
    (admissibleBackwardDomain_subset_backwardDomain f c v P W S C) hP

/-- Every limiting elapsed time is nonnegative, even if the selected supports
are not closed. -/
theorem backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain
    {Q : V} (hQ : Q ∈ closure (admissibleBackwardDomain f c v P W S C)) (j : Fin n) :
    0 ≤ backwardTime f c (fun j => v j.castSucc) j Q :=
  backwardTime_nonneg_of_mem_closure f c _
    (admissibleBackwardDomain_subset_backwardDomain f c v P W S C) hQ j

/-- The extended path at an admitted endpoint is the actual admissible ray. -/
@[simp]
theorem AdmissibleRayRealization.toContinuousMap_eq_backwardPath {Q : V}
    (r : AdmissibleRayRealization f c v P W S C Q) :
    r.ray.toContinuousMap = backwardPath f c v Q := by
  obtain ⟨hpos, _, hr⟩ := r.eq_backwardRay
  rw [hr, backwardPath_eq_backwardRay f c v Q hpos]

/-- Endpoint limits give compact-open limits of actual admissible rays.
The limiting endpoint need not itself be admissible. -/
theorem tendsto_admissibleRayRealization {A : Type*} {l : Filter A}
    {Q : A → V} {Q₀ : V} (hQ : Tendsto Q l (𝓝 Q₀))
    (r : ∀ a, AdmissibleRayRealization f c v P W S C (Q a)) :
    Tendsto (fun a => (r a).ray.toContinuousMap) l
      (𝓝 (backwardPath f c v Q₀)) := by
  simpa only [AdmissibleRayRealization.toContinuousMap_eq_backwardPath,
    Function.comp_def] using
    (backwardPath f c v).continuous.continuousAt.tendsto.comp hQ

/-- The path family on the closed admissible endpoint domain is proper:
evaluation at time zero recovers its endpoint. This is properness of the
family in compact-open path space, without a nonzero-direction hypothesis. -/
theorem isProperMap_backwardPath_closure_admissibleBackwardDomain :
    IsProperMap (fun Q : closure (admissibleBackwardDomain f c v P W S C) =>
      backwardPath f c v Q.val) :=
  isProperMap_backwardPath_restrict f c v isClosed_closure
    (fun _ hQ => backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ)

/-- Every compact-open limiting path, and only such a path, is obtained by
extending backward propagation to the closure of the full admissible domain.
In particular there are no additional limits from escaping endpoints. -/
theorem closure_image_backwardPath_admissibleBackwardDomain :
    closure (backwardPath f c v '' admissibleBackwardDomain f c v P W S C) =
      backwardPath f c v '' closure (admissibleBackwardDomain f c v P W S C) :=
  closure_image_backwardPath f c v
    (admissibleBackwardDomain_subset_backwardDomain f c v P W S C)

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i}

/-- The incoming source persists at every boundary endpoint of the full
admissible family. Polyhedrality controls eventual admission uniformly through
the closed domain of incoming base points, without a uniform entry time. -/
theorem backwardPath_eventually_mem_of_mem_closure_admissibleBackwardDomain
    (hC : IsRationalNormalPolyhedron h C)
    {Q : V} (hQ : Q ∈ closure (admissibleBackwardDomain f c v P W S C)) :
    ∀ᶠ t : ℝ in atBot, backwardPath f c v Q t ∈ C := by
  apply backwardPath_eventually_mem_of_mem_closure f c v C hC _ hQ
  intro Q hQ
  exact (mem_backwardIncomingDomain _ _ _ _ _ _ _ _).mp
    ((mem_admissibleBackwardDomain f c v P W S C Q).mp hQ).2.1 |>.2.2

end Mei.Convex
