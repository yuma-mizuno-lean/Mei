/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Rescaling
public import Mei.Geometry.Convex.Polyhedron.Incoming

/-!
# Rescaling the incoming-source constraint

The unbounded incoming tail of a backward itinerary eventually enters a fixed
polyhedral source precisely when its last reconstructed point belongs to the
source's ray-admission domain. This domain is polyhedral even when the source
has irrational normals or the incoming direction is zero.

At small positive scales about a common center of the selected hyperplanes,
source admission becomes membership in the tangent cone of this admission
domain. One scale works on each bounded endpoint set. The original global
source is retained: it is the admission domain, rather than the source itself,
that must be linearized. A center outside the admission domain admits no nearby
scaled tails. At an admitted center, exactly the tight tangential source rows
constrain the rescaled last point.

These are constraints on the full incoming half-line, including for collapsed
itineraries. No boundary path is asserted to be admissible. The interpretation
of source constraints in closed broken-line charts follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (v : Fin (n + 1) → V) (z : V)
  (C : Set V) (hC : TauCeti.IsConvexPolyhedron C)
  {K : Set V} (hK : Bornology.IsBounded K)

local notation "X" => backwardPoint f 0 (fun j : Fin n => v (Fin.castSucc j)) (Fin.last n)
local notation "D" => Set.ofPred fun x : V => ∀ᶠ s : ℝ in atTop, x + s • v (Fin.last n) ∈ C

include hC hK in
/-- Source admission for the entire incoming half-line rescales to the tangent
cone of its ray-admission domain, uniformly on bounded endpoint sets. A center
not admitted by the original global source gives no nearby admitted tail. -/
theorem eventually_forall_backwardPath_eventually_mem_add_smul_iff :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K,
      (∀ᶠ s : ℝ in atBot, backwardPath f (fun j => f j z) v (z + r • Q) s ∈ C) ↔
        z ∈ D ∧ X Q ∈ posTangentConeAt D z := by
  have hD := hC.eventually_add_smul_mem (v (Fin.last n))
  have he := eventually_forall_add_smul_mem_iff
    (fun _ : Unit => D) (fun _ => hD) z ((X).isBounded_image hK)
  filter_upwards [he] with r hr
  intro Q hQ
  rw [backwardPath_eventually_mem_iff, backwardPoint_add_smul]
  exact hr _ (mem_image_of_mem X hQ) ()

include hK in
/-- For a finite inequality presentation and an admitted center, only source
rows that are both tangential and tight survive rescaling. The center may be
outside the source: strictly decreasing rows are eventually satisfied anyway. -/
theorem eventually_forall_backwardPath_eventually_mem_add_smul_iff_active
    {ι : Type*} [Finite ι] (g : ι → V →ᴬ[ℝ] ℝ)
    (hz : ∀ᶠ s : ℝ in atTop, ∀ j, g j (z + s • v (Fin.last n)) ≤ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K,
      (∀ᶠ s : ℝ in atBot, ∀ j,
        g j (backwardPath f (fun j => f j z) v (z + r • Q) s) ≤ 0) ↔
        ∀ j, (g j).linear (v (Fin.last n)) = 0 → g j z = 0 →
          (g j).contLinear (X Q) ≤ 0 := by
  have he := eventually_forall_backwardPath_eventually_mem_add_smul_iff f v z
    {x | ∀ j, g j x ≤ 0} (TauCeti.isConvexPolyhedron_setOf_forall g) hK
  filter_upwards [he] with r hr
  intro Q hQ
  rw [hr Q hQ, and_iff_right hz,
    ContinuousAffineMap.posTangentConeAt_eventually_forall_apply_add_smul_le_eq g
      (v (Fin.last n)) z hz, mem_ofPred_eq]

end Mei.Convex
