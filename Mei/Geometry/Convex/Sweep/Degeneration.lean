/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Realization
public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification
public import Mathlib.Topology.CompactOpen

/-!
# Closed degeneration charts for backward itineraries

The hinge formula for a backward itinerary defines a continuous family in the
compact-open topology on paths. At strictly positive elapsed times it is the
existing finite affine ray. The formula also makes sense at limits where times
vanish: encounters can coincide, while their positions and parameters retain
their affine formulas. No crossing is sent to infinity at a finite endpoint.

Every rational semilinear subdomain of a selected itinerary admits finitely many
disjoint charts that are relative interiors of closed rational-normal polyhedra.
On their closures the selected support incidences persist and elapsed times are
nonnegative. Endpoint evaluation on a closed chart is proper. Extra semilinear
validity constraints may be imposed before taking these charts; their boundary
points need not satisfy strict avoidance conditions.

We use `backwardRay`, its bend and encounter formulas, sign-cell decomposition
and relative interiors, and Mathlib's `ContinuousMap.curry`. The backward
parameterization follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2). This construction concerns
geometric charts; coefficient decorations and finiteness of the set of
itineraries are separate requirements.
-/

public noncomputable section

namespace Mei.Convex

open Set Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin (n + 1) → V)

/-- The hinge extension of the backward realization, continuous in the endpoint
for the compact-open topology on paths. Outside the weak time-order domain the
formula is totalized and need not have its given endpoint at time zero. -/
def backwardPath : C(V, C(ℝ, V)) :=
  ContinuousMap.curry ⟨fun z =>
    (∑ j : Fin n, max (backwardParameter f c (fun j => v j.castSucc) j.succ z.1 - z.2) 0 •
      (v j.succ - v j.castSucc)) - z.2 • v 0 + z.1, by
        apply Continuous.add
        · apply Continuous.sub
          · apply continuous_finsetSum
            intro j _
            exact (((backwardParameter f c (fun j => v j.castSucc) j.succ).continuous.comp
              continuous_fst).sub continuous_snd).max continuous_const |>.smul continuous_const
          · exact continuous_snd.smul continuous_const
        · exact continuous_fst⟩

/-- The extended family uses the same finite hinges even when encounter times coincide. -/
@[simp]
theorem backwardPath_apply (Q : V) (t : ℝ) :
    backwardPath f c v Q t =
      (∑ j : Fin n, max (backwardParameter f c (fun j => v j.castSucc) j.succ Q - t) 0 •
        (v j.succ - v j.castSucc)) - t • v 0 + Q := (rfl)

/-- On a strict itinerary the extended path is the actual finite affine ray,
including its affine continuation beyond time zero. -/
theorem backwardPath_eq_backwardRay (Q : V)
    (hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q) (t : ℝ) :
    backwardPath f c v Q t = backwardRay f c v Q hpos t := by
  classical
  rw [backwardPath_apply, FiniteAffineRay.eval_def, bends_backwardRay,
    direction_backwardRay, endpoint_backwardRay]
  rw [← Finsupp.sum_finsetSum_index (fun b => smul_zero (max (b - t) 0))
    (fun b x y => smul_add (max (b - t) 0) x y)]
  simp only [Finsupp.sum_single_index
    (h := fun b (x : V) => max (b - t) 0 • x) (smul_zero _), vadd_eq_add]

/-- Converging endpoints give compact-open convergence of the actual strict
realizations to the extended path, even when some limiting elapsed times vanish. -/
theorem tendsto_backwardRay {A : Type*} {l : Filter A} {Q : A → V} {Q₀ : V}
    (hQ : Tendsto Q l (𝓝 Q₀))
    (hpos : ∀ a j, 0 < backwardTime f c (fun j => v j.castSucc) j (Q a)) :
    Tendsto (fun a => (⟨backwardRay f c v (Q a) (hpos a),
      (backwardRay f c v (Q a) (hpos a)).continuous⟩ : C(ℝ, V))) l
      (𝓝 (backwardPath f c v Q₀)) := by
  have he (a : A) : (⟨backwardRay f c v (Q a) (hpos a),
      (backwardRay f c v (Q a) (hpos a)).continuous⟩ : C(ℝ, V)) =
      backwardPath f c v (Q a) := by
    ext t
    exact (backwardPath_eq_backwardRay f c v (Q a) (hpos a) t).symm
  simp_rw [he]
  exact (backwardPath f c v).continuous.continuousAt.tendsto.comp hQ

variable (P : Fin n → Set V)

/-- At any boundary endpoint approached by strict realizations, the extended path
still passes through every affine encounter point at its limiting parameter.
Several of those parameters may be equal. -/
theorem backwardPath_apply_parameter_of_mem_closure {Q : V}
    (hQ : Q ∈ closure (backwardDomain f c (fun j => v j.castSucc) P))
    (j : Fin (n + 1)) :
    backwardPath f c v Q (backwardParameter f c (fun j => v j.castSucc) j Q) =
      backwardPoint f c (fun j => v j.castSucc) j Q := by
  have he : EqOn
      (fun Q => backwardPath f c v Q (backwardParameter f c (fun j => v j.castSucc) j Q))
      (backwardPoint f c (fun j => v j.castSucc) j)
      (backwardDomain f c (fun j => v j.castSucc) P) := by
    intro Q hQ
    dsimp only
    have hpos := fun j => ((mem_backwardDomain _ _ _ _ Q).mp hQ j).1
    rw [backwardPath_eq_backwardRay f c v Q hpos]
    exact backwardRay_apply_parameter f c v Q hpos j
  exact he.closure
    ((backwardPath f c v).continuous.eval
      (backwardParameter f c (fun j => v j.castSucc) j).continuous)
    (backwardPoint f c (fun j => v j.castSucc) j).continuous hQ

/-- Degenerate paths retain their endpoint at parameter zero. -/
theorem backwardPath_apply_zero_of_mem_closure {Q : V}
    (hQ : Q ∈ closure (backwardDomain f c (fun j => v j.castSucc) P)) :
    backwardPath f c v Q 0 = Q := by
  simpa using backwardPath_apply_parameter_of_mem_closure f c v P hQ 0

/-- The limiting path retains the entire incoming affine half-line. Its origin
is the last encounter, even if several encounters have collapsed to that point. -/
theorem backwardPath_apply_incoming_of_mem_closure {Q : V}
    (hQ : Q ∈ closure (backwardDomain f c (fun j => v j.castSucc) P))
    {s : ℝ} (hs : 0 ≤ s) :
    backwardPath f c v Q (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - s) =
      backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q + s • v (Fin.last n) := by
  have he : EqOn
      (fun Q => backwardPath f c v Q
        (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - s))
      (fun Q => backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q + s • v (Fin.last n))
      (backwardDomain f c (fun j => v j.castSucc) P) := by
    intro Q hQ
    dsimp only
    have hpos := fun j => ((mem_backwardDomain _ _ _ _ Q).mp hQ j).1
    rw [backwardPath_eq_backwardRay f c v Q hpos,
      backwardRay_apply_incoming f c v Q hpos _ (sub_le_self _ hs), sub_sub_cancel]
  exact he.closure
    ((backwardPath f c v).continuous.eval
      ((backwardParameter f c (fun j => v j.castSucc) (Fin.last n)).continuous.sub
        continuous_const))
    ((backwardPoint f c (fun j => v j.castSucc) (Fin.last n)).continuous.add
      continuous_const) hQ

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i}

/-- Any rational semilinear validity subdomain has finite closed degeneration
charts. Their interiors partition precisely that domain; their closures retain
nonnegative times and all selected closed-support incidences. The endpoint maps
on the closed charts are proper, without boundedness assumptions. -/
theorem exists_backwardClosedCharts {D : Set V}
    (hD : IsRationalSemilinear h D)
    (hvalid : D ⊆ backwardDomain f c (fun j => v j.castSucc) P)
    (hclosed : ∀ j, IsClosed (P j)) :
    ∃ (κ : Type) (_ : Finite κ) (K : κ → Set V),
      (∀ a, (K a).Nonempty ∧ IsRationalNormalPolyhedron h (K a) ∧
        K a ⊆ closure D ∧ K a ⊆ weakBackwardDomain f c (fun j => v j.castSucc) P ∧
          IsProperMap (fun Q : K a => (Q : V))) ∧
      (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (K a))
        (intrinsicInterior ℝ (K b))) ∧ ⋃ a, intrinsicInterior ℝ (K a) = D := by
  obtain ⟨κ, hκ, K, hK, hdisj, hcover⟩ := hD.exists_disjoint_intrinsicInteriors
  refine ⟨κ, hκ, K, ?_, hdisj, hcover⟩
  intro a
  have hweak : closure D ⊆ weakBackwardDomain f c (fun j => v j.castSucc) P :=
    closure_minimal
      (hvalid.trans (backwardDomain_subset_weakBackwardDomain f c _ P))
      (isClosed_weakBackwardDomain f c _ hclosed)
  exact ⟨(hK a).1, (hK a).2.1, (hK a).2.2, (hK a).2.2.trans hweak,
    (hK a).2.1.isClosed.isProperMap_subtypeVal⟩

end Mei.Convex
