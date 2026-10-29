/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Rational
public import Mei.Geometry.Convex.Polyhedron.Rational.Ray

/-!
# Incoming-ray constraints on backward endpoint domains

After the last selected backward encounter, the incoming segment continues along
an unbounded ray. Its open part must avoid every active wall, and it must eventually
lie in the specified incoming source. Adding these conditions to a backward
itinerary preserves rational semilinearity when the velocities are lattice vectors,
the walls and source are closed rational-normal polyhedra, and the incoming vector
is a recession direction of the source. Thus the resulting endpoint domains admit
the existing finite disjoint decomposition into locally closed polyhedra.

The point at ray parameter zero is excluded from avoidance: it may be the last
recorded wall encounter. With no selected encounters, it is the endpoint itself.
The vector `w` points backwards, so the forward incoming velocity is `-w`.
These are geometric incoming-segment constraints, independent of coefficients;
finite segments, nonzero decorations and their propagation require their own laws.

We use `backwardPoint`, rational pullback, open-ray encounter domains and the
recession criterion for eventual source admission. Backward endpoint
parameterization follows Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg
models*, §4 (arXiv:2205.07753v2).
-/

public section

namespace Mei.Convex

variable {V κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin n → V)
  (P : Fin n → Set V) (w : V) (C : Set V) (W : κ → Set V)

/-- The selected backward domain with wall avoidance on the open incoming ray
and eventual admission of that ray to the incoming source. -/
def backwardIncomingDomain : Set V :=
  {Q | Q ∈ backwardDomain f c v P ∧
    (∀ b (t : ℝ), 0 < t → backwardPoint f c v (Fin.last n) Q + t • w ∉ W b) ∧
    ∀ᶠ t : ℝ in Filter.atTop, backwardPoint f c v (Fin.last n) Q + t • w ∈ C}

/-- Membership records the selected encounters, open-ray avoidance and source
admission, including for an empty selected itinerary. -/
@[simp]
theorem mem_backwardIncomingDomain (Q : V) :
    Q ∈ backwardIncomingDomain f c v P w C W ↔
      Q ∈ backwardDomain f c v P ∧
        (∀ b (t : ℝ), 0 < t → backwardPoint f c v (Fin.last n) Q + t • w ∉ W b) ∧
        ∀ᶠ t : ℝ in Filter.atTop, backwardPoint f c v (Fin.last n) Q + t • w ∈ C :=
  Iff.rfl

/-- Incoming constraints retain all selected support and positive-time conditions. -/
theorem backwardIncomingDomain_subset_backwardDomain :
    backwardIncomingDomain f c v P w C W ⊆ backwardDomain f c v P :=
  fun _ hQ => hQ.1

/-- With no wall supports and unrestricted source, there are no incoming constraints. -/
@[simp]
theorem backwardIncomingDomain_univ_empty :
    backwardIncomingDomain f c v P w Set.univ (fun _ : κ => ∅) =
      backwardDomain f c v P := by
  ext Q
  simp only [mem_backwardIncomingDomain, Set.mem_empty_iff_false, not_false_eq_true,
    implies_true, Set.mem_univ, Filter.eventually_true, and_self, and_true]

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i} [Finite κ]

/-- The unbounded incoming-segment constraints preserve rational semilinearity.
No transversality, genericity, nonemptiness or nonzero-vector assumption is needed.
In particular, the finite disjoint locally closed decomposition applies. -/
theorem isRationalSemilinear_backwardIncomingDomain
    (u : Fin n → N) (q : N)
    (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
    (hP : ∀ j, IsRationalSemilinear h (P j))
    (hC : IsRationalNormalPolyhedron h C) (hq : i q ∈ Set.recessionCone C)
    (hW : ∀ b, IsRationalNormalPolyhedron h (W b)) :
    IsRationalSemilinear h
      (backwardIncomingDomain f c (fun j => i (u j)) P (i q) C W) := by
  let X := backwardPoint f c (fun j => i (u j)) (Fin.last n)
  have hX := isRationalLinearMap_backwardPoint f c u hf (Fin.last n)
  have havoid : IsRationalSemilinear h
      (⋂ b, X ⁻¹' {x : V | ∃ t : ℝ, 0 < t ∧ x + t • i q ∈ W b}ᶜ) :=
    IsRationalSemilinear.iInter fun b =>
      (((hW b).isLocallyClosedPolyhedron_posRay q).isRationalSemilinear.compl).preimage X hX
  have hsource : IsRationalSemilinear h
      (X ⁻¹' {x : V | ∀ᶠ t : ℝ in Filter.atTop, x + t • i q ∈ C}) :=
    ((hC.eventually_add_smul_mem q hq).preimage X hX).isLocallyClosedPolyhedron.isRationalSemilinear
  convert (isRationalSemilinear_backwardDomain f c u hf hP).inter
    (havoid.inter hsource) using 1
  ext Q
  simp only [mem_backwardIncomingDomain, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and, X]

end Mei.Convex
