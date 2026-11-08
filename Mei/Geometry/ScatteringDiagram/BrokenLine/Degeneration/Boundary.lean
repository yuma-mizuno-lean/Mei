/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Support
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Incoming
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Avoidance.Stability
public import Mei.Geometry.Convex.Sweep.Singular.Stability

/-!
# Boundaries of full decorated-type domains

For polyhedral ambient walls, a regular limiting path with endpoint off
the walls has no local constraints except admission of its incoming tail.
The selected supports may be nonclosed, provided they agree locally with
their ambient walls at regular limits. Selected incidences,
strict time order, absence of unrecorded contacts, and singular avoidance all
persist on a neighborhood. The full type domain therefore agrees locally with
the source-admission domain, rather than merely containing its limiting point.

Consequently a frontier endpoint is terminal, has an actual singular contact,
or has its incoming tail in a tight tangential source face. In the last case
the defining source inequality must vary with the endpoint after backward
reconstruction: redundant constant rows do not create boundary events. These
are necessary boundary events; neither their codimensions nor admissibility of
singular boundary paths is asserted. Every path is the original complete-type
extension, retaining its whole coefficient history and incoming half-line.

The closed-family interpretation follows Carl–Pumperla–Siebert, *A tropical view
on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite O] [Finite K]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)
  (t : CutoffDecoratedType d ℳ T a v f ε k) (wall : J → O)
  (hW : ∀ j, TauCeti.IsConvexPolyhedron (W j))
  (hP : ∀ j, P j ⊆ W (wall j))
  (hlocal : ∀ j x, x ∈ closure (P j) → x ∉ singularSupport W →
    ∀ᶠ y in 𝓝 x, y ∈ W (wall j) → y ∈ P j)
  (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
  (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤ (affineSpan ℝ (W (wall j))).direction)
  (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
  (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {x | ν j x = z j})
  (hS : ∀ j, TauCeti.IsConvexPolyhedron (S j))

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)
local notation "w" => fun j : Fin t.itinerary.val.length => v (t.history.val j)
local notation "X" => backwardPoint F b w (Fin.last t.itinerary.val.length)
local notation "D" => domain c P W S C t
local notation "A" => Set.ofPred fun Q : V => ∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C

include hW hP hlocal hheight hdir hspan hS

/-- At a regular limiting path with allowed endpoint, the full domain agrees
locally with incoming-source admission. The source may be any set; only walls
and singular obstacles need to be polyhedral. -/
theorem eventually_mem_domain_iff_sourceAdmission_of_regular
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → t.path c Q s ∉ S j) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D ↔ ∀ᶠ s : ℝ in atBot, t.path c Y s ∈ C := by
  have hclosed := fun j => (hW j).isClosed
  have h0 : ∀ j, 0 ≤ backwardTime F b w j Q := by
    simpa only [Fin.snoc_castSucc] using t.backwardTime_nonneg c P W S C hQ
  have hτ (j : Fin (t.itinerary.val.length + 1)) :
      backwardParameter F b w j Q ≤ 0 := by
    simpa only [backwardParameter_zero] using
      antitone_backwardParameter F b w Q h0 (Fin.zero_le j)
  have hinc := t.mem_interior_backwardDomain_of_eventually_mem_of_mem
    c P W S C W wall hclosed hP hheight hdir hlocal hQ hoff
    (fun j => by
      simpa only [Fin.snoc_castSucc] using
        hregular (backwardParameter F b w j.succ Q) (hτ _))
  have hsing := eventually_mem_backwardSingularAvoidanceDomain F b u
    (fun j => P (t.itinerary.val.get j)) S hS
    (by simpa only [Fin.snoc_castSucc] using h0)
    (by simpa only [path_def] using havoid)
  have hlocal := t.eventually_mem_domain_iff_of_regular c P W S C wall hW
    hP hheight ν z hspan hQ hoff hregular
  simp only [Fin.snoc_castSucc] at hsing hlocal
  filter_upwards [hlocal, hsing, mem_interior_iff_mem_nhds.mp hinc]
    with Y hlocal hsing hinc
  rw [hlocal, and_iff_right hinc, and_iff_left (hsing hinc)]
  simp only [path_def, backwardPath_eventually_mem_iff, Fin.snoc_castSucc]

/-- At a regular closed type limit, belonging to the interior of the full
domain is equivalent to interior incoming-source admission. This includes
unbounded incoming tails and makes no openness assumption on the source. -/
theorem mem_interior_domain_iff_sourceAdmission_of_regular
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → t.path c Q s ∉ S j) :
    Q ∈ interior D ↔ Q ∈ interior A := by
  have he : D =ᶠ[𝓝 Q] A :=
    (t.eventually_mem_domain_iff_sourceAdmission_of_regular c P W S C wall hW hP hlocal
      hheight hdir ν z hspan hS hQ hoff hregular havoid).set_eq
  exact he.mem_interior_iff

variable {ι : Type*} [Finite ι] (g : ι → V →ᴬ[ℝ] ℝ)

local notation "source" => Set.iInter fun j : ι => Set.ofPred fun x : V => g j x ≤ 0
local notation "Dg" => domain c P W S source t

/-- At a regular closed type limit for a polyhedral source, the full-domain
frontier is characterized exactly by a tight tangential source row whose
pullback along the incoming-base map is nonconstant. -/
theorem mem_frontier_domain_iff_source_face_of_regular
    {Q : V} (hQ : Q ∈ closure Dg) (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → t.path c Q s ∉ S j) :
    Q ∈ frontier Dg ↔
      ∃ j, (g j).linear (v 0) = 0 ∧ g j (X Q) = 0 ∧
        ((g j).comp X).toAffineMap.linear ≠ 0 := by
  have hsource : ∀ᶠ s : ℝ in atBot, t.path c Q s ∈ source := by
    apply t.path_eventually_mem_of_isConvexPolyhedron c P W S source _ hQ
    rw [iInter_ofPred]
    exact TauCeti.isConvexPolyhedron_setOf_forall g
  have hi := t.mem_interior_domain_iff_sourceAdmission_of_regular c P W S source
    wall hW hP hlocal hheight hdir ν z hspan hS hQ hoff hregular havoid
  have hf := t.mem_frontier_sourceAdmission_iff c g Q
  have hfront : Q ∈ frontier Dg ↔ Q ∉ interior Dg :=
    ⟨fun h => h.2, fun h => ⟨hQ, h⟩⟩
  have hsourcemem : Q ∈ {Y : V | ∀ᶠ s : ℝ in atBot, t.path c Y s ∈ source} := hsource
  rw [hfront, hi, ← mem_frontier_iff_notMem_interior hsourcemem, hf,
    and_iff_right hsource]

/-- Every boundary of the full type domain has a terminal wall contact, a
wall-singular contact, a prescribed singular contact, or an incoming tail in a
tight tangential source face. Contact times are nonpositive and concern the
whole extended path. No boundary admissibility or codimension is assumed. -/
theorem mem_frontier_domain_imp_terminal_or_singular_or_source_face
    {Q : V} (hQ : Q ∈ frontier Dg) :
    (∃ j, Q ∈ W j) ∨
      (∃ s ≤ 0, t.path c Q s ∈ singularSupport W) ∨
      (∃ j s, s ≤ 0 ∧ t.path c Q s ∈ S j) ∨
      ∃ j, (g j).linear (v 0) = 0 ∧ ((g j).comp X).toAffineMap.linear ≠ 0 ∧
        ∀ᶠ s : ℝ in atBot, t.path c Q s ∈ {x ∈ source | g j x = 0} := by
  by_cases ht : ∃ j, Q ∈ W j
  · exact Or.inl ht
  right
  by_cases hw : ∃ s ≤ 0, t.path c Q s ∈ singularSupport W
  · exact Or.inl hw
  right
  by_cases hs : ∃ j s, s ≤ 0 ∧ t.path c Q s ∈ S j
  · exact Or.inl hs
  right
  have hoff : ∀ j, Q ∉ W j := by simpa only [not_exists] using ht
  have hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W := by
    simpa only [not_exists, not_and] using hw
  have havoid : ∀ j s, s ≤ 0 → t.path c Q s ∉ S j := by
    simpa only [not_exists, not_and] using hs
  have hi := t.mem_interior_domain_iff_sourceAdmission_of_regular c P W S source
    wall hW hP hlocal hheight hdir ν z hspan hS (frontier_subset_closure hQ) hoff hregular havoid
  exact t.path_eventually_mem_source_face_of_mem_closure c g P W S
    (frontier_subset_closure hQ) (fun h => hQ.2 (hi.mpr h))

end Mei.CutoffDecoratedType
