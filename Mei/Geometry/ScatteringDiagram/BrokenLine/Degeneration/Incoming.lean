/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Incoming
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Basic

/-!
# Tangential source events in closed decorated-type families

For each complete decorated type, the incoming-source condition has a closed
endpoint domain. A strictly increasing source inequality makes this domain empty;
otherwise only inequalities tangent to the incoming direction constrain it.
At a boundary endpoint its extended path has an incoming tail entirely in a tight
tangential source face. The corresponding inequality must vary with the endpoint,
so constant zero rows do not give spurious events.

The paths are the existing `CutoffDecoratedType.path` extensions, with all
encounters and whole coefficient histories retained. This classifies boundaries
of source admission, rather than asserting admissibility of boundary paths or
classifying the other support, avoidance and time-order conditions.

We use `backwardPath_eventually_mem_iff`, its incoming affine germ, and the
polyhedral source-admission boundary criterion. The interpretation of incoming
source faces in closed broken-line families follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (t : CutoffDecoratedType d ℳ T a v f ε k)
  [Finite ι] (g : ι → V →ᴬ[ℝ] ℝ)

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)
local notation "X" => backwardPoint F b (fun j : Fin t.itinerary.val.length => v (t.history.val j))
  (Fin.last t.itinerary.val.length)
local notation "C" => Set.iInter fun j : ι => Set.ofPred fun x : V => g j x ≤ 0
local notation "D" => Set.ofPred fun Q : V => ∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C

/-- The full incoming tail is admitted precisely when its affine base satisfies
every tangential source inequality. No time-order or admissibility assumption on
the endpoint is needed. -/
theorem path_eventually_mem_polyhedron_iff
    (hv : ∀ j, (g j).linear (v 0) ≤ 0) (Q : V) :
    (∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C) ↔
      ∀ j, (g j).linear (v 0) = 0 → g j (X Q) ≤ 0 := by
  rw [path_def, backwardPath_eventually_mem_iff]
  simp only [Fin.snoc_last, Fin.snoc_castSucc, mem_iInter, mem_ofPred_eq]
  exact AffineMap.eventually_forall_apply_add_smul_le_iff_of_nonpos
    (fun j => (g j).toAffineMap) (v 0) hv _

/-- The incoming-source condition is closed in endpoint space, including when
the source is lower-dimensional or the incoming velocity is zero. -/
theorem isClosed_sourceAdmission : IsClosed D := by
  have hC : TauCeti.IsConvexPolyhedron C := by
    have he : C = {x | ∀ j, g j x ≤ 0} := by ext x; simp
    rw [he]
    exact TauCeti.isConvexPolyhedron_setOf_forall g
  simpa only [path_def, backwardPath_eventually_mem_iff, Fin.snoc_last,
    Fin.snoc_castSucc, Set.preimage_ofPred_eq] using
      (hC.eventually_add_smul_mem (v 0)).isClosed.preimage (X).continuous

/-- Source-admission boundary endpoints are exactly the admitted endpoints
where a tangential row is tight and nonconstant after backward reconstruction.
This includes tangential source faces and excludes redundant constant rows. -/
theorem mem_frontier_sourceAdmission_iff (Q : V) :
    Q ∈ frontier D ↔
      (∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C) ∧
        ∃ j, (g j).linear (v 0) = 0 ∧ g j (X Q) = 0 ∧
          ((g j).comp X).toAffineMap.linear ≠ 0 := by
  have he : D = {Q : V | ∀ᶠ s : ℝ in atTop, ∀ j, g j (X Q + s • v 0) ≤ 0} := by
    ext Q
    rw [mem_ofPred_eq, path_def, backwardPath_eventually_mem_iff]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, mem_iInter, mem_ofPred_eq]
  have hsource := congrArg (fun A : Set V => Q ∈ A) he
  simp only [mem_ofPred_eq] at hsource
  rw [he, hsource]
  exact ContinuousAffineMap.mem_frontier_eventually_forall_apply_add_smul_le_comp_iff
    g X (v 0) Q

/-- At a source-admission boundary the limiting incoming tail lies entirely in
a tight source face tangent to its velocity. The row varies with the endpoint;
the tail is the original global incoming germ, even for collapsed encounters. -/
theorem path_eventually_mem_source_face_of_mem_frontier
    {Q : V} (hQ : Q ∈ frontier D) :
    ∃ j, (g j).linear (v 0) = 0 ∧ ((g j).comp X).toAffineMap.linear ≠ 0 ∧
      ∀ᶠ s : ℝ in atBot, t.path c Q s ∈ {x ∈ C | g j x = 0} := by
  obtain ⟨hsource, j, hjv, hjQ, hne⟩ :=
    (t.mem_frontier_sourceAdmission_iff c g Q).mp hQ
  refine ⟨j, hjv, hne, ?_⟩
  have htail := backwardPath_eventuallyEq_incoming F b u Q
  simp only [Fin.snoc_last, Fin.snoc_castSucc] at htail
  filter_upwards [hsource, htail] with s hs hpath
  refine ⟨hs, ?_⟩
  rw [path_def, hpath, ContinuousAffineMap.apply_add_smul, hjv, hjQ, zero_mul, add_zero]

/-- In a closed chart of the actual admissible type domain, loss of interior
source admission forces the original incoming tail into a tangential source face.
No rationality of the source rows or nonzero-velocity hypothesis is needed. -/
theorem path_eventually_mem_source_face_of_mem_closure
    {K I : Type*} (P : J → Set V) (W : I → Set V) (S : K → Set V)
    {Q : V} (hQ : Q ∈ closure (domain c P W S C t)) (hnot : Q ∉ interior D) :
    ∃ j, (g j).linear (v 0) = 0 ∧ ((g j).comp X).toAffineMap.linear ≠ 0 ∧
      ∀ᶠ s : ℝ in atBot, t.path c Q s ∈ {x ∈ C | g j x = 0} := by
  have hsub : domain c P W S C t ⊆ D := by
    intro Y hY
    rw [mem_ofPred_eq, path_def, backwardPath_eventually_mem_iff]
    rw [domain_def, mem_admissibleBackwardDomain] at hY
    exact ((mem_backwardIncomingDomain _ _ _ _ _ _ _ _).mp hY.2.1).2.2
  have hsource := closure_minimal hsub (t.isClosed_sourceAdmission c g) hQ
  exact t.path_eventually_mem_source_face_of_mem_frontier c g
    ((mem_frontier_iff_notMem_interior hsource).mpr hnot)

/-- Eventual admission to any convex polyhedral source persists at limiting
endpoints of a complete type. The finite affine-inequality presentation need not
have rational normals, and no lattice or nonzero incoming velocity is required. -/
theorem path_eventually_mem_of_isConvexPolyhedron
    {K I : Type*} (P : J → Set V) (W : I → Set V) (S : K → Set V)
    (C₀ : Set V) (hC : TauCeti.IsConvexPolyhedron C₀)
    {Q : V} (hQ : Q ∈ closure (domain c P W S C₀ t)) :
    ∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C₀ := by
  obtain ⟨n, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hC
  have hclosed : IsClosed {Q : V | ∀ᶠ s : ℝ in atBot,
      t.path c Q s ∈ {x | ∀ j, g j x ≤ 0}} := by
    simpa only [mem_iInter, mem_ofPred_eq] using t.isClosed_sourceAdmission c g
  apply closure_minimal ?_ hclosed hQ
  intro Y hY
  rw [mem_ofPred_eq, path_def, backwardPath_eventually_mem_iff]
  rw [domain_def, mem_admissibleBackwardDomain] at hY
  exact ((mem_backwardIncomingDomain _ _ _ _ _ _ _ _).mp hY.2.1).2.2

end Mei.CutoffDecoratedType
