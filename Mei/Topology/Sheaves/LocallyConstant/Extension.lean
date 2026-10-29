/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Topology.Sheaves.LocallyConstant
public import Mei.Topology.Sheaves.Section
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Extending sections of locally constant sheaves

Let `F` be a sheaf of types with bijective restrictions to nonempty preconnected subopens of
small neighborhoods, on a locally connected space. Restriction of its sections to a dense open
subset is injective. Consequently a section on a dense open subset `G ⊆ U` extends to `U`,
necessarily uniquely, as soon as it extends to some neighborhood of each point of `U`.

Restriction from `U` to an open subset `O` is bijective when every point of `U` has
arbitrarily small preconnected neighborhoods meeting `O` in nonempty preconnected sets. In a
finite-dimensional real normed space this holds when the points of `U` outside `O` lie in a
countable family of affine subspaces of codimension at least two; see
`Mei.Topology.Sheaves.LocallyConstant.FacetDescent`.

Gluing uses Mathlib's `TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types`, and connected
neighborhoods come from `LocallyConnectedSpace.open_connected_basis`.
-/

public section

open CategoryTheory TopologicalSpace Opposite Topology

universe u v

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : X.Sheaf (Type v))

variable [F.HasLocallyBijectivePreconnectedRestrictions]

variable [LocallyConnectedSpace X]

/-- On a locally connected space, restriction of sections to a dense open subset is
injective. -/
theorem map_injective_of_subset_closure {G U : Opens X} (hGU : G ≤ U)
    (hdense : (U : Set X) ⊆ closure (G : Set X)) :
    Function.Injective (F.presheaf.map (homOfLE hGU).op) := by
  intro s t hst
  refine section_ext F fun x hx => ?_
  obtain ⟨W, hxW, hW⟩ := F.exists_bijective_restrictions_of_le x
  obtain ⟨N, ⟨hNo, hxN, hcN⟩, hNWU⟩ := (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp
    (Filter.inter_mem (W.isOpen.mem_nhds hxW) (U.isOpen.mem_nhds hx))
  obtain ⟨y, hyN, hyG⟩ := mem_closure_iff.mp (hdense hx) N hNo hxN
  let N' : Opens X := ⟨N, hNo⟩
  let P : Opens X := ⟨connectedComponentIn (N ∩ G) y, (hNo.inter G.isOpen).connectedComponentIn⟩
  have hPN : P ≤ N' := fun z hz => (connectedComponentIn_subset _ _ hz).1
  have hPG : P ≤ G := fun z hz => (connectedComponentIn_subset _ _ hz).2
  have hNU : N' ≤ U := fun z hz => (hNWU hz).2
  refine ⟨N', hNU, hxN, (hW N' P hPN (fun z hz => (hNWU hz).1)
    ⟨y, mem_connectedComponentIn ⟨hyN, hyG⟩⟩ hcN.isPreconnected
    isPreconnected_connectedComponentIn).injective ?_⟩
  simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using
    F.presheaf.restrict_eq_of_le hGU hGU hPG hst

/-- On a locally connected space, a section over a dense open subset `G` of `U` extends to `U`
if it extends to a neighborhood of every point of `U`; the extension is unique. -/
theorem existsUnique_extension_of_subset_closure {G U : Opens X} (hGU : G ≤ U)
    (hdense : (U : Set X) ⊆ closure (G : Set X)) (s : F.presheaf.obj (op G))
    (hloc : ∀ x ∈ U, ∃ (N : Opens X) (t : F.presheaf.obj (op N)), x ∈ N ∧
      F.presheaf.map (homOfLE (inf_le_left : N ⊓ G ≤ N)).op t =
        F.presheaf.map (homOfLE (inf_le_right : N ⊓ G ≤ G)).op s) :
    ∃! u : F.presheaf.obj (op U), F.presheaf.map (homOfLE hGU).op u = s := by
  apply existsUnique_extension_of_injective F hGU _ s hloc
  intro P hPU
  apply F.map_injective_of_subset_closure inf_le_left
  exact fun z hz => P.isOpen.inter_closure ⟨hz, hdense (hPU hz)⟩

omit [LocallyConnectedSpace X] in
/-- Restriction of sections from `U` to an open subset `O` is bijective if every point of `U`
has arbitrarily small preconnected open neighborhoods whose
intersections with `O` are nonempty and preconnected. -/
theorem map_bijective_of_isPreconnected_inter {O U : Opens X} (hOU : O ≤ U)
    (hO : ∀ x ∈ U, ∀ W ∈ 𝓝 x, ∃ N : Opens X, x ∈ N ∧ (N : Set X) ⊆ W ∧
      IsPreconnected (N : Set X) ∧ IsPreconnected ((N : Set X) ∩ O) ∧
        ((N : Set X) ∩ O).Nonempty) :
    Function.Bijective (F.presheaf.map (homOfLE hOU).op) := by
  -- The supplied neighborhoods give injectivity on every subopen of `U` directly.
  have hinj {P Q : Opens X} (hPU : P ≤ U) (hQP : Q ≤ P) (hOP : O ⊓ P ≤ Q) :
      Function.Injective (F.presheaf.map (homOfLE hQP).op) := by
    intro s t hst
    refine F.section_ext fun x hx => ?_
    obtain ⟨W, hxW, hW⟩ := F.exists_bijective_restrictions_of_le x
    obtain ⟨N, hxN, hNWP, hcN, hcNO, hne⟩ := hO x (hPU hx) (W ⊓ P)
      (Filter.inter_mem (W.isOpen.mem_nhds hxW) (P.isOpen.mem_nhds hx))
    have hNP : N ≤ P := fun z hz => (hNWP hz).2
    have hNOQ : N ⊓ O ≤ Q := fun z hz => hOP ⟨hz.2, hNP hz.1⟩
    refine ⟨N, hNP, hxN,
      (hW N (N ⊓ O) inf_le_left (fun z hz => (hNWP hz).1) hne hcN hcNO).injective ?_⟩
    simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using
      F.presheaf.restrict_eq_of_le hQP hQP hNOQ hst
  refine ⟨hinj le_rfl hOU inf_le_left, fun s => ?_⟩
  refine (existsUnique_extension_of_injective F hOU (fun P hPU =>
    hinj (P := P) hPU inf_le_left (le_inf inf_le_right inf_le_left))
    s fun x hx => ?_).exists
  obtain ⟨W, hxW, hW⟩ := F.exists_bijective_restrictions_of_le x
  obtain ⟨N, hxN, hNW, hcN, hcNO, hne⟩ := hO x hx W (W.isOpen.mem_nhds hxW)
  obtain ⟨t, ht⟩ := (hW N (N ⊓ O) inf_le_left hNW hne hcN hcNO).surjective
    (F.presheaf.map (homOfLE (inf_le_right : N ⊓ O ≤ O)).op s)
  exact ⟨N, t, hxN, ht⟩

end TopCat.Sheaf
