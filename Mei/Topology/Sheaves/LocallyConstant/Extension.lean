/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Topology.Sheaves.LocallyConstant
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Extending sections of locally constant sheaves

Let `F` be a sheaf of types with bijective restrictions to nonempty preconnected subopens of
small neighborhoods, on a locally connected space. Restriction of its sections to a dense open
subset is injective. Consequently a section on a dense open subset `G ⊆ U` extends to `U`,
necessarily uniquely, as soon as it extends to some neighborhood of each point of `U`.

Restriction from `U` to an open subset `O` is bijective when every point of `U` has
arbitrarily small preconnected neighborhoods meeting `O` in nonempty preconnected sets. In a
real vector space this holds when the points of `U` outside `O` lie in affine subspaces of
codimension at least two; see `Mei.Topology.Sheaves.LocallyConstant.FacetDescent`.

Gluing uses Mathlib's `TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types`, and connected
neighborhoods come from `LocallyConnectedSpace.open_connected_basis`.
-/

public section

open CategoryTheory TopologicalSpace Opposite Topology

open TopCat.Presheaf (restrict_restrict)

universe u v

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : X.Sheaf (Type v))

/-- Sections of a sheaf of types that agree near every point are equal. This is the proof of
Mathlib's `TopCat.Presheaf.IsSheaf.section_ext`, which requires the universe of the values to be
that of the space. -/
private theorem section_ext {U : Opens X} {s t : F.presheaf.obj (op U)}
    (h : ∀ x ∈ U, ∃ (N : Opens X) (hN : N ≤ U), x ∈ N ∧
      F.presheaf.map (homOfLE hN).op s = F.presheaf.map (homOfLE hN).op t) :
    s = t := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  choose N hN hxN H using fun x : U => h x.1 x.2
  refine (hF.isSheafFor (.ofArrows N fun x => homOfLE (hN x)) ?_).isSeparatedFor.ext ?_
  · exact fun x hx => ⟨N ⟨x, hx⟩, homOfLE (hN _), Sieve.ofArrows_mk _ _ _, hxN _⟩
  · rintro _ _ ⟨x⟩
    exact H x

variable [F.HasLocallyBijectivePreconnectedRestrictions]

/-- Every point has a neighborhood `W` such that restriction between nonempty preconnected
opens `P ≤ N ≤ W` is bijective. -/
theorem exists_bijective_restrictions_of_le (x : X) :
    ∃ W : Opens X, x ∈ W ∧ ∀ (N P : Opens X) (hPN : P ≤ N), N ≤ W →
      (P : Set X).Nonempty → IsPreconnected (N : Set X) → IsPreconnected (P : Set X) →
        Function.Bijective (F.presheaf.map (homOfLE hPN).op) := by
  obtain ⟨W, hxW, hW⟩ := HasLocallyBijectivePreconnectedRestrictions.exists_bijective_restrictions
    (F := F) x
  refine ⟨W, hxW, fun N P hPN hNW hP hcN hcP => ?_⟩
  have hN := hW N hNW (hP.mono hPN) hcN
  have hcomp : F.presheaf.map (homOfLE hPN).op ∘ F.presheaf.map (homOfLE hNW).op =
      F.presheaf.map (homOfLE (hPN.trans hNW)).op :=
    funext fun s => restrict_restrict (CC := fun T => T) (F := F.presheaf) hPN hNW s
  rw [← Function.Bijective.of_comp_iff _ hN, hcomp]
  exact hW P (hPN.trans hNW) hP hcP

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
  rw [dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf),
    dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf),
    ← dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf) hPG hGU,
    ← dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf) hPG hGU, hst]

/-- On a locally connected space, a section over a dense open subset `G` of `U` extends to `U`
if it extends to a neighborhood of every point of `U`; the extension is unique. -/
theorem existsUnique_extension_of_subset_closure {G U : Opens X} (hGU : G ≤ U)
    (hdense : (U : Set X) ⊆ closure (G : Set X)) (s : F.presheaf.obj (op G))
    (hloc : ∀ x ∈ U, ∃ (N : Opens X) (t : F.presheaf.obj (op N)), x ∈ N ∧
      F.presheaf.map (homOfLE (inf_le_left : N ⊓ G ≤ N)).op t =
        F.presheaf.map (homOfLE (inf_le_right : N ⊓ G ≤ G)).op s) :
    ∃! u : F.presheaf.obj (op U), F.presheaf.map (homOfLE hGU).op u = s := by
  -- Restriction to the dense part is injective on every open subset of `U`.
  have hinj {O : Opens X} (hOU : O ≤ U) :
      Function.Injective (F.presheaf.map (homOfLE (inf_le_left : O ⊓ G ≤ O)).op) :=
    F.map_injective_of_subset_closure _ fun z hz => O.isOpen.inter_closure ⟨hz, hdense (hOU hz)⟩
  suffices h : ∃ u : F.presheaf.obj (op U), F.presheaf.map (homOfLE hGU).op u = s by
    obtain ⟨u, hu⟩ := h
    exact ⟨u, hu, fun u' hu' =>
      F.map_injective_of_subset_closure hGU hdense (hu'.trans hu.symm)⟩
  choose N t hxN ht using fun x : U => hloc x.1 x.2
  -- Glue the local extensions, restricted to `U`.
  let N' : U → Opens X := fun x => N x ⊓ U
  let t' : ∀ x, F.presheaf.obj (op (N' x)) := fun x =>
    F.presheaf.map (homOfLE (inf_le_left : N' x ≤ N x)).op (t x)
  -- Each restricted extension still restricts to `s` on the dense part.
  have ht' (x : U) : F.presheaf.map (homOfLE (inf_le_left : N' x ⊓ G ≤ N' x)).op (t' x) =
      F.presheaf.map (homOfLE (inf_le_right : N' x ⊓ G ≤ G)).op s := by
    have h := congrArg (F.presheaf.map (homOfLE
      (inf_le_inf_right G inf_le_left : N' x ⊓ G ≤ N x ⊓ G)).op) (ht x)
    simp only [t', dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf)] at h ⊢
    exact h
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf N' t' := by
    intro x y
    apply hinj (inf_le_left.trans inf_le_right : N' x ⊓ N' y ≤ U)
    unfold Opens.infLELeft Opens.infLERight
    simp only [dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf)]
    rw [← dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (N' x ⊓ N' y) ⊓ G ≤ N' x ⊓ G) (inf_le_left : N' x ⊓ G ≤ N' x),
      ← dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          (N' x ⊓ N' y) ⊓ G ≤ N' y ⊓ G) (inf_le_left : N' y ⊓ G ≤ N' y),
      ht', ht', dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf),
      dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
        restrict_restrict (CC := fun T => T) (F := F.presheaf)]
  obtain ⟨g, hg, -⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types F.property t' hcompat
  have hcover : U ≤ iSup N' := fun x hx =>
    Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩, hx⟩
  refine ⟨F.presheaf.map (homOfLE hcover).op g, section_ext F fun x hx => ?_⟩
  -- Near each point of `G`, both sections are restrictions of the local extension.
  obtain ⟨y, rfl⟩ : ∃ y : U, y.1 = x := ⟨⟨x, hGU hx⟩, rfl⟩
  refine ⟨N' y ⊓ G, inf_le_right, ⟨⟨hxN y, hGU hx⟩, hx⟩, ?_⟩
  rw [dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf), ← ht' y, ← hg y]
  unfold Opens.leSupr
  rw [dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf),
    dsimp% [Presheaf.restrictOpen, Presheaf.restrict]
      restrict_restrict (CC := fun T => T) (F := F.presheaf)]

/-- On a locally connected space, restriction of sections from `U` to an open subset `O` is
bijective if every point of `U` has arbitrarily small preconnected open neighborhoods whose
intersections with `O` are nonempty and preconnected. -/
theorem map_bijective_of_isPreconnected_inter {O U : Opens X} (hOU : O ≤ U)
    (hO : ∀ x ∈ U, ∀ W ∈ 𝓝 x, ∃ N : Opens X, x ∈ N ∧ (N : Set X) ⊆ W ∧
      IsPreconnected (N : Set X) ∧ IsPreconnected ((N : Set X) ∩ O) ∧
        ((N : Set X) ∩ O).Nonempty) :
    Function.Bijective (F.presheaf.map (homOfLE hOU).op) := by
  have hdense : (U : Set X) ⊆ closure (O : Set X) := fun x hx =>
    mem_closure_iff_nhds.mpr fun W hW => by
      obtain ⟨N, -, hNW, -, -, z, hzN, hzO⟩ := hO x hx W hW
      exact ⟨z, hNW hzN, hzO⟩
  refine ⟨F.map_injective_of_subset_closure hOU hdense, fun s => ?_⟩
  refine (F.existsUnique_extension_of_subset_closure hOU hdense s fun x hx => ?_).exists
  obtain ⟨W, hxW, hW⟩ := F.exists_bijective_restrictions_of_le x
  obtain ⟨N, hxN, hNW, hcN, hcNO, hne⟩ := hO x hx W (W.isOpen.mem_nhds hxW)
  obtain ⟨t, ht⟩ := (hW N (N ⊓ O) inf_le_left hNW hne hcN hcNO).surjective
    (F.presheaf.map (homOfLE (inf_le_right : N ⊓ O ≤ O)).op s)
  exact ⟨N, t, hxN, ht⟩

end TopCat.Sheaf
