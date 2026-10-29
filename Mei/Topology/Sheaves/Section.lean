/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Local equality and gluing of sheaf sections

The local equality principle for type-valued sheaves, with independent universes for the
space and values, together with unique gluing when restrictions to overlaps are injective.
The local equality proof is adapted from Mathlib's `TopCat.Presheaf.IsSheaf.section_ext`.
-/

public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (F : X.Presheaf (Type v))

/-- Agreement of two sections on a common open passes to every smaller open. -/
theorem restrict_eq_of_le {M P Q R : Opens X} (hMP : M ≤ P) (hMQ : M ≤ Q)
    (hRM : R ≤ M) {s : F.obj (op P)} {t : F.obj (op Q)}
    (h : F.map (homOfLE hMP).op s = F.map (homOfLE hMQ).op t) :
    F.map (homOfLE (hRM.trans hMP)).op s =
      F.map (homOfLE (hRM.trans hMQ)).op t := by
  -- Normalize composition with the functor law and the preorder category's composition rule.
  simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using
    congrArg (F.map (homOfLE hRM).op) h

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : X.Sheaf (Type v))

/-- Sections of a sheaf of types that agree near every point are equal. This is the proof of
Mathlib's `TopCat.Presheaf.IsSheaf.section_ext`, which requires the universe of the values to be
that of the space. -/
theorem section_ext {U : Opens X} {s t : F.presheaf.obj (op U)}
    (h : ∀ x ∈ U, ∃ (N : Opens X) (hN : N ≤ U), x ∈ N ∧
      F.presheaf.map (homOfLE hN).op s = F.presheaf.map (homOfLE hN).op t) :
    s = t := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  choose N hN hxN H using fun x : U => h x.1 x.2
  refine (hF.isSheafFor (.ofArrows N fun x => homOfLE (hN x)) ?_).isSeparatedFor.ext ?_
  · exact fun x hx => ⟨N ⟨x, hx⟩, homOfLE (hN _), Sieve.ofArrows_mk _ _ _, hxN _⟩
  · rintro _ _ ⟨x⟩
    exact H x

/-- A section that extends near every point extends uniquely if restriction from every
subopen to its overlap with the domain is injective. This gluing criterion does not require
local connectedness or a local-constancy condition on the sheaf. -/
theorem existsUnique_extension_of_injective {G U : Opens X} (hGU : G ≤ U)
    (hinj : ∀ (P : Opens X), P ≤ U →
      Function.Injective (F.presheaf.map (homOfLE (inf_le_left : P ⊓ G ≤ P)).op))
    (s : F.presheaf.obj (op G))
    (hloc : ∀ x ∈ U, ∃ (N : Opens X) (t : F.presheaf.obj (op N)), x ∈ N ∧
      F.presheaf.map (homOfLE (inf_le_left : N ⊓ G ≤ N)).op t =
        F.presheaf.map (homOfLE (inf_le_right : N ⊓ G ≤ G)).op s) :
    ∃! u : F.presheaf.obj (op U), F.presheaf.map (homOfLE hGU).op u = s := by
  suffices h : ∃ u : F.presheaf.obj (op U), F.presheaf.map (homOfLE hGU).op u = s by
    obtain ⟨u, hu⟩ := h
    refine ⟨u, hu, fun u' hu' => hinj U le_rfl ?_⟩
    exact F.presheaf.restrict_eq_of_le hGU hGU inf_le_right (hu'.trans hu.symm)
  choose N t hxN ht using fun x : U => hloc x.1 x.2
  -- Glue the local extensions, restricted to `U`.
  let N' : U → Opens X := fun x => N x ⊓ U
  let t' : ∀ x, F.presheaf.obj (op (N' x)) := fun x =>
    F.presheaf.map (homOfLE (inf_le_left : N' x ≤ N x)).op (t x)
  -- Each restricted extension still restricts to `s` on the dense part.
  have ht' (x : U) : F.presheaf.map (homOfLE (inf_le_left : N' x ⊓ G ≤ N' x)).op (t' x) =
      F.presheaf.map (homOfLE (inf_le_right : N' x ⊓ G ≤ G)).op s := by
    simpa only [t', ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using
      F.presheaf.restrict_eq_of_le inf_le_left inf_le_right
        (inf_le_inf_right G inf_le_left : N' x ⊓ G ≤ N x ⊓ G) (ht x)
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf N' t' := by
    intro x y
    apply hinj (N' x ⊓ N' y) (inf_le_left.trans inf_le_right)
    have hx := F.presheaf.restrict_eq_of_le inf_le_left inf_le_right
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (N' x ⊓ N' y) ⊓ G ≤ N' x ⊓ G) (ht' x)
    have hy := F.presheaf.restrict_eq_of_le inf_le_left inf_le_right
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (N' x ⊓ N' y) ⊓ G ≤ N' y ⊓ G) (ht' y)
    simpa only [Opens.infLELeft, Opens.infLERight, ← Functor.map_comp_apply, ← op_comp,
      homOfLE_comp] using hx.trans hy.symm
  obtain ⟨g, hg, -⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types F.property t' hcompat
  have hcover : U ≤ iSup N' := fun x hx =>
    Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩, hx⟩
  refine ⟨F.presheaf.map (homOfLE hcover).op g, section_ext F fun x hx => ?_⟩
  -- Near each point of `G`, both sections are restrictions of the local extension.
  obtain ⟨y, rfl⟩ : ∃ y : U, y.1 = x := ⟨⟨x, hGU hx⟩, rfl⟩
  refine ⟨N' y ⊓ G, inf_le_right, ⟨⟨hxN y, hGU hx⟩, hx⟩, ?_⟩
  have h := congrArg (F.presheaf.map (homOfLE (inf_le_left : N' y ⊓ G ≤ N' y)).op) (hg y)
  have h' : F.presheaf.map (homOfLE (inf_le_left.trans (le_iSup N' y))).op g =
      F.presheaf.map (homOfLE (inf_le_left : N' y ⊓ G ≤ N' y)).op (t' y) := by
    simpa only [Opens.leSupr, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using h
  simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using h'.trans (ht' y)

end TopCat.Sheaf
