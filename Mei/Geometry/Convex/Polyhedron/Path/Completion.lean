/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Restriction
public import Mei.GroupTheory.CompletedGroup.OrderedProduct

/-!
# Cutoff compatibility of wall products

For a wall family labelled in a completed group, projecting a finite active-wall path product
to a lower cutoff restricts the path to the surviving walls. This uses
`Quiver.Path.map_wallPathProduct` and `Quiver.Path.wallPathProduct_restrict`, independently of
any directed or KS presentation of the supports and coorientations.
-/

public section

noncomputable section

open Set Mei Mei.Convex CategoryTheory Opposite

universe u

namespace Quiver.Path

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {F : ℕᵒᵖ ⥤ GrpCat.{u}}

/-- Lowering the cutoff of completed wall labels projects transport and forgets exactly
the walls whose labels become the identity. -/
theorem map_wallPathProduct_projection (W : ι → Set V) (ν : ι → V →ₗ[ℝ] ℝ)
    (label : ι → completedGroup F)
    (hcomm : ∀ a b, affineSpan ℝ (W a) = affineSpan ℝ (W b) →
      Commute (label a) (label b))
    {k l : ℕ} (hkl : k ≤ l)
    [Finite (Function.mulSupport fun j => CompletedGroup.projection k (label j))]
    [Finite (Function.mulSupport fun j => CompletedGroup.projection l (label j))]
    {x y : WallComplement
      (fun j : Function.mulSupport (fun j => CompletedGroup.projection l (label j)) => W j)}
    (p : AdmissiblePLPath x y) :
    F.map (homOfLE hkl).op
        (p.wallPathProduct
          (fun j : Function.mulSupport (fun j => CompletedGroup.projection l (label j)) => ν j)
          (fun j => CompletedGroup.projection l (label j))
          (fun a b hab => (hcomm a b hab).map (CompletedGroup.projection l))) =
      ((WallComplement.restrictPrefunctor _
        (Set.inclusion
          (CompletedGroup.monotone_mulSupport_projection label hkl))).mapPath p).wallPathProduct
            (fun j : Function.mulSupport (fun j => CompletedGroup.projection k (label j)) => ν j)
            (fun j => CompletedGroup.projection k (label j))
            (fun a b hab => (hcomm a b hab).map (CompletedGroup.projection k)) := by
  let f := Set.inclusion (CompletedGroup.monotone_mulSupport_projection label hkl)
  let φ := (F.map (homOfLE hkl).op).hom
  have hproj (j : Function.mulSupport fun j => CompletedGroup.projection l (label j)) :
      φ (CompletedGroup.projection l (label j)) = CompletedGroup.projection k (label j) :=
    CompletedGroup.map_projection k l hkl (label j)
  have hlabel : ∀ j, j ∉ range f → φ (CompletedGroup.projection l (label j)) = 1 := by
    intro j hj
    rw [hproj]
    by_contra hne
    exact hj ⟨⟨j.val, hne⟩, Subtype.ext rfl⟩
  rw [Quiver.Path.map_wallPathProduct _ _ _ φ p]
  have he := p.wallPathProduct_restrict
    (fun j : Function.mulSupport (fun j => CompletedGroup.projection l (label j)) => ν j)
    (fun j => φ (CompletedGroup.projection l (label j)))
    (fun a b hab => ((hcomm a b hab).map (CompletedGroup.projection l)).map φ)
    f (Set.inclusion_injective _) hlabel
  simpa only [Function.comp_def, hproj, f, Set.coe_inclusion] using he.symm

end Quiver.Path
