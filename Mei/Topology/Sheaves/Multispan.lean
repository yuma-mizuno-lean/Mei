/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Basic
public import Mei.Topology.Sheaves.Span
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer

/-!
# Linear matching families from local common face lifts

For an incidence diagram of semimodule-valued sheaves, chamber maps from an
incoming semimodule assemble uniquely into a linear matching family when their
incident pairs have common face lifts locally. The two maps at a face need only
be jointly injective on sections of subopens; either individual map may have a
kernel. No additive inverses or finiteness of the incidence diagram are needed.

The chamber maps may be finite sums of branch maps. Only the totals need local
common face lifts; no lifts of the separate branches are assumed. Local lifts
glue by `TopCat.Sheaf.existsUnique_hom_lift_of_local`. The existing
`MultispanIndex.existsUnique_sections_lift_iff` then assembles the linear matching
family, so no matching-family reconstruction is repeated here.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r w t

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {J : MultispanShape}

/-- Evaluate an incidence diagram of sheaves on one open. This is an abbreviation
so matching-family components retain the original section carriers. It uses
Mathlib's mapping of multispan indices by the sheaf-evaluation functor. -/
@[simps!]
noncomputable abbrev sectionsIndex {C : Type w} [Category.{t} C]
    (I : MultispanIndex J (X.Sheaf C)) (U : Opens X) : MultispanIndex J C :=
  I.map ((sheafSections (Opens.grothendieckTopology X) C).obj (op U))

variable {R : Type r} [Semiring R]
  (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))

/-- Linear chamber maps with local common face lifts extend uniquely to a linear
matching family. Joint injectivity is required only on subopens of the chosen
domain, and separate summands of a chamber map need not admit common lifts. -/
theorem existsUnique_sections_lift_of_local (E : SemimoduleCat.{v} R) (U : Opens X)
    (α : ∀ j, E ⟶ (I.right j).obj.obj (op U))
    (hinj : ∀ (W : Opens X), W ≤ U → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hloc : ∀ b x, x ∈ U → ∃ (N : Opens X) (hNU : N ≤ U)
      (t : E ⟶ (I.left b).obj.obj (op N)), x ∈ N ∧
        t ≫ (I.fst b).hom.app (op N) =
          α (J.fst b) ≫ (I.right (J.fst b)).obj.map (homOfLE hNU).op ∧
        t ≫ (I.snd b).hom.app (op N) =
          α (J.snd b) ≫ (I.right (J.snd b)).obj.map (homOfLE hNU).op) :
    ∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan,
      ∀ a j, (ℓ a).val (.right j) = (α j).hom a := by
  apply ((I.sectionsIndex U).existsUnique_sections_lift_iff
    (fun j => (α j).hom) (hinj U le_rfl)).mpr
  intro a b
  have hinjHom (W : Opens X) (hWU : W ≤ U) : Function.Injective
      (fun t : E ⟶ (I.left b).obj.obj (op W) =>
        (t ≫ (I.fst b).hom.app (op W), t ≫ (I.snd b).hom.app (op W))) := by
    intro s t hst
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply hinj W hWU b
    have hfst := congrArg
      (fun q : E ⟶ (I.right (J.fst b)).obj.obj (op W) => q.hom a) (congrArg _root_.Prod.fst hst)
    have hsnd := congrArg
      (fun q : E ⟶ (I.right (J.snd b)).obj.obj (op W) => q.hom a) (congrArg _root_.Prod.snd hst)
    exact Prod.ext hfst hsnd
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_hom_lift_of_local
    (I.left b) (I.right (J.fst b)) (I.right (J.snd b)) (I.fst b) (I.snd b) E U
    hinjHom (α (J.fst b)) (α (J.snd b)) (hloc b)
  exact ⟨t.hom a, Prod.ext (ConcreteCategory.congr_hom ht.1 a)
    (ConcreteCategory.congr_hom ht.2 a)⟩

end CategoryTheory.Limits.MultispanIndex
