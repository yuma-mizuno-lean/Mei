/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Category.SemimoduleCat.Multispan.Basic
public import Mei.Topology.Sheaves.Span
public import Mei.LinearAlgebra.CommonLift
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer

/-!
# Linear matching families from local common face lifts

For an incidence diagram of semimodule-valued sheaves, chamber maps from an
incoming semimodule assemble uniquely into a linear matching family when their
incident pairs have common face lifts locally. The two maps at a face need only
be jointly injective on sections of subopens; either individual map may have a
kernel. No additive inverses or finiteness of the incidence diagram are needed.

The chamber maps may be finite sums of branch maps. Only the totals need local
common face lifts; no lifts of the separate branches are assumed. Neighborhoods
and face lifts may depend on each incoming input and need not vary linearly in
that input. The existing
`MultispanIndex.existsUnique_sections_lift_iff` then assembles the linear matching
family, so no matching-family reconstruction is repeated here.

It is enough to supply local common lifts on a spanning set of incoming inputs.
This gives a finite-input test when the incoming semimodule is finitely generated,
without requiring a common neighborhood for different generators.
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r w t

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {J : MultispanShape}

/-- Evaluate an incidence diagram of sheaves on one open. This is an abbreviation
so matching-family components retain the original section carriers. It uses
Mathlib's mapping of multispan indices by the sheaf-evaluation functor. -/
noncomputable abbrev sectionsIndex {C : Type w} [Category.{t} C]
    (I : MultispanIndex J (X.Sheaf C)) (U : Opens X) : MultispanIndex J C :=
  I.map (((TopCat.Sheaf.forget C X).flip).obj (op U))

variable {R : Type r} [Semiring R]
  (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))

-- Glue whole linear local lifts as an internal step for the cyclic-submodule proof.
private theorem existsUnique_sections_lift_of_linear_local (E : SemimoduleCat.{v} R) (U : Opens X)
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

/-- Linear chamber maps admit a unique linear matching family when each individual
input has common face lifts near every point. The local neighborhoods can depend
on both the input and the face, and either individual face leg may have a kernel. -/
theorem existsUnique_sections_lift_of_local (E : SemimoduleCat.{v} R)
    (U : Opens X) (α : ∀ j, E ⟶ (I.right j).obj.obj (op U))
    (hinj : ∀ (W : Opens X), W ≤ U → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hloc : ∀ (a : E) b x, x ∈ U → ∃ (N : Opens X) (hNU : N ≤ U)
      (t : (I.left b).obj.obj (op N)), x ∈ N ∧
        (I.fst b).hom.app (op N) t =
          (I.right (J.fst b)).obj.map (homOfLE hNU).op ((α (J.fst b)).hom a) ∧
        (I.snd b).hom.app (op N) t =
          (I.right (J.snd b)).obj.map (homOfLE hNU).op ((α (J.snd b)).hom a)) :
    ∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan,
      ∀ a j, (ℓ a).val (.right j) = (α j).hom a := by
  apply ((I.sectionsIndex U).existsUnique_sections_lift_iff
    (fun j => (α j).hom) (hinj U le_rfl)).mpr
  intro a b
  -- Glue on the cyclic submodule of each input. It fits in the section universe
  -- even when the scalar semiring does not; span closure supplies all local lifts.
  let P : Submodule R E := Submodule.span R {a}
  let β (j : J.R) : SemimoduleCat.of R P ⟶ (I.right j).obj.obj (op U) :=
    SemimoduleCat.ofHom ((α j).hom.comp P.subtype)
  obtain ⟨ℓ, hℓ, -⟩ := I.existsUnique_sections_lift_of_linear_local (SemimoduleCat.of R P) U β
    hinj (by
      intro c x hx
      obtain ⟨N, hNU, t, hxN, hf, hg⟩ := hloc a c x hx
      -- Specify the original face maps so the lift equations already use the
      -- original section carriers; no mapped-index wrapper is unfolded below.
      obtain ⟨ψ, ⟨hψf, hψg⟩, -⟩ :=
        LinearMap.existsUnique_comp_eq_and_comp_eq_on_span_singleton
          (f := ((I.fst c).hom.app (op N)).hom)
          (g := ((I.snd c).hom.app (op N)).hom) (hinj N hNU c)
          (α := ((I.right (J.fst c)).obj.map (homOfLE hNU).op).hom.comp
            (α (J.fst c)).hom)
          (β := ((I.right (J.snd c)).obj.map (homOfLE hNU).op).hom.comp
            (α (J.snd c)).hom) a ⟨t, Prod.ext hf hg⟩
      refine ⟨N, hNU, SemimoduleCat.ofHom ψ, hxN, ?_, ?_⟩
      · apply SemimoduleCat.hom_ext
        simpa only [SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom, β,
          P, LinearMap.comp_assoc] using hψf
      · apply SemimoduleCat.hom_ext
        simpa only [SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom, β,
          P, LinearMap.comp_assoc] using hψg)
  let aP : P := ⟨a, Submodule.mem_span_singleton_self a⟩
  have hright (j : J.R) : (ℓ aP).val (.right j) = (α j).hom a := by
    simpa only [β, SemimoduleCat.hom_ofHom, LinearMap.comp_apply,
      Submodule.subtype_apply] using hℓ aP j
  have hface := (I.sectionsIndex U).mem_sectionsSubmodule_multispan.mp (ℓ aP).property
  exact ⟨(ℓ aP).val (.left b), Prod.ext ((hface.1 b).trans (hright _))
    ((hface.2 b).trans (hright _))⟩

/-- It suffices to check local common face lifts on a spanning set of incoming
inputs. Neighborhoods and lifts may depend on the generator and the face;
no compatibility between the chosen lifts, and no lifts for individual summands
of a chamber map, are required. A finite generating set therefore gives a
finite-input criterion for the unique linear matching family. -/
theorem existsUnique_sections_lift_of_local_on_generators
    (E : SemimoduleCat.{v} R) (U : Opens X)
    (α : ∀ j, E ⟶ (I.right j).obj.obj (op U))
    (s : Set E) (hs : Submodule.span R s = ⊤)
    (hinj : ∀ (W : Opens X), W ≤ U → ∀ b,
      Function.Injective (((I.sectionsIndex W).fst b).hom.prod
        ((I.sectionsIndex W).snd b).hom))
    (hloc : ∀ a ∈ s, ∀ b x, x ∈ U → ∃ (N : Opens X) (hNU : N ≤ U)
      (t : (I.left b).obj.obj (op N)), x ∈ N ∧
        (I.fst b).hom.app (op N) t =
          (I.right (J.fst b)).obj.map (homOfLE hNU).op ((α (J.fst b)).hom a) ∧
        (I.snd b).hom.app (op N) t =
          (I.right (J.snd b)).obj.map (homOfLE hNU).op ((α (J.snd b)).hom a)) :
    ∃! ℓ : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex U).multispan,
      ∀ a j, (ℓ a).val (.right j) = (α j).hom a := by
  apply ((I.sectionsIndex U).existsUnique_sections_lift_iff
    (fun j => (α j).hom) (hinj U le_rfl)).mpr
  have hspan : Submodule.span R s ≤
      ((I.sectionsIndex U).compatibleFamilies).comap (LinearMap.pi fun j => (α j).hom) := by
    apply Submodule.span_le.mpr
    intro a ha
    -- A generator supplies local lifts on its cyclic submodule; span closure
    -- of compatible chamber families then handles all incoming inputs.
    let P : Submodule R E := Submodule.span R {a}
    let β (j : J.R) : SemimoduleCat.of R P ⟶ (I.right j).obj.obj (op U) :=
      SemimoduleCat.ofHom ((α j).hom.comp P.subtype)
    obtain ⟨ℓ, hℓ, -⟩ := I.existsUnique_sections_lift_of_local
      (SemimoduleCat.of R P) U β hinj (by
        intro p b x hx
        obtain ⟨N, hNU, t, hxN, hf, hg⟩ := hloc a ha b x hx
        let f := ((I.fst b).hom.app (op N)).hom
        let g := ((I.snd b).hom.app (op N)).hom
        let δ j := ((I.right j).obj.map (homOfLE hNU).op).hom.comp (α j).hom
        have hP : P ≤ (LinearMap.range (f.prod g)).comap ((δ (J.fst b)).prod (δ (J.snd b))) :=
          (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨t, Prod.ext hf hg⟩
        obtain ⟨z, hz⟩ := hP p.property
        refine ⟨N, hNU, z, hxN, ?_⟩
        simpa only [f, g, δ, β, LinearMap.prod_apply, LinearMap.comp_apply,
          SemimoduleCat.hom_ofHom, Submodule.subtype_apply, Function.prod_apply,
          LinearMap.coe_comp, Function.comp_apply, Prod.mk.injEq] using hz)
    let aP : P := ⟨a, Submodule.mem_span_singleton_self a⟩
    have hright (j : J.R) : (ℓ aP).val (.right j) = (α j).hom a := by
      simpa only [β, SemimoduleCat.hom_ofHom, LinearMap.comp_apply,
        Submodule.subtype_apply] using hℓ aP j
    have hmem := ((I.sectionsIndex U).restrictSections (ℓ aP)).property
    apply (Submodule.mem_comap (f := LinearMap.pi fun j => (α j).hom)
      (p := (I.sectionsIndex U).compatibleFamilies) (x := a)).mpr
    apply (I.sectionsIndex U).mem_compatibleFamilies.mpr
    simpa only [mem_compatibleFamilies, restrictSections_apply, hright,
      LinearMap.pi_apply] using hmem
  intro a
  exact (I.sectionsIndex U).mem_compatibleFamilies_iff_forall_mem_range.mp
    (hspan (hs.ge Submodule.mem_top))

end CategoryTheory.Limits.MultispanIndex
