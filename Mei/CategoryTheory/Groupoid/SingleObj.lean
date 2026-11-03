/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.SingleObj

/-!
# Faithful functors from groupoids to groups

Every groupoid `G` admits a faithful functor to the one-object groupoid of a group
(`CategoryTheory.Groupoid.exists_faithful_functor_singleObj`). The group is the product, over
the objects `c` of `G`, of the automorphism groups of `c`. An arrow `f : a ⟶ b` goes, in the
factor of `c`, to `u ≫ f ≫ v⁻¹` where `u : c ⟶ a` and `v : c ⟶ b` are fixed arrows, whenever
`c` maps into `a` and hence into `b`, and to the identity otherwise. The fixed arrows
cancel in composites, and the factor of the source `a` recovers `f`.

Such a functor lets statements about groups, for instance about words in a free group, be
applied to arrows of a groupoid.
-/

public section

noncomputable section

namespace CategoryTheory.Groupoid

universe v u

variable {G : Type u} [Groupoid.{v} G]

/-- A fixed isomorphism from `c` to an object that `c` maps into. -/
private def gaugeIso (c a : G) (h : Nonempty (c ⟶ a)) : c ≅ a :=
  (Groupoid.isoEquivHom c a).symm h.some

open Classical in
/-- The `c`-factor of the image of an arrow in the product of automorphism groups: the arrow
conjugated by fixed isomorphisms from `c` when `c` maps into its source, and the identity
otherwise. -/
private def gaugedAut (c : G) {a b : G} (f : a ⟶ b) : Aut c :=
  if h : Nonempty (c ⟶ a) then
    .of (gaugeIso c a h ≪≫ asIso f ≪≫ (gaugeIso c b ⟨h.some ≫ f⟩).symm)
  else 1

private theorem gaugedAut_id (c a : G) : gaugedAut c (𝟙 a) = 1 := by
  unfold gaugedAut
  split_ifs with h
  · ext
    simp [gaugeIso]
  · rfl

private theorem gaugedAut_comp (c : G) {a b d : G} (f : a ⟶ b) (g : b ⟶ d) :
    gaugedAut c (f ≫ g) = gaugedAut c g * gaugedAut c f := by
  by_cases h : Nonempty (c ⟶ a)
  · have hb : Nonempty (c ⟶ b) := ⟨h.some ≫ f⟩
    simp only [gaugedAut, h, hb, ↓reduceDIte]
    ext
    simp [gaugeIso]
  · have hb : ¬ Nonempty (c ⟶ b) := fun ⟨u⟩ => h ⟨u ≫ inv f⟩
    simp [gaugedAut, h, hb]

/-- The functor from a groupoid to the one-object groupoid of the product of the automorphism
groups of its objects, sending an arrow to its gauged conjugates. -/
private def toSingleObjAut : G ⥤ SingleObj (∀ c : G, Aut c) where
  obj _ := SingleObj.star _
  map f := fun c => gaugedAut c f
  map_id a := funext fun c => gaugedAut_id c a
  map_comp f g := funext fun c => gaugedAut_comp c f g

private theorem toSingleObjAut_faithful : (toSingleObjAut : G ⥤ _).Faithful where
  map_injective {a b} f g hfg := by
    have h := congrFun hfg a
    have hnon : Nonempty (a ⟶ a) := ⟨𝟙 a⟩
    have hnb : Nonempty (a ⟶ b) := ⟨f⟩
    simp only [toSingleObjAut, gaugedAut, hnon, ↓reduceDIte] at h
    have h' := congrArg (fun e : Aut a => e.asIso.hom) h
    simp only [gaugeIso, Groupoid.isoEquivHom_symm_apply_hom, Iso.trans_hom, asIso_hom] at h'
    simpa [cancel_epi, cancel_mono] using h'

/-- Every groupoid has a faithful functor to the one-object groupoid of a group. -/
theorem exists_faithful_functor_singleObj (G : Type u) [Groupoid.{v} G] :
    ∃ (H : Type (max u v)) (_ : Group H) (F : G ⥤ SingleObj H), F.Faithful :=
  ⟨∀ c : G, Aut c, inferInstance, toSingleObjAut, toSingleObjAut_faithful⟩

end CategoryTheory.Groupoid
