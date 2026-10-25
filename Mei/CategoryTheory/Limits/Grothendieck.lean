/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Fiberwise limits over a Grothendieck construction

For a diagram on a Grothendieck construction, taking limits on the fibers is covariant
in the base whenever restriction along each transition induces an isomorphism of limits.
The limit of this fiberwise diagram is the limit of the original diagram, naturally
in that diagram. Initial transition functors supply the restriction hypothesis through
Mathlib's `Functor.Initial.limit_pre_isIso`.

The functor and cone constructions are reducible on objects and cone points: the fiber
limits and the original cone points are retained as their actual carriers.

The construction uses Mathlib's fiber inclusions `Grothendieck.ι`, their transformations
`Grothendieck.ιNatTrans`, and the inverse of `limit.pre`. It is the limit counterpart of
Mathlib's `fiberwiseColimit`, with an additional restriction hypothesis because the
Grothendieck construction is covariant in its fibers.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u' w z

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] {C : D ⥤ Cat.{w, z}}
  {V : Type u'} [Category.{v'} V]
  (F : Grothendieck C ⥤ V)
  [∀ d, HasLimit (Grothendieck.ι C d ⋙ F)]
  [∀ {d e} (f : d ⟶ e), HasLimit ((C.map f).toFunctor ⋙ (Grothendieck.ι C e ⋙ F))]
  [∀ {d e} (f : d ⟶ e), IsIso (limit.pre (Grothendieck.ι C e ⋙ F) (C.map f).toFunctor)]

namespace FiberwiseLimit

/-- The map between fiber limits induced by a base arrow. -/
noncomputable def map {d e : D} (f : d ⟶ e) :
    limit (Grothendieck.ι C d ⋙ F) ⟶ limit (Grothendieck.ι C e ⋙ F) :=
  limMap (whiskerRight (Grothendieck.ιNatTrans f) F ≫
    (Functor.associator _ _ _).hom) ≫
      inv (limit.pre (Grothendieck.ι C e ⋙ F) (C.map f).toFunctor)

/-- Restricting the target projection computes the fiber map. -/
@[reassoc (attr := simp)]
theorem map_π {d e : D} (f : d ⟶ e) (x : C.obj d) :
    map F f ≫ limit.π (Grothendieck.ι C e ⋙ F) ((C.map f).toFunctor.obj x) =
      limit.π (Grothendieck.ι C d ⋙ F) x ≫ F.map ((Grothendieck.ιNatTrans f).app x) := by
  simp [map, limit.inv_pre_π]

/-- The fiber map intertwines every arrow in the total category over the given base arrow. -/
@[reassoc]
theorem map_π_of_hom {X Y : Grothendieck C} (h : X ⟶ Y) :
    map F h.base ≫ limit.π (Grothendieck.ι C Y.base ⋙ F) Y.fiber =
      limit.π (Grothendieck.ι C X.base ⋙ F) X.fiber ≫ F.map h := by
  rw [← limit.w (Grothendieck.ι C Y.base ⋙ F) h.fiber]
  simp only [Functor.comp_map]
  rw [← Category.assoc (obj := V), map_π, Category.assoc (obj := V), ← F.map_comp,
    Grothendieck.ιNatTrans_app_comp_ι_map]
  rfl

/-- The fiber map of an identity arrow is the identity. -/
@[simp]
theorem map_id (d : D) : map F (𝟙 d) = 𝟙 _ := by
  apply limit.hom_ext
  intro x
  have h := map_π_of_hom F (𝟙 (⟨d, x⟩ : Grothendieck C))
  erw [F.map_id, Category.comp_id] at h
  simpa only [Grothendieck.id_base, Category.id_comp (obj := V)] using h

/-- The fiber maps respect composition in the base. -/
@[reassoc, simp]
theorem map_comp {d e b : D} (f : d ⟶ e) (g : e ⟶ b) :
    map F (f ≫ g) = map F f ≫ map F g := by
  apply (cancel_mono (limit.pre (Grothendieck.ι C b ⋙ F) (C.map (f ≫ g)).toFunctor)).mp
  apply limit.hom_ext
  intro x
  simp only [Category.assoc (obj := V), limit.pre_π]
  let h : (⟨e, (C.map f).toFunctor.obj x⟩ : Grothendieck C) ⟶
      ⟨b, (C.map (f ≫ g)).toFunctor.obj x⟩ :=
    ⟨g, eqToHom (by simp)⟩
  rw [map_π, map_π_of_hom F h]
  dsimp only [Grothendieck.base, Grothendieck.fiber]
  erw [map_π_assoc, ← F.map_comp]
  congr 2
  refine Grothendieck.ext _ _ (by
    dsimp [Grothendieck.ιNatTrans, Grothendieck.comp, h]
    rfl) ?_
  dsimp [Grothendieck.ιNatTrans, Grothendieck.ι, h]
  erw [(C.map g).toFunctor.map_id]
  erw [Category.comp_id (obj := C.obj b), Category.id_comp (obj := C.obj b),
    eqToHom_trans (C := C.obj b)]
  rfl

end FiberwiseLimit

/-- The diagram obtained by taking limits on the fibers and inverting restriction along
base transitions. -/
noncomputable abbrev fiberwiseLimit : D ⥤ V where
  obj d := limit (Grothendieck.ι C d ⋙ F)
  map f := FiberwiseLimit.map F f
  map_id := FiberwiseLimit.map_id F
  map_comp := FiberwiseLimit.map_comp F

@[simp]
theorem fiberwiseLimit_obj (d : D) :
    (fiberwiseLimit F).obj d = limit (Grothendieck.ι C d ⋙ F) := (rfl)

@[simp]
theorem fiberwiseLimit_map {d e : D} (f : d ⟶ e) :
    (fiberwiseLimit F).map f = FiberwiseLimit.map F f := (rfl)

namespace FiberwiseLimit

/-- A cone on the total diagram induces a cone on its fiber limits. -/
noncomputable abbrev coneOfCone (c : Cone F) : Cone (fiberwiseLimit F) where
  pt := c.pt
  π :=
    { app d := limit.lift _ (c.whisker (Grothendieck.ι C d))
      naturality d e f := by
        erw [Category.id_comp (obj := V)]
        apply (cancel_mono (limit.pre (Grothendieck.ι C e ⋙ F) (C.map f).toFunctor)).mp
        apply limit.hom_ext
        intro x
        simp only [Category.assoc (obj := V), limit.pre_π, map_π,
          limit.lift_π_assoc, limit.lift_π]
        exact (c.w ((Grothendieck.ιNatTrans f).app x)).symm }

@[simp]
theorem coneOfCone_pt (c : Cone F) : (coneOfCone F c).pt = c.pt := (rfl)

@[simp]
theorem coneOfCone_π_app (c : Cone F) (d : D) :
    (coneOfCone F c).π.app d = limit.lift _ (c.whisker (Grothendieck.ι C d)) := (rfl)

/-- A cone on the fiber limits induces a cone on the total diagram. -/
noncomputable abbrev totalCone (c : Cone (fiberwiseLimit F)) : Cone F where
  pt := c.pt
  π :=
    { app X := c.π.app X.base ≫ limit.π (Grothendieck.ι C X.base ⋙ F) X.fiber
      naturality X Y h := by
        erw [Category.id_comp (obj := V)]
        rw [← c.w h.base]
        erw [Category.assoc (obj := V), map_π_of_hom, Category.assoc (obj := V)]
        rfl }

@[simp]
theorem totalCone_pt (c : Cone (fiberwiseLimit F)) : (totalCone F c).pt = c.pt := (rfl)

@[simp]
theorem totalCone_π_app (c : Cone (fiberwiseLimit F)) (X : Grothendieck C) :
    (totalCone F c).π.app X =
      c.π.app X.base ≫ limit.π (Grothendieck.ι C X.base ⋙ F) X.fiber := (rfl)

/-- A limiting cone on the fiber limits gives a limiting cone on the total diagram. -/
noncomputable def isLimitTotalCone {c : Cone (fiberwiseLimit F)} (hc : IsLimit c) :
    IsLimit (totalCone F c) where
  lift s := hc.lift (coneOfCone F s)
  fac s X := by
    erw [totalCone_π_app, hc.fac_assoc, coneOfCone_π_app, limit.lift_π]
    rfl
  uniq s m hm := by
    apply hc.uniq (coneOfCone F s) m
    intro d
    apply limit.hom_ext
    intro x
    erw [Category.assoc (obj := V), coneOfCone_π_app, limit.lift_π]
    exact hm ((Grothendieck.ι C d).obj x)

/-- A limiting cone on the total diagram gives a limiting cone on the fiber limits. -/
noncomputable def isLimitConeOfCone {c : Cone F} (hc : IsLimit c) :
    IsLimit (coneOfCone F c) where
  lift s := hc.lift (totalCone F s)
  fac s d := by
    apply limit.hom_ext
    intro x
    erw [coneOfCone_π_app, Category.assoc (obj := V), limit.lift_π, hc.fac,
      totalCone_π_app]
    rfl
  uniq s m hm := by
    apply hc.uniq (totalCone F s) m
    intro X
    have h := congrArg (fun t => t ≫ limit.π (Grothendieck.ι C X.base ⋙ F) X.fiber)
      (hm X.base)
    erw [coneOfCone_π_app, Category.assoc (obj := V), limit.lift_π] at h
    exact h

end FiberwiseLimit

/-- Existence of a limit is equivalent to existence of the iterated fiberwise limit. -/
theorem hasLimit_fiberwiseLimit_iff : HasLimit (fiberwiseLimit F) ↔ HasLimit F := by
  constructor
  · intro h
    exact ⟨⟨_, FiberwiseLimit.isLimitTotalCone F (limit.isLimit _)⟩⟩
  · intro h
    exact ⟨⟨_, FiberwiseLimit.isLimitConeOfCone F (limit.isLimit _)⟩⟩

/-- Taking the total limit agrees with first taking limits on fibers and then on the base. -/
noncomputable def limitFiberwiseLimitIso [HasLimit F] [HasLimit (fiberwiseLimit F)] :
    limit F ≅ limit (fiberwiseLimit F) :=
  (limit.isLimit F).conePointUniqueUpToIso
    (FiberwiseLimit.isLimitTotalCone F (limit.isLimit _))

/-- The comparison to the iterated limit preserves every fiber projection. -/
@[reassoc (attr := simp)]
theorem limitFiberwiseLimitIso_hom_π [HasLimit F] [HasLimit (fiberwiseLimit F)]
    (d : D) (x : C.obj d) :
    (limitFiberwiseLimitIso F).hom ≫ limit.π (fiberwiseLimit F) d ≫
        limit.π (Grothendieck.ι C d ⋙ F) x = limit.π F ⟨d, x⟩ := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨d, x⟩ : Grothendieck C)

/-- The inverse comparison computes the projection at every object of the total category. -/
@[reassoc (attr := simp)]
theorem limitFiberwiseLimitIso_inv_π [HasLimit F] [HasLimit (fiberwiseLimit F)]
    (X : Grothendieck C) :
    (limitFiberwiseLimitIso F).inv ≫ limit.π F X =
      limit.π (fiberwiseLimit F) X.base ≫
        limit.π (Grothendieck.ι C X.base ⋙ F) X.fiber := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ X

section Naturality

variable {F} {G H : Grothendieck C ⥤ V}
  [∀ d, HasLimit (Grothendieck.ι C d ⋙ G)]
  [∀ {d e} (f : d ⟶ e), HasLimit ((C.map f).toFunctor ⋙ (Grothendieck.ι C e ⋙ G))]
  [∀ {d e} (f : d ⟶ e), IsIso (limit.pre (Grothendieck.ι C e ⋙ G) (C.map f).toFunctor)]
  [∀ d, HasLimit (Grothendieck.ι C d ⋙ H)]
  [∀ {d e} (f : d ⟶ e), HasLimit ((C.map f).toFunctor ⋙ (Grothendieck.ι C e ⋙ H))]
  [∀ {d e} (f : d ⟶ e), IsIso (limit.pre (Grothendieck.ι C e ⋙ H) (C.map f).toFunctor)]

/-- A transformation of total diagrams induces a transformation of their fiber limits. -/
noncomputable def fiberwiseLimitMap (α : F ⟶ G) : fiberwiseLimit F ⟶ fiberwiseLimit G where
  app d := limMap (whiskerLeft (Grothendieck.ι C d) α)
  naturality d e f := by
    apply (cancel_mono (limit.pre (Grothendieck.ι C e ⋙ G) (C.map f).toFunctor)).mp
    apply limit.hom_ext
    intro x
    dsimp only [fiberwiseLimit]
    simp only [Category.assoc (obj := V), limit.pre_π]
    erw [limMap_π, FiberwiseLimit.map_π_assoc, FiberwiseLimit.map_π, limMap_π_assoc]
    exact congrArg (fun t => limit.π (Grothendieck.ι C d ⋙ F) x ≫ t)
      (α.naturality ((Grothendieck.ιNatTrans f).app x))

@[simp]
theorem fiberwiseLimitMap_app (α : F ⟶ G) (d : D) :
    (fiberwiseLimitMap α).app d = limMap (whiskerLeft (Grothendieck.ι C d) α) := (rfl)

/-- Fiberwise limits preserve identity transformations. -/
@[simp]
theorem fiberwiseLimitMap_id : fiberwiseLimitMap (𝟙 F) = 𝟙 (fiberwiseLimit F) := by
  apply NatTrans.ext
  funext d
  apply limit.hom_ext
  intro x
  simp [Category.id_comp (obj := V)]

/-- Fiberwise limits preserve composition of transformations. -/
@[simp]
theorem fiberwiseLimitMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    fiberwiseLimitMap (α ≫ β) = fiberwiseLimitMap α ≫ fiberwiseLimitMap β := by
  apply NatTrans.ext
  funext d
  apply limit.hom_ext
  intro x
  simp [Category.assoc (obj := V)]

/-- The total-to-iterated limit comparison is natural in the total diagram. -/
@[reassoc]
theorem limitFiberwiseLimitIso_naturality (α : F ⟶ G)
    [HasLimit F] [HasLimit G] [HasLimit (fiberwiseLimit F)] [HasLimit (fiberwiseLimit G)] :
    limMap α ≫ (limitFiberwiseLimitIso G).hom =
      (limitFiberwiseLimitIso F).hom ≫ limMap (fiberwiseLimitMap α) := by
  apply limit.hom_ext
  intro d
  apply limit.hom_ext
  intro x
  simp only [Category.assoc (obj := V), limMap_π, fiberwiseLimitMap_app]
  rw [limitFiberwiseLimitIso_hom_π]
  erw [limMap_π α (⟨d, x⟩ : Grothendieck C), limitFiberwiseLimitIso_hom_π_assoc]
  rfl

end Naturality

end CategoryTheory.Limits
