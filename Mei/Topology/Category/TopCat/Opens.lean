/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Images of opens under identity and composite open maps

The image-open functor identifies the identity image with the original open,
and the image under a composite with successive images. These equalities supply
canonical comparison morphisms between section domains without exposing the
representation of an open as a set with an openness proof.
-/

public section

open CategoryTheory TopologicalSpace TopCat

universe u

namespace IsOpenMap

/-- The image of an open under the identity open map is the original open. -/
@[simp]
theorem functor_obj_id {X : TopCat.{u}} (U : Opens X) :
    (functor (f := 𝟙 X) IsOpenMap.id).obj U = U :=
  Opens.ext (Set.image_id _)

/-- Taking the image of an open under a composite is taking successive images. -/
@[simp]
theorem functor_obj_comp {X Y Z : TopCat.{u}} {j : X ⟶ Y} {k : Y ⟶ Z}
    (hj : IsOpenMap j) (hk : IsOpenMap k) (U : Opens X) :
    (functor (f := j ≫ k) (hk.comp hj)).obj U = hk.functor.obj (hj.functor.obj U) := by
  apply Opens.ext
  exact (Set.image_image k j (U : Set X)).symm

end IsOpenMap
