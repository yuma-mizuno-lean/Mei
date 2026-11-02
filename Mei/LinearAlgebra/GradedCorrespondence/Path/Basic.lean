/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Hom
public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Homogeneous transfers along admissible paths

Choose a homogeneous piece at each vertex of a quiver and a graded
correspondence on each arrow.  `pathTransfer` composes the selected homogeneous
transfers in traversal order.  Vertices may represent occurrences of a chamber
with different selected degrees; neither the quiver nor its sets of arrows need
to be finite.

The construction retains the full selected degree at every vertex.  A terminal
vertex needs no admissible lift, so its selected degree may lie outside the
admissible set.  The transfer is not assumed invertible and its middle
correspondence may differ from edge to edge.

This module provides the basic transfer and one-edge laws.  The concatenation
and coefficient-map naturality laws live in `Path/Composition.lean`.
-/

public noncomputable section

namespace Mei.GradedCorrespondence

open CategoryTheory

universe v

variable {R Q : Type*} [Semiring R] [Quiver Q]
  {M : Q → Type v} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (𝒜 : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (𝒜 q)]
  {I : ∀ {u v : Q}, (u ⟶ v) → Set (ι u)}
  {J : ∀ {u v : Q}, (u ⟶ v) → Set (ι v)}
  {B : ∀ {u v : Q}, (u ⟶ v) → Type*}
  [∀ (u v : Q) (e : u ⟶ v), AddCommMonoid (B e)]
  [∀ (u v : Q) (e : u ⟶ v), Module R (B e)]
  (C : ∀ {u v : Q} (e : u ⟶ v),
    GradedCorrespondence (B := B e) (𝒜 u) (𝒜 v) (I e) (J e))
  (p : ∀ q, ι q)
  (hp : ∀ {u v : Q} (e : u ⟶ v), p u ∈ I e)

/-- The prefunctor selecting the homogeneous transfer on each quiver edge. -/
@[expose]
noncomputable def pathTransferPrefunctor :
    Q ⥤q SemimoduleCat R where
  obj q := SemimoduleCat.of R (𝒜 q (p q))
  map e := SemimoduleCat.ofHom
    ((C e).transfer ⟨p _, hp e⟩ (p _))

/-- The linear propagation map along a finite itinerary.  The transfer on the
last edge is composed on the left with the propagation map on the preceding
path.  Thus edge transfers are applied in traversal order. -/
@[expose]
noncomputable def pathTransfer {u v : Q} (f : Quiver.Path u v) :
    𝒜 u (p u) →ₗ[R] 𝒜 v (p v) := by
  change (SemimoduleCat.of R {x // x ∈ 𝒜 u (p u)} →ₗ[R]
    SemimoduleCat.of R {x // x ∈ 𝒜 v (p v)})
  exact ((Paths.lift (pathTransferPrefunctor (𝒜 := 𝒜) (C := C) (p := p) (hp := hp))).map f).hom

/-- The propagation map on an empty itinerary is the identity. -/
@[simp]
theorem pathTransfer_nil (u : Q) :
    pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp)
      (Quiver.Path.nil : Quiver.Path u u) = LinearMap.id := by
  rfl

/-- The propagation map on a one-edge itinerary is the corresponding edge
transfer. -/
@[simp]
theorem pathTransfer_toPath {u v : Q} (e : u ⟶ v) :
    pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) e.toPath =
      (C e).transfer ⟨p u, hp e⟩ (p v) := by
  rw [pathTransfer, Paths.lift_toPath]
  rfl

/-- Appending one edge to an itinerary applies its edge transfer after the
propagation map on the preceding path (composition on the left). -/
@[simp]
theorem pathTransfer_cons {u v w : Q} (g : Quiver.Path u v) (e : v ⟶ w) :
    pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) (g.cons e) =
      ((C e).transfer ⟨p v, hp e⟩ (p w)).comp
        (pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) g) := by
  rfl

end Mei.GradedCorrespondence
