/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Hom
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

/-- The linear propagation map along a finite itinerary.  The transfer on the
last edge is composed on the left with the propagation map on the preceding
path.  Thus edge transfers are applied in traversal order. -/
noncomputable def pathTransfer {u v : Q} (f : Quiver.Path u v) :
    𝒜 u (p u) →ₗ[R] 𝒜 v (p v) :=
  @Quiver.Path.rec Q _ u (fun v _ => 𝒜 u (p u) →ₗ[R] 𝒜 v (p v))
    LinearMap.id
    (fun {b c} _g e ih =>
      ((C e).transfer ⟨p b, hp e⟩ (p c)).comp
        (ih : 𝒜 u (p u) →ₗ[R] 𝒜 b (p b))) v f

/-- The propagation map on an empty itinerary is the identity. -/
@[simp]
theorem pathTransfer_nil (u : Q) :
    pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp)
      (Quiver.Path.nil : Quiver.Path u u) = LinearMap.id := by
  rfl

/-- Appending one edge to an itinerary composes its edge transfer on the right
with the propagation map on the preceding path. -/
@[simp]
theorem pathTransfer_cons {u v w : Q} (g : Quiver.Path u v) (e : v ⟶ w) :
    pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) (g.cons e) =
      ((C e).transfer ⟨p v, hp e⟩ (p w)).comp
        (pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) g) := by
  rfl



end Mei.GradedCorrespondence
