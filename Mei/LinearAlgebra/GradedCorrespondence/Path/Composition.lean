/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MiniMax
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Path.Basic

/-!
# Concatenation of homogeneous correspondence transfers

A finite itinerary may pass through chambers whose coefficient modules and
correspondence spans differ from edge to edge.  `pathTransfer` composes the
selected homogeneous transfers in traversal order.  Concatenation of
itineraries is the composition of their path transfers, with the second
itinerary's transfer on the left.  These equations make the propagation map
computable by rewriting along the path.

The construction retains the full selected degree at every vertex and does not
assume that the intermediate correspondence is a graph or that its transfer is
invertible.
The component interpretation follows Gross–Hacking–Siebert, *Theta functions
on varieties with effective anti-canonical class*, §3.2
(arXiv:1601.07081v4).
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


/-- Concatenating two itineraries composes their propagation maps, with the
propagation map of the second itinerary on the left.  This is the
concatenation law for finite homogeneous component expansions. -/
@[simp]
theorem pathTransfer_comp {u v w : Q} (f : Quiver.Path u v) (g : Quiver.Path v w) :
    pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) (f.comp g) =
      (pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) g).comp
        (pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) f) := by
  let φ : Q ⥤q SemimoduleCat R := {
    obj q := SemimoduleCat.of R (𝒜 q (p q))
    map e := SemimoduleCat.ofHom ((C e).transfer ⟨p _, hp e⟩ (p _))
  }
  change (SemimoduleCat.Hom.hom ((Paths.lift φ).map (f.comp g))) =
    (SemimoduleCat.Hom.hom ((Paths.lift φ).map g)).comp
      (SemimoduleCat.Hom.hom ((Paths.lift φ).map f))
  exact congrArg SemimoduleCat.Hom.hom ((Paths.lift φ).map_comp f g)

/-- Evaluating the concatenated propagation map first propagates through the
first itinerary and then through the second. -/
theorem pathTransfer_comp_apply {u v w : Q} (f : Quiver.Path u v) (g : Quiver.Path v w)
    (a : 𝒜 u (p u)) :
    pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) (f.comp g) a =
      pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) g
        (pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) f a) := by
  rw [pathTransfer_comp, LinearMap.comp_apply]

section Naturality

variable {M' : Q → Type v} [∀ q, AddCommMonoid (M' q)] [∀ q, Module R (M' q)]
  (𝒜' : ∀ q, ι q → Submodule R (M' q)) [∀ q, DirectSum.Decomposition (𝒜' q)]
  {B' : ∀ {u v : Q}, (u ⟶ v) → Type*}
  [∀ (u v : Q) (e : u ⟶ v), AddCommMonoid (B' e)]
  [∀ (u v : Q) (e : u ⟶ v), Module R (B' e)]
  {I' : ∀ {u v : Q}, (u ⟶ v) → Set (ι u)}
  {J' : ∀ {u v : Q}, (u ⟶ v) → Set (ι v)}
  (D : ∀ {u v : Q} (e : u ⟶ v),
    GradedCorrespondence (B := B' e) (𝒜' u) (𝒜' v) (I' e) (J' e))
  (r : ∀ q, M q →ₗ[R] M' q)
  (hr : ∀ q i a, a ∈ 𝒜 q i → r q a ∈ 𝒜' q i)
  (f : ∀ {u v : Q} (e : u ⟶ v), Hom (C e) (D e) id id)
  (hl : ∀ {u v : Q} (e : u ⟶ v), (f e).left = r u)
  (hv : ∀ {u v : Q} (e : u ⟶ v), (f e).right = r v)

include f hl hv

private theorem edge_restrict_comp_transfer {u v : Q} (e : u ⟶ v) :
    ((r v).restrict (hr v (p v))).comp ((C e).transfer ⟨p u, hp e⟩ (p v)) =
      ((D e).transfer ⟨p u, (f e).admissible_left (hp e)⟩ (p v)).comp
        ((r u).restrict (hr u (p u))) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  have he := (f e).transfer_map_of_injective Function.injective_id
    ⟨p u, hp e⟩ a (p v)
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrict_apply,
    LinearMap.restrict_apply, transfer_apply, id_eq, hl e, hv e] using he.symm

/-- The restricted chamber maps at the endpoints intertwine the path transfers
of the two families of correspondences. -/
theorem restrict_comp_pathTransfer {u v : Q} (fpath : Quiver.Path u v) :
    ((r v).restrict (hr v (p v))).comp
        (pathTransfer (𝒜 := 𝒜) (C := C) (p := p) (hp := hp) fpath) =
      (pathTransfer (𝒜 := 𝒜') (C := D) (p := p)
        (hp := fun {_ _} e ↦ (f e).admissible_left (hp e)) fpath).comp
        ((r u).restrict (hr u (p u))) := by
  let φ : Q ⥤q SemimoduleCat R := {
    obj q := SemimoduleCat.of R (𝒜 q (p q))
    map e := SemimoduleCat.ofHom ((C e).transfer ⟨p _, hp e⟩ (p _))
  }
  let ψ : Q ⥤q SemimoduleCat R := {
    obj q := SemimoduleCat.of R (𝒜' q (p q))
    map e := SemimoduleCat.ofHom ((D e).transfer ⟨p _, (f e).admissible_left (hp e)⟩ (p _))
  }
  let α : (q : Q) → SemimoduleCat.of R (𝒜 q (p q)) ⟶
      SemimoduleCat.of R (𝒜' q (p q)) :=
    fun q => SemimoduleCat.ofHom ((r q).restrict (hr q (p q)))
  have hα : ∀ {u v : Q} (e : u ⟶ v),
      (Paths.lift φ).map e.toPath ≫ α v = α u ≫ (Paths.lift ψ).map e.toPath := by
    intro u v e
    have he := edge_restrict_comp_transfer 𝒜 C p hp 𝒜' D r hr f hl hv e
    apply SemimoduleCat.Hom.ext
    change ((r v).restrict (hr v (p v))).comp ((C e).transfer ⟨p u, hp e⟩ (p v)) =
      ((D e).transfer ⟨p u, (f e).admissible_left (hp e)⟩ (p v)).comp
        ((r u).restrict (hr u (p u)))
    exact he
  have hnat := (Paths.liftNatTrans (F := Paths.lift φ) (G := Paths.lift ψ) α hα).naturality fpath
  have hh := congrArg SemimoduleCat.Hom.hom hnat
  change ((r v).restrict (hr v (p v))).comp
      (SemimoduleCat.Hom.hom ((Paths.lift φ).map fpath)) =
    (SemimoduleCat.Hom.hom ((Paths.lift ψ).map fpath)).comp
      ((r u).restrict (hr u (p u)))
  exact hh

end Naturality

end Mei.GradedCorrespondence
