/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.GroupTheory.CompletedGroup.Basic

/-!
# Maps of completed group towers

A monotone cutoff modulus `l` and a natural transformation from the source tower
reindexed by `l` to the target tower induce a homomorphism of completed groups.
Its order-`k` projection uses only source order `l k`. Same-level tower maps are
the case `l = OrderHom.id`; no cofinality or surjectivity assumption is needed.

The maps respect identities and composition. Enlarging a modulus, and precomposing
its components with the corresponding transitions, leaves the completed map unchanged.
Maps inverse up to such transitions give an equivalence of completed groups. These
facts let one compare completions constructed using different cutoff functions.

The construction uses `Mei.CompletedGroup.lift`; compatible finite-order maps are
represented by Mathlib's natural transformations, rather than a separate tower-map
structure.
-/

public section

open CategoryTheory Opposite

universe u

namespace Mei.CompletedGroup

variable {F : ℕᵒᵖ ⥤ GrpCat.{u}} {G : ℕᵒᵖ ⥤ GrpCat.{u}}
  {H : ℕᵒᵖ ⥤ GrpCat.{u}}

/-- The homomorphism of completed groups induced by compatible maps with cutoff modulus `l`. -/
def map (l : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G) :
    completedGroup F →* completedGroup G :=
  lift (fun k => (f.app (op k)).hom.comp (projection (l k))) (by
    intro k j h
    ext x
    have hn := ConcreteCategory.congr_hom (f.naturality (homOfLE h).op)
      (projection (l j) x)
    have hn' : G.map (homOfLE h).op (f.app (op j) (projection (l j) x)) =
        f.app (op k) (F.map (homOfLE (l.monotone h)).op (projection (l j) x)) := hn.symm
    simpa only [MonoidHom.comp_apply, map_projection] using hn')

/-- Projection of a completed map is its prescribed finite-order component. -/
@[simp]
theorem projection_map (l : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (k : ℕ) (x : completedGroup F) :
    projection k (map l f x) = f.app (op k) (projection (l k) x) := by
  rw [map, projection_lift, MonoidHom.comp_apply]

/-- A larger source cutoff computes the same component of a completed map. -/
theorem projection_map_of_le (l : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (k a : ℕ) (h : l k ≤ a) (x : completedGroup F) :
    projection k (map l f x) =
      f.app (op k) (F.map (homOfLE h).op (projection a x)) := by
  rw [map_projection, projection_map]

/-- Identity components at the identity modulus induce the identity map. -/
@[simp]
theorem map_id : map OrderHom.id (Functor.leftUnitor F).hom = MonoidHom.id (completedGroup F) := by
  ext x k
  exact projection_map OrderHom.id (Functor.leftUnitor F).hom k x

/-- Successive completed maps compose with modulus `l ∘ m`. -/
theorem map_comp (l m : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (g : m.toFunctor.op ⋙ G ⟶ H) :
    map (l.comp m) (Functor.whiskerLeft m.toFunctor.op f ≫ g) =
      (map m g).comp (map l f) := by
  ext x k
  simp only [projection_map, MonoidHom.comp_apply]
  rfl

/-- Comparing components after any common larger cutoff suffices to compare completed maps. -/
theorem map_eq (l m : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (g : m.toFunctor.op ⋙ F ⟶ G)
    (h : ∀ k, ∃ a, ∃ hl : l k ≤ a, ∃ hm : m k ≤ a,
      F.map (homOfLE hl).op ≫ f.app (op k) =
        F.map (homOfLE hm).op ≫ g.app (op k)) :
    map l f = map m g := by
  ext x k
  obtain ⟨a, hl, hm, ha⟩ := h k
  rw [projection_map_of_le l f k a hl, projection_map_of_le m g k a hm]
  exact ConcreteCategory.congr_hom ha (projection a x)

/-- Enlarging the source modulus and precomposing with transitions preserves the map. -/
theorem map_eq_of_le (l m : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (g : m.toFunctor.op ⋙ F ⟶ G) (h : l ≤ m)
    (hg : ∀ k, F.map (homOfLE (h k)).op ≫ f.app (op k) = g.app (op k)) :
    map l f = map m g := by
  apply map_eq
  intro k
  refine ⟨m k, h k, le_rfl, ?_⟩
  simpa using hg k

/-- A cutoff-modulus map carries the corresponding source filtration into the target one. -/
theorem map_mem_degreeFiltration (l : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (k : ℕ) {x : completedGroup F} (hx : x ∈ degreeFiltration F (l k + 1)) :
    map l f x ∈ degreeFiltration G (k + 1) := by
  simp only [degreeFiltration_succ, MonoidHom.mem_ker] at hx ⊢
  rw [projection_map, hx, map_one]

/-- Finite-order maps which compose to transitions induce a left inverse after completion. -/
theorem map_leftInverse (l m : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (g : m.toFunctor.op ⋙ G ⟶ F) (h : ∀ k, k ≤ l (m k))
    (hgf : ∀ k, f.app (op (m k)) ≫ g.app (op k) = F.map (homOfLE (h k)).op) :
    Function.LeftInverse (map m g) (map l f) := by
  intro x
  apply ext
  intro k
  simp only [projection_map]
  rw [← GrpCat.comp_apply, hgf, map_projection]

/-- Mutually inverse finite-order maps up to transition induce an equivalence of completions.
The two moduli may differ and need not be inverses as functions. -/
def equivOfCompEqTransition (l m : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (g : m.toFunctor.op ⋙ G ⟶ F)
    (hl : ∀ k, k ≤ l (m k)) (hm : ∀ k, k ≤ m (l k))
    (hgf : ∀ k, f.app (op (m k)) ≫ g.app (op k) = F.map (homOfLE (hl k)).op)
    (hfg : ∀ k, g.app (op (l k)) ≫ f.app (op k) = G.map (homOfLE (hm k)).op) :
    completedGroup F ≃* completedGroup G :=
  { map l f with
    invFun := map m g
    left_inv := map_leftInverse l m f g hl hgf
    right_inv := map_leftInverse m l g f hm hfg }

@[simp]
theorem equivOfCompEqTransition_apply (l m : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (g : m.toFunctor.op ⋙ G ⟶ F)
    (hl : ∀ k, k ≤ l (m k)) (hm : ∀ k, k ≤ m (l k))
    (hgf : ∀ k, f.app (op (m k)) ≫ g.app (op k) = F.map (homOfLE (hl k)).op)
    (hfg : ∀ k, g.app (op (l k)) ≫ f.app (op k) = G.map (homOfLE (hm k)).op)
    (x : completedGroup F) : equivOfCompEqTransition l m f g hl hm hgf hfg x = map l f x := (rfl)

@[simp]
theorem equivOfCompEqTransition_symm_apply (l m : ℕ →o ℕ) (f : l.toFunctor.op ⋙ F ⟶ G)
    (g : m.toFunctor.op ⋙ G ⟶ F)
    (hl : ∀ k, k ≤ l (m k)) (hm : ∀ k, k ≤ m (l k))
    (hgf : ∀ k, f.app (op (m k)) ≫ g.app (op k) = F.map (homOfLE (hl k)).op)
    (hfg : ∀ k, g.app (op (l k)) ≫ f.app (op k) = G.map (homOfLE (hm k)).op)
    (x : completedGroup G) :
    (equivOfCompEqTransition l m f g hl hm hgf hfg).symm x = map m g x := (rfl)

end Mei.CompletedGroup
