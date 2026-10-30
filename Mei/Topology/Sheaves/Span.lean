/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.Section

/-!
# Local common lifts through a sheaf span

Two morphisms into the targets of a sheaf span have a unique common lift if they
have common lifts locally and the span is jointly injective on morphisms from the
fixed source object. Neither leg needs to be injective on its own.

We glue in Mathlib's `CategoryTheory.sheafOver`, so the local and global lifts are
morphisms in the original value category. For semimodule-valued sheaves this
preserves linearity without any additive-inverse assumption. Compatibility on
overlaps follows from joint injectivity; existence uses the existing sheaf gluing
theorem, and equality of the target morphisms uses local equality of sections.
-/

public section

open CategoryTheory TopologicalSpace Opposite Topology

universe u v w

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {C : Type w} [Category.{v} C]
  (F G K : X.Sheaf C) (f : F ⟶ G) (g : F ⟶ K)

/-- Local common lifts through a jointly injective sheaf span glue uniquely.
Joint injectivity is required only on morphisms from the chosen object `A` and
on subopens of `U`. The two legs may each fail to be injective. -/
theorem existsUnique_hom_lift_of_local (A : C) (U : Opens X)
    (hinj : ∀ (W : Opens X), W ≤ U → Function.Injective
      (fun t : A ⟶ F.obj.obj (op W) =>
        (t ≫ f.hom.app (op W), t ≫ g.hom.app (op W))))
    (a : A ⟶ G.obj.obj (op U)) (b : A ⟶ K.obj.obj (op U))
    (hloc : ∀ x ∈ U, ∃ (N : Opens X) (hNU : N ≤ U)
      (t : A ⟶ F.obj.obj (op N)), x ∈ N ∧
        t ≫ f.hom.app (op N) = a ≫ G.obj.map (homOfLE hNU).op ∧
        t ≫ g.hom.app (op N) = b ≫ K.obj.map (homOfLE hNU).op) :
    ∃! t : A ⟶ F.obj.obj (op U),
      t ≫ f.hom.app (op U) = a ∧ t ≫ g.hom.app (op U) = b := by
  classical
  choose N hN t hxN hf hg using fun x : U => hloc x.val x.property
  have hfres (x : U) {W : Opens X} (hWN : W ≤ N x) :
      (t x ≫ F.obj.map (homOfLE hWN).op) ≫ f.hom.app (op W) =
        a ≫ G.obj.map (homOfLE (hWN.trans (hN x))).op := by
    rw [Category.assoc, f.hom.naturality, ← Category.assoc, hf x, Category.assoc,
      ← G.obj.map_comp, ← op_comp, homOfLE_comp]
  have hgres (x : U) {W : Opens X} (hWN : W ≤ N x) :
      (t x ≫ F.obj.map (homOfLE hWN).op) ≫ g.hom.app (op W) =
        b ≫ K.obj.map (homOfLE (hWN.trans (hN x))).op := by
    rw [Category.assoc, g.hom.naturality, ← Category.assoc, hg x, Category.assoc,
      ← K.obj.map_comp, ← op_comp, homOfLE_comp]
  let H : X.Sheaf (Type v) := CategoryTheory.sheafOver F A
  have hcompat : TopCat.Presheaf.IsCompatible H.obj N t := by
    intro x y
    apply hinj (N x ⊓ N y) (inf_le_left.trans (hN x))
    exact Prod.ext ((hfres x inf_le_left).trans (hfres y inf_le_right).symm)
      ((hgres x inf_le_left).trans (hgres y inf_le_right).symm)
  have hcover : U ≤ iSup N := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
  obtain ⟨s₀, hs₀, -⟩ :=
    TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types H.property t hcompat
  -- Keep the morphism carrier explicit when passing out of the Type-valued Hom sheaf.
  let s₀' : A ⟶ F.obj.obj (op (iSup N)) := s₀
  let s : A ⟶ F.obj.obj (op U) := s₀' ≫ F.obj.map (homOfLE hcover).op
  have hs (x : U) : s ≫ F.obj.map (homOfLE (hN x)).op = t x := by
    calc
      s ≫ F.obj.map (homOfLE (hN x)).op =
          s₀' ≫ (F.obj.map (homOfLE hcover).op ≫ F.obj.map (homOfLE (hN x)).op) :=
        Category.assoc _ _ _
      _ = s₀' ≫ F.obj.map (homOfLE (le_iSup N x)).op :=
        congrArg (s₀' ≫ ·) (F.obj.map_comp (homOfLE hcover).op (homOfLE (hN x)).op).symm
      _ = t x := hs₀ x
  have hsf : s ≫ f.hom.app (op U) = a := by
    apply TopCat.Sheaf.section_ext (CategoryTheory.sheafOver G A)
    intro x hx
    let z : U := ⟨x, hx⟩
    refine ⟨N z, hN z, hxN z, ?_⟩
    -- The Hom sheaf uses coyoneda, so restriction is definitionally postcomposition.
    -- Expose that representation here to apply f.hom.naturality in the value category.
    change (s ≫ f.hom.app (op U)) ≫ G.obj.map (homOfLE (hN z)).op = _
    rw [Category.assoc, ← f.hom.naturality, ← Category.assoc]
    exact (congrArg (fun q => q ≫ f.hom.app (op (N z))) (hs z)).trans (hf z)
  have hsg : s ≫ g.hom.app (op U) = b := by
    apply TopCat.Sheaf.section_ext (CategoryTheory.sheafOver K A)
    intro x hx
    let z : U := ⟨x, hx⟩
    refine ⟨N z, hN z, hxN z, ?_⟩
    -- The Hom sheaf uses coyoneda, so restriction is definitionally postcomposition.
    -- Expose that representation here to apply g.hom.naturality in the value category.
    change (s ≫ g.hom.app (op U)) ≫ K.obj.map (homOfLE (hN z)).op = _
    rw [Category.assoc, ← g.hom.naturality, ← Category.assoc]
    exact (congrArg (fun q => q ≫ g.hom.app (op (N z))) (hs z)).trans (hg z)
  refine ⟨s, ⟨hsf, hsg⟩, fun s' hs' => ?_⟩
  exact hinj U le_rfl (Prod.ext (hs'.1.trans hsf.symm) (hs'.2.trans hsg.symm))

end TopCat.Sheaf
