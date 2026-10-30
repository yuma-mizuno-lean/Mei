/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.DenseBasisTransport.Extension
public import Mathlib.Topology.Sheaves.Functors

/-!
# Morphisms between dense transport sheaves over open embeddings

A map of coefficients intertwining chart transport defines a morphism to the
existing target sheaf restricted along an open embedding. The dense coefficient
domains may differ: target coefficients at additional points are determined by
the transported dense values. Source sections need only be locally parallel.
We construct target sections on source local-predicate witnesses and use the
existing sheaf gluing theorem; agreement on the dense source points proves
uniqueness and naturality.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Set Topology TopCat

universe u v

namespace Mei.DenseBasisTransport

variable {X Y : TopCat.{u}} {S : Set X} {S' : Set Y} {M N : Type v}
  (T : DenseBasisTransport S M) (T' : DenseBasisTransport S' N)
  (j : X ⟶ Y) (hj : IsOpenEmbedding j) (q : S → S')
  (hq : ∀ x, (q x).val = j x.val)

include T hq in
private theorem exists_coefficient_in_image {U : Opens X} {V : Opens Y}
    (hVU : V ≤ hj.functor.obj U) (hne : (V : Set Y).Nonempty) :
    ∃ x : S, (q x).val ∈ V := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hz, rfl⟩ := hVU hy
  obtain ⟨x, hxV, hxS⟩ := T.dense.inter_open_nonempty
    ((Opens.map j).obj V) ((Opens.map j).obj V).isOpen ⟨z, hy⟩
  simp only [Opens.map_coe, Set.mem_preimage] at hxV
  exact ⟨⟨x, hxS⟩, by rw [hq]; exact hxV⟩

include T hq in
/-- On the image of a source open, target sections are determined by their values
at the mapped source coefficient points. -/
theorem section_ext_image {U : Opens X} {V : Opens Y} (hVU : V ≤ hj.functor.obj U)
    {s t : T'.sheaf.presheaf.obj (op V)}
    (h : ∀ x hx, T'.value s (q x) hx = T'.value t (q x) hx) : s = t :=
  T'.section_ext_of_exists_mem_open q
    (fun _ hW hne => T.exists_coefficient_in_image j hj q hq (hW.trans hVU) hne) h

include hq in
/-- A mapped coefficient point belongs to the image of every source open
containing it. Naming this proof keeps the transport-intertwining interface
available across Lean module boundaries. -/
theorem mem_image_of_mem (U : Opens X) (x : S) (hx : x.val ∈ U) :
    (q x).val ∈ hj.functor.obj U := by
  rw [hq]
  exact ⟨x.val, hx, rfl⟩

variable (φ : M → N)
  (hchart : ∀ B, B ∈ T.basis → hj.functor.obj B ∈ T'.basis)
  (htransport : ∀ B (hB : B ∈ T.basis) x y hx hy m,
    φ (T.transport B hB x y hx hy m) =
      T'.transport (hj.functor.obj B) (hchart B hB) (q x) (q y)
        (mem_image_of_mem j hj q hq B x hx)
        (mem_image_of_mem j hj q hq B y hy) (φ m))

private structure SectionChart (U : Opens X) (s : T.sheaf.presheaf.obj (op U)) where
  carrier : Opens X
  mem_basis : carrier ∈ T.basis
  le_domain : carrier ≤ U
  nonempty : (carrier : Set X).Nonempty
  parallel : T.prelocal.pred (fun x hx => T.value s ⟨x.val, hx⟩ (le_domain x.property))

private theorem exists_sectionChart {U : Opens X} (s : T.sheaf.presheaf.obj (op U))
    (x : X) (hx : x ∈ U) : ∃ B : T.SectionChart U s, x ∈ B.carrier := by
  obtain ⟨V, hxV, iV, hsV⟩ := T.locallyParallel_value s ⟨x, hx⟩
  obtain ⟨B, hB, hxB, hBV⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis hxV
  refine ⟨⟨B, hB, hBV.trans iV.le, ⟨x, hxB⟩, ?_⟩, hxB⟩
  exact T.prelocal.res (homOfLE hBV) _ hsV

private def chartAnchor {U : Opens X} {s : T.sheaf.presheaf.obj (op U)}
    (B : T.SectionChart U s) : S :=
  ⟨(T.dense.inter_open_nonempty B.carrier B.carrier.isOpen B.nonempty).choose,
    (T.dense.inter_open_nonempty B.carrier B.carrier.isOpen B.nonempty).choose_spec.2⟩

private theorem chartAnchor_mem {U : Opens X} {s : T.sheaf.presheaf.obj (op U)}
    (B : T.SectionChart U s) : (T.chartAnchor B).val ∈ B.carrier :=
  (T.dense.inter_open_nonempty B.carrier B.carrier.isOpen B.nonempty).choose_spec.1

private def chartSection {U : Opens X} {s : T.sheaf.presheaf.obj (op U)}
    (B : T.SectionChart U s) :
    T'.sheaf.presheaf.obj (op (hj.functor.obj B.carrier)) :=
  T'.parallelSection (hchart B.carrier B.mem_basis) le_rfl (q (T.chartAnchor B))
    (by rw [hq]; exact ⟨_, T.chartAnchor_mem B, rfl⟩)
    (φ (T.value s (T.chartAnchor B) (B.le_domain (T.chartAnchor_mem B))))

include htransport in
private theorem value_chartSection {U : Opens X} {s : T.sheaf.presheaf.obj (op U)}
    (B : T.SectionChart U s) (x : S) (hx : x.val ∈ B.carrier) :
    T'.value (T.chartSection T' j hj q hq φ hchart B) (q x)
      (by rw [hq]; exact ⟨x.val, hx, rfl⟩) =
        φ (T.value s x (B.le_domain hx)) := by
  dsimp only [chartSection]
  rw [value_parallelSection,
    ← htransport B.carrier B.mem_basis (T.chartAnchor B) x (T.chartAnchor_mem B) hx]
  have hp := B.parallel
  rw [prelocal_pred_iff] at hp
  rw [hp B.carrier B.mem_basis le_rfl (T.chartAnchor B) x (T.chartAnchor_mem B) hx]

include hq in
private theorem point_mem_image_iff (U : Opens X) (x : S) :
    (q x).val ∈ hj.functor.obj U ↔ x.val ∈ U := by
  rw [hq]
  constructor
  · rintro ⟨y, hy, he⟩
    exact hj.injective he ▸ hy
  · intro hx
    exact ⟨x.val, hx, rfl⟩

include htransport in
private theorem existsUnique_mapSection {U : Opens X} (s : T.sheaf.presheaf.obj (op U)) :
    ∃! t : T'.sheaf.presheaf.obj (op (hj.functor.obj U)),
      ∀ x hx, T'.value t (q x) (by rw [hq]; exact ⟨x.val, hx, rfl⟩) =
        φ (T.value s x hx) := by
  let cover (B : T.SectionChart U s) := hj.functor.obj B.carrier
  let localSection (B : T.SectionChart U s) := T.chartSection T' j hj q hq φ hchart B
  let inclusion (B : T.SectionChart U s) : cover B ⟶ hj.functor.obj U :=
    hj.functor.map (homOfLE B.le_domain)
  have hcover : hj.functor.obj U ≤ iSup cover := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨B, hxB⟩ := T.exists_sectionChart s x hx
    exact Opens.mem_iSup.mpr ⟨B, ⟨x, hxB, rfl⟩⟩
  have hcompatible : T'.sheaf.presheaf.IsCompatible cover localSection := by
    intro B C
    apply T.section_ext_image T' j hj q hq (U := U)
      (inf_le_left.trans (inclusion B).le)
    intro x hx
    have hxB := (point_mem_image_iff j hj q hq B.carrier x).mp hx.1
    have hxC := (point_mem_image_iff j hj q hq C.carrier x).mp hx.2
    exact (T'.value_restrict inf_le_left _ _ hx).trans
      ((T.value_chartSection T' j hj q hq φ hchart htransport B x hxB).trans
        ((T.value_chartSection T' j hj q hq φ hchart htransport C x hxC).symm.trans
          (T'.value_restrict inf_le_right _ _ hx).symm))
  obtain ⟨t, ht, _⟩ := T'.sheaf.existsUnique_gluing' cover
    (hj.functor.obj U) inclusion hcover localSection hcompatible
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hxB⟩ := T.exists_sectionChart s x.val hx
    have hxB' : (q x).val ∈ cover B := by rw [hq]; exact ⟨x.val, hxB, rfl⟩
    have he := (T'.value_restrict (inclusion B).le t (q x) hxB').symm.trans
      (congrArg (fun r => T'.value r (q x) hxB') (ht B))
    exact he.trans (T.value_chartSection T' j hj q hq φ hchart htransport B x hxB)
  · intro t' ht'
    apply T.section_ext_image T' j hj q hq le_rfl
    intro x hx
    have hxU := (point_mem_image_iff j hj q hq U x).mp hx
    obtain ⟨B, hxB⟩ := T.exists_sectionChart s x.val hxU
    have hxB' : (q x).val ∈ cover B := by rw [hq]; exact ⟨x.val, hxB, rfl⟩
    have he := (T'.value_restrict (inclusion B).le t (q x) hxB').symm.trans
      (congrArg (fun r => T'.value r (q x) hxB') (ht B))
    exact (ht' x hxU).trans
      (he.trans (T.value_chartSection T' j hj q hq φ hchart htransport B x hxB)).symm

private def mapSection {U : Opens X} (s : T.sheaf.presheaf.obj (op U)) :
    T'.sheaf.presheaf.obj (op (hj.functor.obj U)) :=
  (T.existsUnique_mapSection T' j hj q hq φ hchart htransport s).choose

private theorem value_mapSection {U : Opens X} (s : T.sheaf.presheaf.obj (op U))
    (x : S) (hx : x.val ∈ U) :
    T'.value (T.mapSection T' j hj q hq φ hchart htransport s) (q x)
      (by rw [hq]; exact ⟨x.val, hx, rfl⟩) = φ (T.value s x hx) :=
  (T.existsUnique_mapSection T' j hj q hq φ hchart htransport s).choose_spec.1 x hx

/-- The canonical target sheaf on the source space, with sections on the image
of each source open. This is the naive open-embedding pullback, allowing a larger
universe of coefficient values than that of the ambient spaces. -/
@[expose] def imageRestriction : X.Sheaf (Type (max u v)) :=
  ⟨hj.functor.op ⋙ T'.sheaf.presheaf,
    TopCat.Presheaf.isSheaf_of_isOpenEmbedding hj T'.sheaf.property⟩

/-- A coefficient map intertwining chart transport induces a morphism to the
existing target sheaf restricted along the ambient open embedding. -/
def mapOfIntertwining : T.sheaf ⟶ T'.imageRestriction j hj := by
  refine ⟨{ app := fun U => ↾(T.mapSection T' j hj q hq φ hchart htransport)
            naturality := ?_ }⟩
  intro U V i
  apply ConcreteCategory.hom_ext
  intro s
  apply T.section_ext_image T' j hj q hq le_rfl
  intro x hx
  have hxV := (point_mem_image_iff j hj q hq V.unop x).mp hx
  simp only [ConcreteCategory.comp_apply]
  -- The component homs are `mapSection`; `imageRestriction` maps `i` by the target
  -- restriction along the image-open map `hj.functor.map i.unop`.
  change T'.value (T.mapSection T' j hj q hq φ hchart htransport
      (T.sheaf.presheaf.map i s)) (q x) hx =
    T'.value (T'.sheaf.presheaf.map (hj.functor.map i.unop).op
      (T.mapSection T' j hj q hq φ hchart htransport s)) (q x) hx
  refine (T.value_mapSection T' j hj q hq φ hchart htransport
    (T.sheaf.presheaf.map i s) x hxV).trans
      (Eq.trans ?_ (T'.value_restrict (hj.functor.map i.unop).le _ (q x) hx).symm)
  rw [T.value_mapSection T' j hj q hq φ hchart htransport s x (i.unop.le hxV)]
  exact congrArg φ (T.value_restrict i.unop.le s x hxV)

/-- On every source coefficient point, the sheaf morphism applies the prescribed
coefficient map. Its target value exists even when other target points are missing
from the source coefficient domain. -/
@[simp]
theorem value_mapOfIntertwining {U : Opens X} (s : T.sheaf.presheaf.obj (op U))
    (x : S) (hx : x.val ∈ U) :
    T'.value ((T.mapOfIntertwining T' j hj q hq φ hchart htransport).hom.app (op U) s)
      (q x) (mem_image_of_mem j hj q hq U x hx) = φ (T.value s x hx) :=
  T.value_mapSection T' j hj q hq φ hchart htransport s x hx

/-- The value equation uniquely determines the entire sheaf morphism, including
its action on sections over every open domain. -/
theorem mapOfIntertwining_unique
    (α : T.sheaf ⟶ T'.imageRestriction j hj)
    (hα : ∀ U (s : T.sheaf.presheaf.obj (op U)) x hx,
      T'.value (α.hom.app (op U) s) (q x)
        (mem_image_of_mem j hj q hq U x hx) = φ (T.value s x hx)) :
    α = T.mapOfIntertwining T' j hj q hq φ hchart htransport := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply T.section_ext_image T' j hj q hq le_rfl
  intro x hx
  have hxU := (point_mem_image_iff j hj q hq U.unop x).mp hx
  exact (hα U.unop s x hxU).trans
    (T.value_mapOfIntertwining T' j hj q hq φ hchart htransport s x hxU).symm

end Mei.DenseBasisTransport
