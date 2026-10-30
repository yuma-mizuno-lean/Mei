/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.DenseBasisTransport

/-!
# Extending generic coefficients to the transport sheaf

Values on a dense collection of coefficient points extend uniquely to a section
when they obey the specified transport on every chart. The construction fills in
all coefficient points by transport from a generic point in a chart; density and
the cocycle law prove independence on overlaps. The resulting section belongs to
the existing ambient sheaf, including across points with no coefficient values.

Ordinary local constancy on the generic domain is not assumed to imply extension:
the hypothesis compares every two generic points of an ambient transport chart.
No topology or injectivity is required on the indexing type of generic points.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Set Topology TopCat

universe u v w

namespace Mei.DenseBasisTransport

variable {X : TopCat.{u}} {S : Set X} {M : Type v}
  (T : DenseBasisTransport S M) {A : Type w} (q : A → S)
  (hd : DenseRange (fun a => (q a).val))

include hd

/-- A section is determined by its values on any ambient-dense collection of
coefficient points, even when the coefficient domain is larger. -/
theorem section_ext_of_dense {U : Opens X} {s t : T.sheaf.presheaf.obj (op U)}
    (h : ∀ a ha, T.value s (q a) ha = T.value t (q a) ha) : s = t := by
  apply T.section_ext
  intro x hx
  obtain ⟨V, hxV, iV, hsV⟩ := T.locallyParallel_value s ⟨x.val, hx⟩
  obtain ⟨W, hxW, iW, htW⟩ := T.locallyParallel_value t ⟨x.val, hx⟩
  rw [prelocal_pred_iff] at hsV htW
  -- Specify the intersection so the basis-neighborhood API can infer its open set.
  obtain ⟨B, hB, hxB, hBVW⟩ :=
    Opens.isBasis_iff_nbhd.mp T.isBasis (show x.val ∈ V ⊓ W from ⟨hxV, hxW⟩)
  have hBV : B ≤ V := hBVW.trans inf_le_left
  have hBW : B ≤ W := hBVW.trans inf_le_right
  obtain ⟨a, ha⟩ := hd.exists_mem_open B.isOpen ⟨x.val, hxB⟩
  apply (T.transport B hB x (q a) hxB ha).injective
  exact (hsV B hB hBV x (q a) hxB ha).trans
    ((h a (iV.le (hBV ha))).trans (htW B hB hBW x (q a) hxB ha).symm)

variable (f : A → M)
  (hf : ∀ B (hB : B ∈ T.basis) a b ha hb,
    T.transport B hB (q a) (q b) ha hb (f a) = f b)

include hf

/-- Chartwise transport from generic anchors gives the same value wherever the
charts overlap. The common comparison point is supplied by ambient density. -/
private theorem transport_generic_eq {B C : Opens X} (hB : B ∈ T.basis) (hC : C ∈ T.basis)
    (x : S) (hxB : x.val ∈ B) (hxC : x.val ∈ C)
    (a b : A) (ha : (q a).val ∈ B) (hb : (q b).val ∈ C) :
    T.transport B hB (q a) x ha hxB (f a) =
      T.transport C hC (q b) x hb hxC (f b) := by
  -- Specify the intersection so the basis-neighborhood API can infer its open set.
  obtain ⟨W, hW, hxW, hWBC⟩ :=
    Opens.isBasis_iff_nbhd.mp T.isBasis (show x.val ∈ B ⊓ C from ⟨hxB, hxC⟩)
  have hWB : W ≤ B := hWBC.trans inf_le_left
  have hWC : W ≤ C := hWBC.trans inf_le_right
  obtain ⟨c, hc⟩ := hd.exists_mem_open W.isOpen ⟨x.val, hxW⟩
  have hBac := congrArg (fun e => e (f a))
    (T.transport_trans B hB (q a) (q c) x ha (hWB hc) hxB)
  have hCbc := congrArg (fun e => e (f b))
    (T.transport_trans C hC (q b) (q c) x hb (hWC hc) hxC)
  simp only [Equiv.trans_apply] at hBac hCbc
  rw [hf B hB a c ha (hWB hc)] at hBac
  rw [hf C hC b c hb (hWC hc)] at hCbc
  calc
    _ = T.transport B hB (q c) x (hWB hc) hxB (f c) := hBac.symm
    _ = T.transport W hW (q c) x hc hxW (f c) :=
      congrArg (fun e => e (f c)) (T.transport_restrict hW hB hWB (q c) x hc hxW).symm
    _ = T.transport C hC (q c) x (hWC hc) hxC (f c) :=
      congrArg (fun e => e (f c)) (T.transport_restrict hW hC hWC (q c) x hc hxW)
    _ = _ := hCbc

/-- Generic coefficients satisfying ambient chart transport extend uniquely to
a global section of the original transport sheaf. -/
theorem existsUnique_section_of_dense :
    ∃! s : T.sheaf.presheaf.obj (op (⊤ : Opens X)),
      ∀ a, T.value s (q a) (by trivial) = f a := by
  have hex (x : S) : ∃ m : M, ∃ (B : Opens X) (hB : B ∈ T.basis) (hx : x.val ∈ B)
      (a : A) (ha : (q a).val ∈ B), m = T.transport B hB (q a) x ha hx (f a) := by
    obtain ⟨B, hB, hxB, _⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis (Opens.mem_top x.val)
    obtain ⟨a, ha⟩ := hd.exists_mem_open B.isOpen ⟨x.val, hxB⟩
    exact ⟨_, B, hB, hxB, a, ha, rfl⟩
  let g (x : S) : M := (hex x).choose
  have hg (B : Opens X) (hB : B ∈ T.basis) (x : S) (hx : x.val ∈ B)
      (a : A) (ha : (q a).val ∈ B) : g x = T.transport B hB (q a) x ha hx (f a) := by
    obtain ⟨C, hC, hxC, b, hb, he⟩ := (hex x).choose_spec
    exact he.trans (T.transport_generic_eq q hd f hf hC hB x hxC hx b a hb ha)
  let s : T.sheaf.presheaf.obj (op (⊤ : Opens X)) :=
    T.sectionOfLocallyParallel (fun x hx => g ⟨x.val, hx⟩)
      (PrelocalPredicate.sheafifyOf (by
        rw [prelocal_pred_iff]
        intro B hB _ x y hx hy
        obtain ⟨a, ha⟩ := hd.exists_mem_open B.isOpen ⟨x.val, hx⟩
        simp only [Subtype.coe_eta]
        rw [hg B hB x hx a ha, hg B hB y hy a ha]
        exact congrArg (fun e => e (f a)) (T.transport_trans B hB (q a) x y ha hx hy)))
  refine ⟨s, ?_, ?_⟩
  · intro a
    obtain ⟨B, hB, haB, _⟩ :=
      Opens.isBasis_iff_nbhd.mp T.isBasis (Opens.mem_top (q a).val)
    dsimp only [s]
    rw [value_sectionOfLocallyParallel]
    simpa only [Subtype.coe_eta, T.transport_self, Equiv.refl_apply] using
      hg B hB (q a) haB a haB
  · intro t ht
    apply T.section_ext_of_dense q hd
    intro a ha
    exact (ht a).trans (by
      obtain ⟨B, hB, haB, _⟩ :=
        Opens.isBasis_iff_nbhd.mp T.isBasis (Opens.mem_top (q a).val)
      dsimp only [s]
      rw [value_sectionOfLocallyParallel]
      simpa only [Subtype.coe_eta, T.transport_self, Equiv.refl_apply] using
        (hg B hB (q a) haB a haB).symm)

end Mei.DenseBasisTransport
