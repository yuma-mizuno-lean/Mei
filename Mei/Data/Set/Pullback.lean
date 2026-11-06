/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Set.Lattice.Image

/-!
# Covers of pullback loci

A cover of a domain on which a function agrees with given functions induces a
cover of its pullback locus by the corresponding matching loci. No algebraic
structure or finiteness assumption is needed on the cover or the functions.
-/

public section

namespace Set

/-- Pulling back a function given on a covered domain amounts to taking the union
of the matching loci on its pieces. -/
theorem iUnion_pullback_pieces {V W X κ : Type*} {D : Set V} {f : D → W}
    (S : κ → Set V) (g : κ → V → W) (φ : X → W)
    (hD : (⋃ k, S k) = D)
    (hfg : ∀ k (v : D), v.1 ∈ S k → f v = g k v) :
    (⋃ k, Prod.fst ⁻¹' S k ∩ {p : V × X | g k p.1 = φ p.2}) =
      {p : V × X | ∃ hx : p.1 ∈ D, f ⟨p.1, hx⟩ = φ p.2} := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, he⟩
    have hx : p.1 ∈ D := hD ▸ Set.mem_iUnion.mpr ⟨k, hk⟩
    exact ⟨hx, (hfg k ⟨p.1, hx⟩ hk).trans he⟩
  · rintro ⟨hx, he⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hD.symm ▸ hx)
    exact ⟨k, hk, (hfg k ⟨p.1, hx⟩ hk).symm.trans he⟩

end Set
