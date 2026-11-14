/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.SemimoduleCat.Multispan.Refinement.Basic
public import Mei.Topology.Sheaves.Multispan.Restriction

/-!
# Gluing matching families in locally chosen subdivisions

Different endpoint patches may present the same coefficient diagram using
different subdivisions. Chamber and face copies are retained, and identity
faces may connect copies of each original chamber. Agreement of the original
chamber values on overlaps suffices for a unique global matching family whose
pullback recovers every local refined family, including all face components.

There is no common global subdivision or chosen comparison between the local
subdivisions. Covers, incidence diagrams and copy inventories may be infinite.
Identity-face graphs need not be connected: diagonal overlap compatibility
already identifies all chamber copies. Joint injectivity is assumed only on
pairwise-overlap sections, whose diagonal cases cover the individual patches.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat

universe u v r w

namespace CategoryTheory.Limits.MultispanIndex

variable {X : TopCat.{u}} {R : Type r} [Semiring R] {J : MultispanShape}

/-- Matching families on separately subdivided endpoint patches glue uniquely
when their original chamber values agree on overlaps. Every chamber and face
has a copy; identity-face graphs need not be connected. The global
family recovers all local refined components, not just the chamber evaluations. -/
theorem existsUnique_sections_gluing_of_local_subdivisions
    (I : MultispanIndex J (X.Sheaf (SemimoduleCat.{v} R)))
    (E : SemimoduleCat.{v} R) {ι : Type*} (U : ι → Opens X)
    (D : ι → MultispanShape.Subdivision.{w} J)
    [∀ i j, Nonempty ((D i).chambers j)] [∀ i b, Nonempty ((D i).faces b)]
    (hinjOverlap : ∀ i k b,
      Function.Injective (((I.sectionsIndex (U i ⊓ U k)).fst b).hom.prod
        ((I.sectionsIndex (U i ⊓ U k)).snd b).hom))
    (ℓ : ∀ i, E →ₗ[R]
      SemimoduleCat.sectionsSubmodule ((D i).index (I.sectionsIndex (U i))).multispan)
    (hcompat : ∀ i k a j (c : (D i).chambers j) (d : (D k).chambers j),
      (I.right j).obj.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op
          ((ℓ i a).val (.right ⟨j, c⟩)) =
        (I.right j).obj.map (homOfLE (inf_le_right : U i ⊓ U k ≤ U k)).op
          ((ℓ k a).val (.right ⟨j, d⟩))) :
    ∃! L : E →ₗ[R] SemimoduleCat.sectionsSubmodule (I.sectionsIndex (iSup U)).multispan,
      ∀ i, ((D i).sectionsPullback (I.sectionsIndex (U i))).comp
        ((I.sectionsRestrict (le_iSup U i)).comp L) = ℓ i := by
  classical
  have hinj i b : Function.Injective (((I.sectionsIndex (U i)).fst b).hom.prod
      ((I.sectionsIndex (U i)).snd b).hom) := by
    have h := hinjOverlap i i b
    rw [inf_idem] at h
    exact h
  have hconst i x j (c d : (D i).chambers j) :
      (ℓ i x).val (.right ⟨j, c⟩) = (ℓ i x).val (.right ⟨j, d⟩) := by
    have h := hcompat i i x j c d
    have hm : IsIso (homOfLE (inf_le_left : U i ⊓ U i ≤ U i)) :=
      ⟨⟨homOfLE (le_inf le_rfl le_rfl), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    exact ((asIso ((I.right j).obj.map
      (homOfLE (inf_le_left : U i ⊓ U i ≤ U i)).op)).toLinearEquivₛ.injective) h
  choose a hp using fun i =>
    ((D i).existsUnique_sectionsPullback_comp_eq_of_chambers_eq
      (I.sectionsIndex (U i)) (hinj i) (ℓ i) (hconst i)).exists
  have har i x j (c : (D i).chambers j) :
      (a i x).val (.right j) = (ℓ i x).val (.right ⟨j, c⟩) := by
    have h := congrArg (fun s => s.val (.right ⟨j, c⟩)) (LinearMap.congr_fun (hp i) x)
    erw [MultispanShape.Subdivision.sectionsPullback_apply_right] at h
    exact h
  let chosen i j : (D i).chambers j := Classical.choice inferInstance
  have ha i k : (I.sectionsRestrict (inf_le_left : U i ⊓ U k ≤ U i)).comp (a i) =
      (I.sectionsRestrict (inf_le_right : U i ⊓ U k ≤ U k)).comp (a k) := by
    apply (I.sectionsIndex (U i ⊓ U k)).linearMap_ext_of_injective
      (hinjOverlap i k)
    intro x j
    simp only [LinearMap.comp_apply, sectionsRestrict_apply_right]
    rw [har i x j (chosen i j), har k x j (chosen k j)]
    exact hcompat i k x j (chosen i j) (chosen k j)
  obtain ⟨L, hL, huniq⟩ := I.existsUnique_sections_gluing E U a ha
  refine ⟨L, ?_, ?_⟩
  · intro i
    rw [hL i]
    exact hp i
  · intro q hq
    apply huniq q
    intro i
    apply LinearMap.ext
    intro x
    apply (D i).sectionsPullback_injective_of_nonempty_faces (I.sectionsIndex (U i))
    exact (LinearMap.congr_fun (hq i) x).trans (LinearMap.congr_fun (hp i) x).symm

end CategoryTheory.Limits.MultispanIndex
