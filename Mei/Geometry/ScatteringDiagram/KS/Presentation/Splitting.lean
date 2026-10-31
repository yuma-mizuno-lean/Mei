/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall.Splitting
public import Mei.Geometry.ScatteringDiagram.KS.Presentation.Equivalence

/-!
# Transport under homogeneous splitting

Splitting the logarithms of an abelian-ray presentation into their actual
homogeneous degrees preserves every finite-order path product. The comparison
holds on common admissible vertex lists, including simultaneous crossings of
repeated or overlapping supports. Consequently the original and split
presentations are equivalent and give equivalent completed KS diagrams.
Coefficient change commutes with this splitting, and the transport comparison
allows coefficient maps that kill active labels.

The proof uses `IndexedWallPresentation.projection_eq_noncommProd_homogeneousPresentation`
and the crossing-event comparison
`WallComplement.segmentPathProduct_eq_of_crossingEventProduct_eq`.
Finite commuting products are regrouped by their original wall indices.
Coefficient naturality uses `IndexedWallPresentation.levelPathProduct_mapPathPrefunctor`.
This is homogeneous splitting of the abelian-ray presentations in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

namespace Mei.IndexedWallPresentation

universe u

variable {N V R ι : Type*} {L : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsAbelianRays d ℒ]
  (D : IndexedWallPresentation s d ℒ ι)

private def homogeneousParent (k : ℕ) (a : D.homogeneousPresentation.active k) : D.active k :=
  ⟨a.val.1, D.active_homogeneousPresentation_parent a.property⟩

private theorem homogeneousFiber_product (k : ℕ) (j : D.active k) (σ : ℤ)
    (T : Finset (D.homogeneousPresentation.active k × ℤ))
    (hT : ∀ a, a ∈ T ↔ a.1.val.1 = j.val ∧ a.2 = σ)
    (comm : (T : Set (D.homogeneousPresentation.active k × ℤ)).Pairwise (fun a b =>
      Commute (CompletedGroup.projection k (D.homogeneousPresentation.wall a.1).label ^ a.2)
        (CompletedGroup.projection k (D.homogeneousPresentation.wall b.1).label ^ b.2)))
    (hσ : σ = -1 ∨ σ = 1) :
    T.noncommProd
      (fun a => CompletedGroup.projection k (D.homogeneousPresentation.wall a.1).label ^ a.2)
      comm = CompletedGroup.projection k (D.wall j).label ^ σ := by
  classical
  let f (n : (D.wall j).ray.rayDegrees) :=
    CompletedGroup.projection k (D.homogeneousPresentation.wall ⟨j.val, n⟩).label
  have hc (n m : (D.wall j).ray.rayDegrees) : Commute (f n) (f m) := by
    simpa only [f, homogeneousPresentation_wall, IndexedWall.homogeneousFactor_label] using
      (d.commute_of_mem_completedRaySubgroup ℒ
      (d.homogeneousFactor_mem_completedRaySubgroup ℒ (D.wall j).label_mem n.val)
      (d.homogeneousFactor_mem_completedRaySubgroup ℒ (D.wall j).label_mem m.val)).map
        (CompletedGroup.projection k)
  have he : (D.homogeneousIndices k j).noncommProd (fun n => f n ^ σ)
      (fun n _ m _ _ => (hc n m).zpow_zpow _ _) =
      T.noncommProd
        (fun a => CompletedGroup.projection k (D.homogeneousPresentation.wall a.1).label ^ a.2)
        comm := by
    apply Finset.noncommProd_bij
      (i := fun n hn => (⟨⟨j.val, n⟩, (D.mem_homogeneousIndices k j n).mp hn⟩, σ))
    · intro n hn
      exact (hT _).mpr ⟨rfl, rfl⟩
    · intro n hn m hm he
      have hp : (⟨j.val, n⟩ : D.HomogeneousIndex) = ⟨j.val, m⟩ :=
        congrArg (fun a => a.1.val) he
      exact eq_of_heq (Sigma.mk.inj_iff.mp hp).2
    · rintro ⟨⟨⟨j', n⟩, ha⟩, τ⟩ ht
      obtain ⟨hj, rfl⟩ := (hT _).mp ht
      dsimp only at hj
      subst j'
      exact ⟨n, (D.mem_homogeneousIndices k j n).mpr ha, rfl⟩
    · intro n hn
      rfl
  rw [← he]
  rcases hσ with rfl | rfl
  · simp only [zpow_neg_one]
    rw [Finset.noncommProd_inv _ f (fun n _ m _ _ => hc n m)]
    exact congrArg Inv.inv (D.projection_eq_noncommProd_homogeneousPresentation k j).symm
  · simp only [zpow_one]
    exact (D.projection_eq_noncommProd_homogeneousPresentation k j).symm

variable [Module.Free ℤ N]

private theorem crossingEventProduct_homogeneousPresentation (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement
      (fun a : D.homogeneousPresentation.active k => (D.homogeneousPresentation.wall a).support)}
    (e : x ⟶ y) (e' : x' ⟶ y') (hx : x.val = x'.val) (hy : y.val = y'.val) (t : ℝ) :
    crossingEventProduct (fun j : D.active k => s.normal (D.wall j).ray.generator)
        (fun j => CompletedGroup.projection k (D.wall j).label) (D.activeLabels_commute k) e t =
      crossingEventProduct
        (fun a : D.homogeneousPresentation.active k =>
          s.normal (D.homogeneousPresentation.wall a).ray.generator)
        (fun a => CompletedGroup.projection k (D.homogeneousPresentation.wall a).label)
        (D.homogeneousPresentation.activeLabels_commute k) e' t := by
  classical
  let S := signedCrossingEvent
    (fun j : D.active k => s.normal (D.wall j).ray.generator) x y t
  let T := signedCrossingEvent
    (fun a : D.homogeneousPresentation.active k =>
      s.normal (D.homogeneousPresentation.wall a).ray.generator) x' y' t
  let p (a : D.homogeneousPresentation.active k × ℤ) := (D.homogeneousParent k a.1, a.2)
  have hmem (a : D.homogeneousPresentation.active k × ℤ) : a ∈ T ↔ p a ∈ S := by
    rcases a with ⟨a, σ⟩
    simp only [T, S, p, homogeneousParent, mem_signedCrossingEvent, mem_crossings,
      homogeneousPresentation_wall, IndexedWall.homogeneousFactor_support,
      IndexedWall.homogeneousFactor_ray, hx, hy]
  have hc := signedCrossingEvent_pairwise
    (fun a : D.homogeneousPresentation.active k =>
      s.normal (D.homogeneousPresentation.wall a).ray.generator) _
    (D.homogeneousPresentation.activeLabels_commute k) e' t
  -- Regroup a simultaneous split event by its original signed wall index.
  have he := Finset.noncommProd_fiberwise_of_maps_to T S p
    (fun a => CompletedGroup.projection k (D.homogeneousPresentation.wall a.1).label ^ a.2)
    hc (fun a ha => (hmem a).mp ha)
  rw [crossingEventProduct_eq_noncommProd _ _ _ e t
    (signedCrossingEvent_pairwise _ _ (D.activeLabels_commute k) e t),
    crossingEventProduct_eq_noncommProd _ _ _ e' t hc]
  refine Eq.trans ?_ he
  apply Finset.noncommProd_congr rfl
  rintro ⟨j, σ⟩ hj
  symm
  -- Each fiber contains exactly the retained homogeneous factors of one label.
  have hT (a : D.homogeneousPresentation.active k × ℤ) :
      a ∈ T.filter (p · = (j, σ)) ↔ a.1.val.1 = j.val ∧ a.2 = σ := by
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, he⟩
      exact ⟨congrArg Subtype.val (Prod.mk.inj he).1, (Prod.mk.inj he).2⟩
    · rintro ⟨ha, hσ⟩
      have he : p a = (j, σ) := Prod.ext (Subtype.ext ha) hσ
      exact ⟨(hmem a).mpr (he.symm ▸ hj), he⟩
  have hσ : σ = -1 ∨ σ = 1 := by
    have hs := ((mem_signedCrossingEvent _ _ _ _ j σ).mp hj).2
    rw [hs]
    split_ifs <;> simp
  exact D.homogeneousFiber_product k j σ _ hT _ hσ

/-- Homogeneous splitting preserves transport on every common admissible vertex
list, with the original sign and order of all crossing events. -/
theorem levelPathProduct_homogeneousPresentation (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement
      (fun a : D.homogeneousPresentation.active k => (D.homogeneousPresentation.wall a).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    D.levelPathProduct k p = D.homogeneousPresentation.levelPathProduct k q := by
  rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k),
    D.homogeneousPresentation.levelPathProduct_eq_wallPathProduct k q
      (D.homogeneousPresentation.activeLabels_commute k)]
  exact Quiver.Path.wallPathProduct_eq_of_segmentPathProduct_eq _ _ _ _ _ _
    (fun e e' hx hy => segmentPathProduct_eq_of_crossingEventProduct_eq _ _ _ _ _ _ e e'
      (fun t _ => D.crossingEventProduct_homogeneousPresentation k e e' hx hy t)) p q hpq

/-- Splitting each ray logarithm into its actual homogeneous degrees preserves
the presentation's equivalence class. -/
theorem homogeneousPresentation_equivalent : D.homogeneousPresentation.Equivalent D := by
  rw [equivalent_iff]
  intro k
  rw [levelEquivalent_def]
  intro x y x' y' p q hpq
  exact (D.levelPathProduct_homogeneousPresentation k q p hpq.symm).symm

/-- The completed KS diagrams of a presentation and its homogeneous splitting
are equivalent, even if their auxiliary subdivisions differ. -/
theorem toCompletedDiagram_homogeneousPresentation_equivalent :
    D.homogeneousPresentation.toCompletedDiagram.Equivalent D.toCompletedDiagram :=
  (D.homogeneousPresentation.equivalent_iff_toCompletedDiagram D).mp
    D.homogeneousPresentation_equivalent

section Map

variable {L' : Type u} [LieRing L'] [LieAlgebra R L']
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  {ℳ : N → Submodule R L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]
  [IsAbelianRays d ℳ]

/-- Splitting after coefficient change maps the original transport on every
common admissible vertex list. Killed labels and simultaneous crossings are
allowed; no injectivity or consistency is assumed. -/
theorem levelPathProduct_homogeneousPresentation_map
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement
      (fun a : (D.map f).homogeneousPresentation.active k =>
        ((D.map f).homogeneousPresentation.wall a).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    (D.map f).homogeneousPresentation.levelPathProduct k q =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.levelPathProduct k p) := by
  let r := (D.mapPathPrefunctor f k).mapPath p
  have hrq : r.vertices.map WallComplement.val = q.vertices.map WallComplement.val :=
    (D.vertices_mapPathPrefunctor f k p).trans hpq
  exact ((D.map f).levelPathProduct_homogeneousPresentation k r q hrq).symm.trans
    (D.levelPathProduct_mapPathPrefunctor f k p)

end Map
end Mei.IndexedWallPresentation
