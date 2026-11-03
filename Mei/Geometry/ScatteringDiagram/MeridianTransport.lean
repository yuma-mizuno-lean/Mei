/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.CategoryTheory.Groupoid.SingleObj
public import Mei.Geometry.ScatteringDiagram.Groupoid

/-!
# Transport of groupoid-labelled diagrams and joint meridians

For a groupoid-labelled wall diagram on a complex covering the ambient space, the transport
around an admissible loop is trivial as soon as the transport around the isolating triangular
meridians of the joints is, and transport along admissible paths that are homotopic in an
open region agrees as soon as the meridians of the joints in that region have trivial transport.
This is the groupoid form of `Mei.FiniteWallDiagram.consistent_iff_jointMeridianWords` and
`Mei.FiniteWallDiagram.pathProduct_eq_of_homotopy`.

The proof reduces to the group case. A faithful functor from the groupoid to a group
(`CategoryTheory.Groupoid.exists_faithful_functor_singleObj`) turns the diagram into a
group-labelled one with the same joint meridians, whose path products are the images of the
transports.
-/

public section

noncomputable section

open CategoryTheory Set Mei.Convex Mei.Convex.WallComplement Mei.FinitePolyhedralComplex

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace GroupoidWallDiagram

variable {C : FinitePolyhedralComplex h} {G : Type*} [Groupoid G] (D : GroupoidWallDiagram C G)
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- The transport of a diagram around every isolating triangular meridian of a joint in the
region `U` is trivial. -/
def JointMeridiansTrivial (U : Set V) : Prop :=
  ∀ (x y z : WallComplement (fun P : C.walls => (P : Set V)))
    (e : x ⟶ y) (f : y ⟶ z) (r : z ⟶ x),
    ((e.toPath.cons f).cons r).crossingWord D.normal ∈ C.jointMeridianWords D.normal U →
      D.transport ((e.toPath.cons f).cons r) = 𝟙 _

/-- The defining condition of `JointMeridiansTrivial`. -/
theorem jointMeridiansTrivial_def (U : Set V) :
    D.JointMeridiansTrivial U ↔
      ∀ (x y z : WallComplement (fun P : C.walls => (P : Set V)))
        (e : x ⟶ y) (f : y ⟶ z) (r : z ⟶ x),
        ((e.toPath.cons f).cons r).crossingWord D.normal ∈ C.jointMeridianWords D.normal U →
          D.transport ((e.toPath.cons f).cons r) = 𝟙 _ := Iff.rfl

/-- If the transport of a diagram around the joint meridians in `U` is trivial, the labels of
its image under a functor to a group kill the words of those meridians. -/
private theorem lift_label_eq_one_of_jointMeridiansTrivial {H : Type*} [Group H] {U : Set V}
    (hD : D.JointMeridiansTrivial U) (Φ : G ⥤ SingleObj H)
    {g : FreeGroup C.walls}
    (hg : g ∈ C.jointMeridianWords (D.map Φ).toFiniteWallDiagram.normal U) :
    FreeGroup.lift (D.map Φ).toFiniteWallDiagram.label g = 1 := by
  rw [GroupoidWallDiagram.toFiniteWallDiagram_normal] at hg
  obtain ⟨x, y, z, e, f, r, -, -, -, rfl⟩ :=
    (C.mem_triangleWords _ U g).mp (C.jointMeridianWords_subset_triangleWords _ U hg)
  have h := pathProduct_map_toFiniteWallDiagram D Φ ((e.toPath.cons f).cons r)
  rw [hD x y z e f r hg, CategoryTheory.Functor.map_id] at h
  rw [FiniteWallDiagram.pathProduct_def, GroupoidWallDiagram.toFiniteWallDiagram_normal] at h
  exact h.trans (SingleObj.id_as_one _ _)

/-- **Homotopy invariance of transport.** For a complex covering the ambient space, if the
transport around the isolating triangular meridians of the joints in an open region `U` is
trivial, then admissible paths whose realizations are homotopic in `U` relative to their
endpoints have the same transport. -/
theorem transport_eq_of_homotopy (hC : C.support = univ) {U : Set V} (hUo : IsOpen U)
    (hD : D.JointMeridiansTrivial U) (p q : AdmissiblePLPath x y)
    (F : p.toContinuousPath.Homotopy q.toContinuousPath) (hF : ∀ z, F z ∈ U) :
    D.transport p = D.transport q := by
  obtain ⟨H, _, Φ, hΦ⟩ := Groupoid.exists_faithful_functor_singleObj G
  apply hΦ.map_injective
  rw [← pathProduct_map_toFiniteWallDiagram D Φ p, ← pathProduct_map_toFiniteWallDiagram D Φ q]
  exact (D.map Φ).toFiniteWallDiagram.pathProduct_eq_of_homotopy hC hUo
    (fun _ hg => lift_label_eq_one_of_jointMeridiansTrivial D hD Φ hg) p q F hF

/-- For a complex covering the ambient space, the transport around every admissible loop is
trivial exactly when the transport around the isolating triangular meridians of all joints is. -/
theorem forall_transport_eq_id_iff_jointMeridiansTrivial (hC : C.support = univ) :
    (∀ (x : WallComplement (fun P : C.walls => (P : Set V))) (p : AdmissiblePLPath x x),
      D.transport p = 𝟙 _) ↔ D.JointMeridiansTrivial univ := by
  constructor
  · intro hD x y z e f r _
    exact hD x _
  · intro hD x p
    obtain ⟨H, _, Φ, hΦ⟩ := Groupoid.exists_faithful_functor_singleObj G
    apply hΦ.map_injective
    have hcons := ((D.map Φ).toFiniteWallDiagram.consistent_iff_jointMeridianWords hC).mpr
      (fun _ hg => lift_label_eq_one_of_jointMeridiansTrivial D hD Φ hg)
    rw [← pathProduct_map_toFiniteWallDiagram D Φ p,
      (D.map Φ).toFiniteWallDiagram.consistent_def.mp hcons p .nil,
      (D.map Φ).toFiniteWallDiagram.pathProduct_nil, CategoryTheory.Functor.map_id]
    exact (SingleObj.id_as_one _ _).symm

end GroupoidWallDiagram

end Mei
