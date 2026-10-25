/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Toric.Algebraic.RationalFunctional
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Rational-normal affine polyhedra

A presentation consists of finitely many continuous affine inequalities whose
linear parts are rational multiples of lattice characters. Offsets are arbitrary
real numbers. Distinct presentations may have the same carrier; no extensionality
of presentations is asserted. Rational offsets are a separate condition.
-/

public section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-- A finite rational-normal presentation, with arbitrary real affine offsets. -/
structure RationalAffinePolyhedron (h : TauCeti.Toric.IsIntegralLattice i) where
  /-- The number of inequalities, including any redundant inequalities. -/
  numConstraints : ℕ
  /-- The affine functions required to be nonpositive. -/
  inequality : Fin numConstraints → (V →ᴬ[ℝ] ℝ)
  /-- Every linear part is a rational multiple of a lattice character. -/
  rational_linear : ∀ j, Toric.IsRationalFunctional h (inequality j).toAffineMap.linear

namespace RationalAffinePolyhedron

variable {h : TauCeti.Toric.IsIntegralLattice i}

/-- The closed set defined by the affine inequalities. -/
def carrier (P : RationalAffinePolyhedron h) : Set V :=
  {x | ∀ j, P.inequality j x ≤ 0}

/-- Membership is simultaneous satisfaction of all inequalities. -/
@[simp]
theorem mem_carrier {P : RationalAffinePolyhedron h} {x : V} :
    x ∈ P.carrier ↔ ∀ j, P.inequality j x ≤ 0 := Iff.rfl

/-- The presentation is a convex polyhedron on the existing supplier's carrier. -/
theorem isConvexPolyhedron (P : RationalAffinePolyhedron h) :
    TauCeti.IsConvexPolyhedron P.carrier :=
  TauCeti.isConvexPolyhedron_setOf_forall P.inequality

/-- Rational-normal polyhedra are closed. -/
theorem isClosed (P : RationalAffinePolyhedron h) : IsClosed P.carrier :=
  P.isConvexPolyhedron.isClosed

/-- Rational-normal polyhedra are convex. -/
theorem convex (P : RationalAffinePolyhedron h) : Convex ℝ P.carrier :=
  P.isConvexPolyhedron.convex

/-- Rational offsets are additional data; the default presentation allows real offsets. -/
def HasRationalOffsets (P : RationalAffinePolyhedron h) : Prop :=
  ∀ j, ∃ q : ℚ, P.inequality j 0 = (q : ℝ)

/-- Rational offsets mean that every inequality takes a rational value at zero. -/
theorem hasRationalOffsets_iff {P : RationalAffinePolyhedron h} :
    P.HasRationalOffsets ↔ ∀ j, ∃ q : ℚ, P.inequality j 0 = (q : ℝ) := Iff.rfl

/-- Reindex a finite family of rational-normal inequalities by a finite ordinal. -/
noncomputable def ofFinite {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    RationalAffinePolyhedron h := by
  letI := Fintype.ofFinite ι
  exact ⟨Fintype.card ι, fun j => g ((Fintype.equivFin ι).symm j), fun j => hg _⟩

/-- Reindexing preserves the exact simultaneous-inequality carrier. -/
theorem mem_carrier_ofFinite {ι : Type*} [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) {x : V} :
    x ∈ (ofFinite g hg).carrier ↔ ∀ j, g j x ≤ 0 := by
  classical
  let _ := Fintype.ofFinite ι
  dsimp only [carrier, ofFinite, Set.mem_ofPred_eq]
  constructor
  · intro hx j
    simpa using hx ((Fintype.equivFin ι) j)
  · intro hx j
    exact hx _

/-- Finite reindexing preserves rational affine offsets. -/
theorem hasRationalOffsets_ofFinite {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (ho : ∀ j, ∃ q : ℚ, g j 0 = (q : ℝ)) : (ofFinite g hg).HasRationalOffsets := by
  classical
  let _ := Fintype.ofFinite ι
  exact fun j => ho _

/-- Intersect two presentations by retaining both families of inequalities. -/
noncomputable def inter (P Q : RationalAffinePolyhedron h) : RationalAffinePolyhedron h :=
  ofFinite (Sum.elim P.inequality Q.inequality) (by
    intro j
    cases j with
    | inl j => exact P.rational_linear j
    | inr j => exact Q.rational_linear j)

/-- Intersection of presentations has the intersection of their carriers. -/
@[simp]
theorem carrier_inter (P Q : RationalAffinePolyhedron h) :
    (P.inter Q).carrier = P.carrier ∩ Q.carrier := by
  ext x
  unfold inter
  rw [mem_carrier_ofFinite]
  simp [Sum.forall]

/-- The empty family of inequalities presents the entire space. -/
def univ (h : TauCeti.Toric.IsIntegralLattice i) : RationalAffinePolyhedron h :=
  ⟨0, Fin.elim0, fun j => Fin.elim0 j⟩

/-- The empty family has full carrier. -/
@[simp]
theorem carrier_univ (h : TauCeti.Toric.IsIntegralLattice i) :
    (univ h).carrier = Set.univ := by
  ext x
  simp [carrier, univ]

/-- A contradictory constant inequality presents the empty set. -/
def empty (h : TauCeti.Toric.IsIntegralLattice i) : RationalAffinePolyhedron h :=
  ⟨1, fun _ => ContinuousAffineMap.const ℝ V 1,
    fun _ => Toric.IsRationalFunctional.zero h⟩

/-- The contradictory constant inequality has empty carrier. -/
@[simp]
theorem carrier_empty (h : TauCeti.Toric.IsIntegralLattice i) :
    (empty h).carrier = ∅ := by
  ext x
  simp [carrier, empty]

variable {N' W : Type*} [AddCommGroup N'] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {i' : N' →+ W} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- Pull back a presentation along an affine map with rational linear part.
Translations may be arbitrary real vectors, as the offsets may be real. -/
def preimage (P : RationalAffinePolyhedron h) (f : W →ᴬ[ℝ] V)
    (hf : Toric.IsRationalLinearMap h' h f.toAffineMap.linear) :
    RationalAffinePolyhedron h' where
  numConstraints := P.numConstraints
  inequality j := (P.inequality j).comp f
  rational_linear j := hf.map_functional (P.rational_linear j)

/-- Pulling back the inequalities pulls back the carrier. -/
@[simp]
theorem carrier_preimage (P : RationalAffinePolyhedron h) (f : W →ᴬ[ℝ] V)
    (hf : Toric.IsRationalLinearMap h' h f.toAffineMap.linear) :
    (P.preimage f hf).carrier = f ⁻¹' P.carrier := by
  ext x
  rfl

end RationalAffinePolyhedron

/-- A set admits a finite rational-normal affine presentation. -/
def IsRationalNormalPolyhedron (h : TauCeti.Toric.IsIntegralLattice i) (P : Set V) : Prop :=
  ∃ Q : RationalAffinePolyhedron h, Q.carrier = P

/-- A rational polyhedron also admits rational offsets. -/
def IsRationalPolyhedron (h : TauCeti.Toric.IsIntegralLattice i) (P : Set V) : Prop :=
  ∃ Q : RationalAffinePolyhedron h, Q.carrier = P ∧ Q.HasRationalOffsets

/-- Rational-normal polyhedrality is the existence of a presentation with this carrier. -/
theorem isRationalNormalPolyhedron_iff {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V} :
    IsRationalNormalPolyhedron h P ↔ ∃ Q : RationalAffinePolyhedron h, Q.carrier = P :=
  Iff.rfl

/-- Rational polyhedrality additionally requires rational offsets in the presentation. -/
theorem isRationalPolyhedron_iff {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V} :
    IsRationalPolyhedron h P ↔
      ∃ Q : RationalAffinePolyhedron h, Q.carrier = P ∧ Q.HasRationalOffsets := Iff.rfl

end Mei
