/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Incoming.Affine
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Order.Setoid.Basic

/-!
# Simultaneous deck transport of incoming source records and tails

A family of one-chart incoming sources with compatible affine deck charts,
linear coefficient identifications and an action on incoming data has a genuine
group action on its admitted tails. The action moves the source, incoming datum
and full geometric representative together. Forgetting positions is equivariant,
so it descends to the deck quotients of tails and incoming type data.

This is the deck-identification part of incoming-tail transport. The source index
retains its degree and coefficient map. Chart/common-facet identifications beyond
the specified deck action and the construction of a developing cover are separate.
-/

public section

namespace Mei

variable {G I Γ V R E : Type*} [Group G] [MulAction G I]
  [AddCommMonoid Γ] [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [Semiring R] [AddCommMonoid E] [Module R E] [DistribMulAction G E]
  {M : Γ → Type*} [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  {v : Γ →+ V} (S : I → AffineIncomingSource R E M v)

/-- Compatibility data for simultaneous deck transport of a family of incoming sources. -/
structure AffineIncomingDeckData where
  /-- The additive action on incoming data is also linear over the coefficient semiring. -/
  datum_smul_comm : SMulCommClass G R E
  /-- The affine coordinate change belonging to each deck transformation. -/
  chart : G → V ≃ᴬ[ℝ] V
  /-- The identity deck transformation fixes coordinates. -/
  chart_one : chart 1 = ContinuousAffineEquiv.refl ℝ V
  /-- Charts follow the left-action composition convention. -/
  chart_mul : ∀ g h, chart (g * h) = (chart h).trans (chart g)
  /-- Coefficient identifications between the indicated source degrees. -/
  coefficientEquiv : ∀ (g : G) (i : I), M (S i).degree ≃ₗ[R] M (S (g • i)).degree
  /-- The source coefficient and incoming datum are transported together. -/
  coefficient_map : ∀ (g : G) (i : I) (a : E),
    (S (g • i)).coefficient (g • a) = coefficientEquiv g i ((S i).coefficient a)
  /-- The transported tail remains admitted by its transported source carrier. -/
  maps_carrier : ∀ (g : G) (i : I), chart g '' (S i).carrier ⊆ (S (g • i)).carrier
  /-- Geometric degree directions are transported by the same affine chart. -/
  map_direction : ∀ (g : G) (i : I), (chart g).linear (v (S i).degree) = v (S (g • i)).degree

variable {S}

/-- A source-labelled admitted tail before its deck identifications. The coefficient
and degree are determined by the source and datum, while positions remain in the tail. -/
structure AffineIncomingDeckTail (D : AffineIncomingDeckData (G := G) S) where
  /-- The incoming source record. -/
  source : I
  /-- The incoming datum at that source. -/
  datum : E
  /-- The full admitted affine representative. -/
  tail : AffineIncomingTail (S source) datum

namespace AffineIncomingDeckTail

variable {D : AffineIncomingDeckData (G := G) S}

/-- Source, datum and full geometric path determine a labelled tail. -/
@[ext]
theorem ext {β γ : AffineIncomingDeckTail D} (hs : β.source = γ.source)
    (ha : β.datum = γ.datum) (ht : ∀ t, β.tail t = γ.tail t) : β = γ := by
  cases β with
  | mk i a β =>
    cases γ with
    | mk j b γ =>
      dsimp only at hs ha ht
      cases hs
      cases ha
      have hβ : β = γ := AffineIncomingTail.ext (ContinuousAffineMap.ext ht)
      cases hβ
      rfl

/-- Apply a deck chart to the full tail, its source and its incoming datum. -/
def transport (g : G) (β : AffineIncomingDeckTail D) : AffineIncomingDeckTail D where
  source := g • β.source
  datum := g • β.datum
  tail := {
    representative := (D.chart g).toContinuousAffineMap.comp β.tail.representative
    velocity := by
      -- The linear projection of a bundled composition is composition of linear maps.
      have hlin : ((D.chart g).toContinuousAffineMap.comp β.tail.representative).linear 1 =
          (D.chart g).linear (β.tail.representative.linear 1) := rfl
      rw [hlin, β.tail.velocity, map_neg, D.map_direction]
    eventually_mem := β.tail.eventually_mem.mono fun t ht =>
      D.maps_carrier g β.source ⟨β.tail t, ht, rfl⟩
    coefficient_ne_zero := by
      rw [D.coefficient_map]
      exact (D.coefficientEquiv g β.source).map_ne_zero_iff.mpr β.tail.coefficient_ne_zero
    direction_ne_zero := by
      rw [← D.map_direction]
      exact (D.chart g).linear.map_ne_zero_iff.mpr β.tail.direction_ne_zero }

/-- The transported path applies the affine deck chart pointwise. -/
theorem transport_apply (g : G) (β : AffineIncomingDeckTail D) (t : ℝ) :
    (transport g β).tail t = D.chart g (β.tail t) := (rfl)

/-- The transport really acts on the source record. -/
theorem transport_source (g : G) (β : AffineIncomingDeckTail D) :
    (transport g β).source = g • β.source := (rfl)

/-- The transport acts on the input datum at the same time. -/
theorem transport_datum (g : G) (β : AffineIncomingDeckTail D) :
    (transport g β).datum = g • β.datum := (rfl)

instance : MulAction G (AffineIncomingDeckTail D) where
  smul := transport
  one_smul β := by
    apply ext
    · exact one_smul G β.source
    · exact one_smul G β.datum
    · intro t
      -- Expose the smul field of the instance being defined; no action equation exists yet.
      change (transport (1 : G) β).tail t = β.tail t
      simp only [transport_apply, D.chart_one, ContinuousAffineEquiv.refl_apply]
  mul_smul g h β := by
    apply ext
    · exact mul_smul g h β.source
    · exact mul_smul g h β.datum
    · intro t
      -- Expose the same local smul field before applying the public transport equation.
      change (transport (g * h) β).tail t = (transport g (transport h β)).tail t
      simp only [transport_apply, D.chart_mul, ContinuousAffineEquiv.trans_apply]

/-- The path evaluation equation for the group action. -/
@[simp]
theorem smul_tail_apply (g : G) (β : AffineIncomingDeckTail D) (t : ℝ) :
    (g • β).tail t = D.chart g (β.tail t) := transport_apply g β t

/-- The source label is transported by the group action. -/
@[simp]
theorem smul_source (g : G) (β : AffineIncomingDeckTail D) :
    (g • β).source = g • β.source := transport_source g β

/-- The incoming datum is transported by the group action. -/
@[simp]
theorem smul_datum (g : G) (β : AffineIncomingDeckTail D) :
    (g • β).datum = g • β.datum := transport_datum g β

/-- Forget the geometric position while retaining the source record and datum. -/
def sourceDatum : AffineIncomingDeckTail D →[G] (I × E) where
  toFun β := (β.source, β.datum)
  map_smul' _ _ := rfl

/-- The type datum retains the source record and its incoming datum. -/
@[simp]
theorem sourceDatum_apply (β : AffineIncomingDeckTail D) :
    sourceDatum β = (β.source, β.datum) := (rfl)

/-- The deck quotient of admitted tails, with geometric positions still present. -/
abbrev Orbit (D : AffineIncomingDeckData (G := G) S) :=
  MulAction.orbitRel.Quotient G (AffineIncomingDeckTail D)

/-- The coefficient-bearing source record, before deck identification. -/
def coefficientDatum (p : I × E) : Σ i, M (S i).degree :=
  ⟨p.1, (S p.1).coefficient p.2⟩

/-- Type data identify equal source coefficients as well as deck-related records.
In particular, they do not retain differences in the kernel of a source map. -/
def typeSetoid : Setoid (I × E) :=
  Setoid.ker (coefficientDatum (S := S)) ⊔ MulAction.orbitRel G (I × E)

omit [TopologicalSpace V] in
/-- The type relation is generated by equal coefficients and deck transport. -/
theorem typeSetoid_eq : typeSetoid (G := G) (S := S) =
    Setoid.ker (coefficientDatum (S := S)) ⊔ MulAction.orbitRel G (I × E) := (rfl)

omit [TopologicalSpace V] in
/-- The coefficient-bearing source record is computed by the source map. -/
@[simp]
theorem coefficientDatum_apply (p : I × E) :
    coefficientDatum (S := S) p = ⟨p.1, (S p.1).coefficient p.2⟩ := (rfl)

/-- Incoming type data retain the source degree and image coefficient, with positions
forgotten and the specified coefficient/deck identifications imposed. -/
abbrev TypeOrbit (S : I → AffineIncomingSource R E M v) :=
  Quotient (typeSetoid (G := G) (S := S))

/-- Forgetting positions descends to the actual deck quotients. -/
def orbitType : Orbit D → TypeOrbit (G := G) S :=
  Quotient.map sourceDatum fun β γ h => by
    obtain ⟨g, hg⟩ := h
    have hh : MulAction.orbitRel G (I × E) (sourceDatum β) (sourceDatum γ) :=
      ⟨g, (sourceDatum.map_smul g γ).symm.trans (congrArg sourceDatum hg)⟩
    have hle : MulAction.orbitRel G (I × E) ≤ typeSetoid (G := G) (S := S) := by
      rw [typeSetoid_eq]
      exact le_sup_right
    exact hle hh

omit [TopologicalSpace V] in
/-- Source inputs giving the same coefficient give the same incoming type datum. -/
theorem type_mk_eq_of_coefficient_eq (i : I) (a b : E)
    (h : (S i).coefficient a = (S i).coefficient b) :
    (Quotient.mk _ (i, a) : TypeOrbit (G := G) S) = Quotient.mk _ (i, b) := by
  apply Quotient.sound
  have hle : Setoid.ker (coefficientDatum (S := S)) ≤ typeSetoid (G := G) (S := S) := by
    rw [typeSetoid_eq]
    exact le_sup_left
  apply hle
  rw [Setoid.ker_def, coefficientDatum_apply, coefficientDatum_apply]
  exact congrArg (Sigma.mk i) h

/-- The quotient map has the expected value on every admitted representative. -/
@[simp]
theorem orbitType_mk (β : AffineIncomingDeckTail D) :
    orbitType (Quotient.mk _ β) = Quotient.mk _ (β.source, β.datum) := (rfl)

end AffineIncomingDeckTail
end Mei
