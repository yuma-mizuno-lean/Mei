/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Incoming.Deck.Basic

/-!
# Coefficient transport on deck quotients of incoming tails

A compatible change of degrees and coefficients transports incoming deck data.
The partial map on full tails is equivariant: vanishing of an image coefficient
is invariant under the deck action. Consequently the partial map descends to
actual tail orbits, while its surviving geometric representative is unchanged.
The induced map of incoming types forgets coefficient kernels and commutes with
the tail-to-type map on every surviving orbit.
-/

public section

namespace Mei

variable {G I Γ Γ' V R E : Type*} [Group G] [MulAction G I]
  [AddCommMonoid Γ] [AddCommMonoid Γ'] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] [Semiring R] [AddCommMonoid E] [Module R E]
  [DistribMulAction G E]
  {M : Γ → Type*} [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  {M' : Γ' → Type*} [∀ p, AddCommMonoid (M' p)] [∀ p, Module R (M' p)]
  {v : Γ →+ V} {S : I → AffineIncomingSource R E M v}
  (T : Γ →+ Γ') (w : Γ' →+ V) (hw : w.comp T = v)
  (ψ : ∀ p, M p →ₗ[R] M' (T p))

namespace AffineIncomingDeckData

/-- Transport compatible deck coefficient identifications along a coefficient map.
The square is required on all coefficients, allowing the map to have a kernel. -/
def regrade (D : AffineIncomingDeckData (G := G) S)
    (μ : ∀ (g : G) (i : I), M' (T (S i).degree) ≃ₗ[R] M' (T (S (g • i)).degree))
    (hμ : ∀ g i c, ψ (S (g • i)).degree (D.coefficientEquiv g i c) =
      μ g i (ψ (S i).degree c)) :
    AffineIncomingDeckData (G := G) (fun i => (S i).regrade T w hw ψ) where
  datum_smul_comm := D.datum_smul_comm
  chart := D.chart
  chart_one := D.chart_one
  chart_mul := D.chart_mul
  coefficientEquiv := μ
  coefficient_map g i a := by
    simp only [AffineIncomingSource.regrade_coefficient, D.coefficient_map, hμ]
    rfl
  maps_carrier := D.maps_carrier
  map_direction g i := by
    have h (p : Γ) : w (T p) = v p := DFunLike.congr_fun hw p
    simpa only [AffineIncomingSource.regrade_degree, h] using D.map_direction g i

/-- Coefficient transport uses the original affine deck charts. -/
@[simp]
theorem regrade_chart (D : AffineIncomingDeckData (G := G) S)
    (μ : ∀ (g : G) (i : I), M' (T (S i).degree) ≃ₗ[R] M' (T (S (g • i)).degree))
    (hμ : ∀ g i c, ψ (S (g • i)).degree (D.coefficientEquiv g i c) =
      μ g i (ψ (S i).degree c)) (g : G) :
    (D.regrade T w hw ψ μ hμ).chart g = D.chart g := (rfl)

/-- The transported deck coefficient identification is the specified target equivalence. -/
@[simp]
theorem regrade_coefficientEquiv (D : AffineIncomingDeckData (G := G) S)
    (μ : ∀ (g : G) (i : I), M' (T (S i).degree) ≃ₗ[R] M' (T (S (g • i)).degree))
    (hμ : ∀ g i c, ψ (S (g • i)).degree (D.coefficientEquiv g i c) =
      μ g i (ψ (S i).degree c)) (g : G) (i : I) :
    (D.regrade T w hw ψ μ hμ).coefficientEquiv g i = μ g i := (rfl)

end AffineIncomingDeckData

namespace AffineIncomingDeckTail

variable {D : AffineIncomingDeckData (G := G) S}
  (D' : AffineIncomingDeckData (G := G) (fun i => (S i).regrade T w hw ψ))
  (hchart : ∀ g, D'.chart g = D.chart g)

/-- Coefficient transport respects both the coefficient-kernel and deck identifications
of incoming type data. -/
def regradeType : TypeOrbit (G := G) S →
    TypeOrbit (G := G) (fun i => (S i).regrade T w hw ψ) :=
  Quotient.map id (by
    have hle : typeSetoid (G := G) (S := S) ≤
        typeSetoid (G := G) (S := fun i => (S i).regrade T w hw ψ) := by
      rw [typeSetoid_eq, typeSetoid_eq]
      apply sup_le_sup ?_ le_rfl
      intro a b h
      rw [Setoid.ker_def] at h ⊢
      simp only [coefficientDatum_apply] at h ⊢
      exact congrArg (fun q : Σ i, M (S i).degree =>
        (⟨q.1, ψ (S q.1).degree q.2⟩ : Σ i, M' (T (S i).degree))) h
    exact fun _ _ h => hle h)

/-- Transport a surviving labelled tail, keeping its source, datum and geometry. -/
def regrade (β : AffineIncomingDeckTail D)
    (ha : ψ (S β.source).degree ((S β.source).coefficient β.datum) ≠ 0) :
    AffineIncomingDeckTail D' where
  source := β.source
  datum := β.datum
  tail := β.tail.regrade T w hw ψ ha

/-- Coefficient transport retains the source label. -/
@[simp]
theorem regrade_source (β : AffineIncomingDeckTail D)
    (ha : ψ (S β.source).degree ((S β.source).coefficient β.datum) ≠ 0) :
    (regrade T w hw ψ D' β ha).source = β.source := (rfl)

/-- Coefficient transport retains the incoming datum. -/
@[simp]
theorem regrade_datum (β : AffineIncomingDeckTail D)
    (ha : ψ (S β.source).degree ((S β.source).coefficient β.datum) ≠ 0) :
    (regrade T w hw ψ D' β ha).datum = β.datum := (rfl)

/-- Surviving labelled tails keep every geometric point. -/
@[simp]
theorem regrade_tail_apply (β : AffineIncomingDeckTail D)
    (ha : ψ (S β.source).degree ((S β.source).coefficient β.datum) ≠ 0) (t : ℝ) :
    (regrade T w hw ψ D' β ha).tail t = β.tail t :=
  AffineIncomingTail.regrade_apply T w hw ψ β.tail ha t

/-- Partial transport removes a labelled tail precisely when its image coefficient vanishes. -/
noncomputable def regrade? (β : AffineIncomingDeckTail D) : Option (AffineIncomingDeckTail D') := by
  classical
  exact if h : ψ (S β.source).degree ((S β.source).coefficient β.datum) = 0 then none
    else some (regrade T w hw ψ D' β h)

/-- A surviving labelled tail is exactly the specified transport of the original tail. -/
@[simp]
theorem regrade?_eq_some (β : AffineIncomingDeckTail D)
    (ha : ψ (S β.source).degree ((S β.source).coefficient β.datum) ≠ 0) :
    regrade? T w hw ψ D' β = some (regrade T w hw ψ D' β ha) := by
  classical
  simp only [regrade?, dite_eq_right ha]

/-- A zero transported coefficient gives no tail. -/
@[simp]
theorem regrade?_eq_none_iff (β : AffineIncomingDeckTail D) :
    regrade? T w hw ψ D' β = none ↔
      ψ (S β.source).degree ((S β.source).coefficient β.datum) = 0 := by
  classical
  simp only [regrade?]
  split_ifs <;> simp_all

include D' in
/-- Deck action preserves survival under the coefficient map. -/
theorem regrade_coefficient_smul_eq_zero_iff (g : G) (β : AffineIncomingDeckTail D) :
    ψ (S (g • β.source)).degree ((S (g • β.source)).coefficient (g • β.datum)) = 0 ↔
      ψ (S β.source).degree ((S β.source).coefficient β.datum) = 0 := by
  -- Coefficient modules depend on the transported degree; allow its projection to reduce
  -- while rewriting the public coefficient equations.
  erw [← AffineIncomingSource.regrade_coefficient T w hw ψ (S (g • β.source))
    (g • β.datum), D'.coefficient_map,
    (D'.coefficientEquiv g β.source).map_eq_zero_iff,
    AffineIncomingSource.regrade_coefficient]
  rfl

include hchart in
/-- Applying a deck transformation and then truncating equals truncating first,
including deletion of a zero image coefficient. -/
theorem regrade?_smul (g : G) (β : AffineIncomingDeckTail D) :
    regrade? T w hw ψ D' (g • β) =
      (regrade? T w hw ψ D' β).map (fun γ => g • γ) := by
  classical
  have hz : ψ (S (g • β).source).degree ((S (g • β).source).coefficient (g • β).datum) =
      0 ↔ ψ (S β.source).degree ((S β.source).coefficient β.datum) = 0 :=
    by
      rw [smul_datum]
      have hs := congrArg (fun i => ψ (S i).degree ((S i).coefficient (g • β.datum)) = 0)
        (smul_source g β)
      exact hs.symm ▸ regrade_coefficient_smul_eq_zero_iff T w hw ψ D' g β
  by_cases h : ψ (S β.source).degree ((S β.source).coefficient β.datum) = 0
  · have hg := hz.mpr h
    simp only [regrade?, dite_eq_left h, dite_eq_left hg, Option.map_none]
  · have hg := mt hz.mp h
    simp only [regrade?, dite_eq_right h, dite_eq_right hg, Option.map_some,
      Option.some.injEq]
    apply ext
    · simp only [regrade_source, smul_source]
    · simp only [regrade_datum, smul_datum]
    · intro t
      rw [regrade_tail_apply, smul_tail_apply, smul_tail_apply, regrade_tail_apply, hchart]

/-- The partial coefficient map is well defined on actual deck orbits of full tails. -/
noncomputable def regradeOrbit? : Orbit D → Option (Orbit D') :=
  Quotient.lift (fun β => (regrade? T w hw ψ D' β).map (Quotient.mk _)) (by
    intro β γ h
    obtain ⟨g, rfl⟩ := h
    rw [regrade?_smul T w hw ψ D' hchart]
    simp only [Option.map_map]
    congr 1
    funext δ
    exact MulAction.orbitRel.Quotient.quotient_smul_eq (g := g) (a := δ))

/-- A represented orbit is mapped by truncating its actual representative. -/
@[simp]
theorem regradeOrbit?_mk (β : AffineIncomingDeckTail D) :
    regradeOrbit? T w hw ψ D' hchart (Quotient.mk _ β) =
      (regrade? T w hw ψ D' β).map (Quotient.mk _) := (rfl)

omit [TopologicalSpace V] in
/-- Type transport applies the coefficient change to each source record. -/
@[simp]
theorem regradeType_mk (p : I × E) :
    regradeType (G := G) (S := S) T w hw ψ (Quotient.mk _ p) = Quotient.mk _ p := (rfl)

/-- On every surviving orbit, coefficient transport commutes with forgetting positions. -/
theorem orbitType_regradeOrbit? (q : Orbit D) (q' : Orbit D')
    (h : regradeOrbit? T w hw ψ D' hchart q = some q') :
    orbitType q' = regradeType T w hw ψ (orbitType q) := by
  classical
  induction q using Quotient.inductionOn with
  | _ β =>
    rw [regradeOrbit?_mk] at h
    unfold regrade? at h
    split_ifs at h with hz
    · cases h
    · simp only [Option.map_some, Option.some.injEq] at h
      cases h
      rw [orbitType_mk, orbitType_mk, regradeType_mk, regrade_source, regrade_datum]

end AffineIncomingDeckTail
end Mei
