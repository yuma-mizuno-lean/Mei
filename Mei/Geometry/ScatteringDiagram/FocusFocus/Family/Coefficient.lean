/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family.Theta

/-!
# Specialization of the complete focus-focus endpoint family

A scalar homomorphism identifies the target endpoint fiber with precisely the
source histories whose whole weights have nonzero image. The comparison retains
the incoming, crossing and constant sectors, the binomial and upper/lower labels,
the complete incoming exponent and the continuous path on the closed endpoint
chart. Thus coefficient reduction removes histories without changing the
geometry of any surviving history, including its terminal and singular limits.

The construction uses `slabThetaFamilyChartFiberEquiv` and Mathlib's
`Equiv.subtypeEquiv`. No new incoming data are chosen after restriction, and
boundary paths are not asserted admissible. Whole-component
propagation follows Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, §3 (arXiv:1601.07081v4). The slab coordinates
follow Gross–Siebert, *An Invitation to Toric Degenerations*, §2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

open Set AddMonoidAlgebra

namespace Mei.FocusFocus

variable {R S : Type*} [CommRing R] [CommRing S]
  (t c : R) (n b : ℤ) (φ : R →+* S)

/-- Specialize a complete chart whose whole decoration survives. Its geometric
labels are unchanged; the coefficient only supplies the new nonvanishing proof. -/
def slabThetaChartSpecialization (α : SlabThetaChartIndex t c n b)
    (hα : mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b α) ≠ 0) :
    SlabThetaChartIndex (φ t) (φ c) n b := by
  rcases α with α | α | u
  · exact .inl ⟨α.val, by
      refine ⟨?_, α.property.2⟩
      simpa using hα⟩
  · exact .inr (.inl (⟨α.1.val, by simpa using hα⟩, α.2))
  · exact .inr (.inr u)

@[simp]
theorem slabThetaChartSpecialization_incoming (α : IncomingSlabChartIndex c n b)
    (hα : mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b (.inl α)) ≠ 0) :
    slabThetaChartSpecialization t c n b φ (.inl α) hα =
      .inl ⟨α.val, ⟨by simpa using hα, α.property.2⟩⟩ := (rfl)

@[simp]
theorem slabThetaChartSpecialization_crossing (α : SlabChartIndex t c n)
    (hα : mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b (.inr (.inl α))) ≠ 0) :
    slabThetaChartSpecialization t c n b φ (.inr (.inl α)) hα =
      .inr (.inl (⟨α.1.val, by simpa using hα⟩, α.2)) := (rfl)

@[simp]
theorem slabThetaChartSpecialization_constant (u : Unit)
    (hα : mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b (.inr (.inr u))) ≠ 0) :
    slabThetaChartSpecialization t c n b φ (.inr (.inr u)) hα = .inr (.inr u) := (rfl)

private def sourceChart (α : SlabThetaChartIndex (φ t) (φ c) n b) :
    SlabThetaChartIndex t c n b := by
  rcases α with α | α | u
  · exact .inl ⟨α.val, ⟨fun hz => α.property.1 (by simp [hz]), α.property.2⟩⟩
  · exact .inr (.inl (⟨α.1.val, fun hz => α.1.property (by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg φ hz)⟩, α.2))
  · exact .inr (.inr u)

/-- Specialization applies the scalar map to the whole chart weight. -/
@[simp]
theorem slabThetaChartSpecialization_weight (α : SlabThetaChartIndex t c n b)
    (hα : mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b α) ≠ 0) :
    slabThetaChartWeight (φ t) (φ c) n b
        (slabThetaChartSpecialization t c n b φ α hα) =
      mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b α) := by
  rcases α with α | α | u <;>
    simp [slabThetaChartSpecialization]

/-- Every surviving chart has exactly the same valid endpoint domain. -/
@[simp]
theorem slabThetaChartSpecialization_domain (α : SlabThetaChartIndex t c n b)
    (hα : mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b α) ≠ 0) :
    slabThetaChartDomain (φ t) (φ c) n b
        (slabThetaChartSpecialization t c n b φ α hα) =
      slabThetaChartDomain t c n b α := by
  rcases α with α | α | u
  · simp [slabThetaChartSpecialization]
  · simp [slabThetaChartSpecialization]
  · have hc : φ c ≠ 0 := by simpa using hα
    have hc' : c ≠ 0 := fun hz => hc (by simp [hz])
    ext Q
    simp [slabThetaChartSpecialization, hc, hc']

/-- The whole continuous path agrees at every endpoint parameter, also outside
the valid chart and on its closed boundary. -/
@[simp]
theorem slabThetaChartSpecialization_path (α : SlabThetaChartIndex t c n b)
    (hα : mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b α) ≠ 0) :
    slabThetaChartPath (φ t) (φ c) n b
        (slabThetaChartSpecialization t c n b φ α hα) =
      slabThetaChartPath t c n b α := by
  rcases α with α | α | u
  · simp [slabThetaChartSpecialization]
  · simp [slabThetaChartSpecialization]
  · apply ContinuousMap.ext
    intro Q
    apply ContinuousMap.ext
    intro s
    simp [slabThetaChartSpecialization]

/-- The developed incoming exponent, including the upper-frame shift, survives
coefficient specialization unchanged. -/
@[simp]
theorem slabThetaChartSpecialization_incomingExponent (α : SlabThetaChartIndex t c n b)
    (hα : mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b α) ≠ 0) :
    slabThetaChartIncomingExponent (φ t) (φ c) n b
        (slabThetaChartSpecialization t c n b φ α hα) =
      slabThetaChartIncomingExponent t c n b α := by
  rcases α with α | α | u <;> simp [slabThetaChartSpecialization]

private theorem sourceChart_weight (α : SlabThetaChartIndex (φ t) (φ c) n b) :
    mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b (sourceChart t c n b φ α)) =
      slabThetaChartWeight (φ t) (φ c) n b α := by
  rcases α with α | α | u <;> simp [sourceChart]

private theorem sourceChart_mem_domain
    (α : SlabThetaChartIndex (φ t) (φ c) n b) {Q : ℝ × ℝ}
    (hQ : Q ∈ slabThetaChartDomain (φ t) (φ c) n b α) :
    Q ∈ slabThetaChartDomain t c n b (sourceChart t c n b φ α) := by
  rcases α with α | α | u
  · simpa only [sourceChart, slabThetaChartDomain_incoming] using hQ
  · simpa only [sourceChart, slabThetaChartDomain_crossing] using hQ
  · have hc := (mem_slabThetaChartDomain_constant (φ t) (φ c) n b Q u).mp hQ
    exact (mem_slabThetaChartDomain_constant t c n b Q u).mpr
      ⟨hc.1, fun hz => hc.2 (by simp [hz])⟩

/-- Identity specialization fixes every surviving complete chart. -/
@[simp]
theorem slabThetaChartSpecialization_id (α : SlabThetaChartIndex t c n b)
    (hα : mapRingHom (ℤ × ℤ) (RingHom.id R) (slabThetaChartWeight t c n b α) ≠ 0) :
    slabThetaChartSpecialization t c n b (RingHom.id R) α hα = α := by
  rcases α with α | α | u <;> rfl

/-- Successive specializations preserve the same complete chart as their
composite. Survival at the final ring implies survival at the intermediate one. -/
theorem slabThetaChartSpecialization_comp {T : Type*} [CommRing T]
    (ψ : S →+* T) (α : SlabThetaChartIndex t c n b)
    (hα : mapRingHom (ℤ × ℤ) (ψ.comp φ) (slabThetaChartWeight t c n b α) ≠ 0) :
    slabThetaChartSpecialization (φ t) (φ c) n b ψ
        (slabThetaChartSpecialization t c n b φ α (by
          intro hz
          apply hα
          rw [mapRingHom_comp, RingHom.comp_apply, hz, map_zero]))
        (by simpa only [slabThetaChartSpecialization_weight, mapRingHom_comp,
          RingHom.comp_apply] using hα) =
      slabThetaChartSpecialization t c n b (ψ.comp φ) α hα := by
  rcases α with α | α | u <;> rfl

variable (h : TauCeti.Toric.IsIntegralLattice
  ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

private def chartFiberEquiv (Q : ℝ × ℝ) :
    {α : {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α} //
      mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b α.val) ≠ 0} ≃
      {α : SlabThetaChartIndex (φ t) (φ c) n b //
        Q ∈ slabThetaChartDomain (φ t) (φ c) n b α} where
  toFun α := ⟨slabThetaChartSpecialization t c n b φ α.val.val α.property, by
    rw [slabThetaChartSpecialization_domain]
    exact α.val.property⟩
  invFun α := ⟨⟨sourceChart t c n b φ α.val,
    sourceChart_mem_domain t c n b φ α.val α.property⟩, by
      rw [sourceChart_weight]
      exact slabThetaChartWeight_ne_zero_of_mem_domain (φ t) (φ c) n b α.val α.property⟩
  left_inv α := by
    apply Subtype.ext
    apply Subtype.ext
    rcases α with ⟨⟨α | α | u, hQ⟩, hz⟩ <;> rfl
  right_inv α := by
    apply Subtype.ext
    rcases α with ⟨α | α | u, hQ⟩ <;> rfl

/-- Actual target fibers are exactly the surviving source histories. No
injectivity of the scalar map, nonzero input or generic endpoint is required. -/
def slabThetaFamilySpecializationEquiv (Q : ℝ × ℝ) :
    {z : (slabThetaFamily t c n b h).fiber Q //
      mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b z.1) ≠ 0} ≃
        (slabThetaFamily (φ t) (φ c) n b h).fiber Q :=
  ((slabThetaFamilyChartFiberEquiv t c n b h Q).symm.subtypeEquiv (fun z => by
    have he := slabThetaFamilyChartFiberEquiv_fst t c n b h Q
      ((slabThetaFamilyChartFiberEquiv t c n b h Q).symm z)
    rw [Equiv.apply_symm_apply] at he
    rw [← he])).trans
    ((chartFiberEquiv t c n b φ Q).trans
      (slabThetaFamilyChartFiberEquiv (φ t) (φ c) n b h Q))

/-- The exact fiber comparison retains the entire specialized chart label. -/
@[simp]
theorem slabThetaFamilySpecializationEquiv_fst (Q : ℝ × ℝ)
    (z : {z : (slabThetaFamily t c n b h).fiber Q //
      mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b z.1) ≠ 0}) :
    (slabThetaFamilySpecializationEquiv t c n b φ h Q z).1 =
      slabThetaChartSpecialization t c n b φ z.val.1 z.property := by
  have he := slabThetaFamilyChartFiberEquiv_fst t c n b h Q
    ((slabThetaFamilyChartFiberEquiv t c n b h Q).symm z.val)
  rw [Equiv.apply_symm_apply] at he
  simp only [slabThetaFamilySpecializationEquiv, Equiv.trans_apply,
    Equiv.subtypeEquiv_apply, chartFiberEquiv, Equiv.coe_fn_mk,
    slabThetaFamilyChartFiberEquiv_fst]
  congr 1
  exact he.symm

/-- Specializing the complete endpoint family commutes with its weighted sum.
Killed histories contribute zero, rather than becoming new zero-decorated paths. -/
theorem mapRingHom_slabThetaFamily_weightedEvaluation (Q : ℝ × ℝ) :
    mapRingHom (ℤ × ℤ) φ
        ((slabThetaFamily t c n b h).weightedEvaluation (slabThetaChartWeight t c n b) Q) =
      (slabThetaFamily (φ t) (φ c) n b h).weightedEvaluation
        (slabThetaChartWeight (φ t) (φ c) n b) Q := by
  classical
  let := Fintype.ofFinite ((slabThetaFamily t c n b h).fiber Q)
  let := Fintype.ofFinite ((slabThetaFamily (φ t) (φ c) n b h).fiber Q)
  let survivors := {z : (slabThetaFamily t c n b h).fiber Q |
    mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b z.1) ≠ 0}
  rw [FiniteSemilinearFamily.weightedEvaluation_def, map_sum,
    FiniteSemilinearFamily.weightedEvaluation_def]
  calc
    _ = ∑ z : survivors, mapRingHom (ℤ × ℤ) φ (slabThetaChartWeight t c n b z.val.1) :=
      Finset.sum_congr_set survivors _ _ (fun _ _ => rfl) (fun _ hz => not_ne_iff.mp hz)
    _ = _ := Fintype.sum_equiv (slabThetaFamilySpecializationEquiv t c n b φ h Q) _ _
      (fun z => by simp)

end Mei.FocusFocus
