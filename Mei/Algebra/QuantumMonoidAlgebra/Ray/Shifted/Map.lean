/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Map
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Quotient

/-!
# Naturality of shifted quantum ray actions

Compatible scalar and positive degree maps intertwine shifted ray actions and
reverse crossings at every ambient origin. Neither map needs to be injective. Finite actions are
intertwined at the source cutoff specified by the degree map modulus. The ray
character uses the skew part of the bilinear form, so neither form needs to be alternating.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "G" => positiveFiltration q' β' e.monoid e.degree (fun _ h => e.degree_nonneg h)
local notation "Ψ" => mapPositiveCompletion d e T φ h
local notation "ψ" => positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn)

private theorem mapPositiveCompletion_apply_eq (a : (F).completion) :
    Ψ a = (F).mapCompletion G ψ T.modulus T.monotone_modulus
      (positiveMap_ideal_le d e T φ h) a := by
  apply (G).completion_ext
  intro k
  exact (projection_mapPositiveCompletion d e T φ h k a).trans
    ((F).projection_mapCompletion G ψ T.modulus T.monotone_modulus
      (positiveMap_ideal_le d e T φ h) k a).symm

/-- Positive degree maps send positive quantum rays to positive quantum rays. -/
theorem mappedRay_degree_pos (n : d.monoid) (hn : 0 < d.degree n) :
    0 < e.degree (T n) := by
  apply e.degree_pos (T.map_mem n.property)
  apply T.map_ne_zero n.property
  intro hz
  simp only [hz, map_zero, lt_self_iff_false] at hn

private theorem positiveMap_firstIdeal_le : (F).ideal 1 ≤ ((G).ideal 1).comap ψ :=
  positiveMap_ideal_le_of_degree φ T.toAddMonoidHom h d.monoid e.monoid
      (fun _ hn => T.map_mem hn) d.degree e.degree
      (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn) 1 1
      (fun n hn hd => mappedRay_degree_pos d e T ⟨n, hn⟩ hd)

include h in
/-- Factor-set transport preserves the skew commutation character without alternation. -/
theorem map_shiftedRay_character_skew (n p : Γ) :
    φ (((q ^ (β n p - β p n) : Rˣ) : R)) =
      ((q' ^ (β' (T n) (T p) - β' (T p) (T n)) : Sˣ) : S) := by
  have hc : Units.map φ.toMonoidHom (q ^ (β n p - β p n)) =
      q' ^ (β' (T n) (T p) - β' (T p) (T n)) := by
    rw [zpow_sub, map_mul, map_inv, h, h, ← zpow_sub]
  simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using
    congrArg Units.val hc

private theorem mapPositiveCompletion_twistedRay_of_character (n : d.monoid) (hn : 0 < d.degree n)
    (c : R) (c' : S) (hc : φ c = c') (H : (PowerSeries R)ˣ) (a : (F).completion) :
    Ψ ((F).completedTwistedSeriesAction
      (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
      c H a) =
    (G).completedTwistedSeriesAction
      (completedRayGenerator q' β' e.monoid e.degree (fun _ h => e.degree_nonneg h)
        ⟨T n, T.map_mem n.property⟩ (mappedRay_degree_pos d e T n hn))
      c' (Units.map (PowerSeries.map φ).toMonoidHom H) (Ψ a) := by
  have hx : Ψ (completedRayGenerator q β d.monoid d.degree
      (fun _ h => d.degree_nonneg h) n hn : (F).completion) =
    (completedRayGenerator q' β' e.monoid e.degree (fun _ h => e.degree_nonneg h)
      ⟨T n, T.map_mem n.property⟩ (mappedRay_degree_pos d e T n hn) : (G).completion) := by
    simp only [coe_completedRayGenerator, mapPositiveCompletion_toCompletion,
      positiveMap_positiveMonomial]
  have ht := (F).mapCompletion_completedTwistedSeriesAction_of_eq G φ ψ
    (positiveMap_algebraMap φ T.toAddMonoidHom h d.monoid e.monoid
      (fun _ hn => T.map_mem hn)) T.modulus T.monotone_modulus
    (positiveMap_ideal_le d e T φ h) (positiveMap_firstIdeal_le d e T φ h)
    (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
    (completedRayGenerator q' β' e.monoid e.degree (fun _ h => e.degree_nonneg h)
      ⟨T n, T.map_mem n.property⟩ (mappedRay_degree_pos d e T n hn))
    ((mapPositiveCompletion_apply_eq d e T φ h _).symm.trans hx)
    c c' hc H a
  have hi := mapPositiveCompletion_apply_eq d e T φ h
    ((F).completedTwistedSeriesAction
      (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
      c H a)
  have ho := congrArg ((G).completedTwistedSeriesAction
    (completedRayGenerator q' β' e.monoid e.degree (fun _ h => e.degree_nonneg h)
      ⟨T n, T.map_mem n.property⟩ (mappedRay_degree_pos d e T n hn))
    c' (Units.map (PowerSeries.map φ).toMonoidHom H))
    (mapPositiveCompletion_apply_eq d e T φ h a)
  exact hi.trans (ht.trans ho.symm)

/-- Positive transport intertwines ray twists given by arbitrary bilinear commutation characters. -/
theorem mapPositiveCompletion_twistedRay_skew (n : d.monoid) (hn : 0 < d.degree n)
    (p : Γ) (H : (PowerSeries R)ˣ) (a : (F).completion) :
    Ψ ((F).completedTwistedSeriesAction
      (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
      (((q ^ (β n p - β p n) : Rˣ) : R)) H a) =
    (G).completedTwistedSeriesAction
      (completedRayGenerator q' β' e.monoid e.degree (fun _ h => e.degree_nonneg h)
        ⟨T n, T.map_mem n.property⟩ (mappedRay_degree_pos d e T n hn))
      (((q' ^ (β' (T n) (T p) - β' (T p) (T n)) : Sˣ) : S))
      (Units.map (PowerSeries.map φ).toMonoidHom H) (Ψ a) :=
  mapPositiveCompletion_twistedRay_of_character d e T φ h n hn _ _
    (map_shiftedRay_character_skew d e T φ h n p) H a

private theorem map_action_coordinates
    (n : d.monoid) (hn : 0 < d.degree n)
    (p : Γ) (H : (PowerSeries R)ˣ) (a : (F).completion) :
    mapShiftedCompletion d e T φ h p
      (shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p a)) =
    shiftedRayAction q' β' e ⟨T n, T.map_mem n.property⟩
      (mappedRay_degree_pos d e T n hn) (T p)
      (Units.map (PowerSeries.map φ).toMonoidHom H)
      (mapShiftedCompletion d e T φ h p
        (positiveCompletionShiftEquiv q β d p a)) := by
  have ht := mapPositiveCompletion_twistedRay_skew d e T φ h n hn p H a
  simp only [AlgFiltration.completedTwistedSeriesAction_apply] at ht
  have hi := congrArg (mapShiftedCompletion d e T φ h p)
    (shiftedRayAction_coordinates_skew q β d n hn p H a)
  have hm := mapShiftedCompletion_coordinates d e T φ h p
    ((F).completedAeval
      (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
      (PowerSeries.rescale (((q ^ (β n p - β p n) : Rˣ) : R)) (H : PowerSeries R)) * a *
      (F).completedAeval
        (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
        (↑(H⁻¹) : PowerSeries R))
  have he := congrArg (positiveCompletionShiftEquiv q' β' e (T p)) ht
  have ho := shiftedRayAction_coordinates_skew q' β' e ⟨T n, T.map_mem n.property⟩
    (mappedRay_degree_pos d e T n hn) (T p)
    (Units.map (PowerSeries.map φ).toMonoidHom H) (Ψ a)
  have hc := congrArg (shiftedRayAction q' β' e ⟨T n, T.map_mem n.property⟩
    (mappedRay_degree_pos d e T n hn) (T p) (Units.map (PowerSeries.map φ).toMonoidHom H))
    (mapShiftedCompletion_coordinates d e T φ h p a)
  -- Change to positive coordinates, transport the twist, then return to the target shift.
  calc
    _ = _ := hi
    _ = _ := hm
    _ = _ := he
    _ = _ := ho.symm
    _ = _ := hc.symm

/-- Scalar and exponent maps intertwine quantum ray actions on every shifted coefficient. -/
theorem mapShiftedCompletion_shiftedRayAction
    (n : d.monoid) (hn : 0 < d.degree n)
    (p : Γ) (H : (PowerSeries R)ˣ) (a : d.ShiftedCoefficients (grade q β) p) :
    mapShiftedCompletion d e T φ h p (shiftedRayAction q β d n hn p H a) =
    shiftedRayAction q' β' e ⟨T n, T.map_mem n.property⟩
      (mappedRay_degree_pos d e T n hn) (T p)
      (Units.map (PowerSeries.map φ).toMonoidHom H)
      (mapShiftedCompletion d e T φ h p a) := by
  have he := (positiveCompletionShiftEquiv q β d p).apply_symm_apply a
  calc
    _ = _ := (congrArg (fun z => mapShiftedCompletion d e T φ h p
      (shiftedRayAction q β d n hn p H z)) he).symm
    _ = _ := map_action_coordinates d e T φ h n hn p H
      ((positiveCompletionShiftEquiv q β d p).symm a)
    _ = _ := congrArg (fun z => shiftedRayAction q' β' e ⟨T n, T.map_mem n.property⟩
      (mappedRay_degree_pos d e T n hn) (T p)
      (Units.map (PowerSeries.map φ).toMonoidHom H)
      (mapShiftedCompletion d e T φ h p z)) he

/-- The same coefficient transport intertwines reverse quantum wall crossings. -/
theorem mapShiftedCompletion_shiftedRayAction_symm
    (n : d.monoid) (hn : 0 < d.degree n)
    (p : Γ) (H : (PowerSeries R)ˣ) (a : d.ShiftedCoefficients (grade q β) p) :
    mapShiftedCompletion d e T φ h p ((shiftedRayAction q β d n hn p H).symm a) =
    (shiftedRayAction q' β' e ⟨T n, T.map_mem n.property⟩
      (mappedRay_degree_pos d e T n hn) (T p)
      (Units.map (PowerSeries.map φ).toMonoidHom H)).symm
      (mapShiftedCompletion d e T φ h p a) := by
  simpa only [map_inv, LinearEquiv.coe_inv] using
    mapShiftedCompletion_shiftedRayAction d e T φ h n hn p (H⁻¹) a

/-- Finite coefficient transport intertwines ray actions at their corresponding cutoff orders. -/
theorem mapShiftedQuotient_shiftedRayQuotientAction
    (n : d.monoid) (hn : 0 < d.degree n)
    (p : Γ) (k : ℕ) (H : (PowerSeries R)ˣ)
    (a : (d.shiftedFiltration (grade q β) p).quotient (T.modulus k)) :
    mapShiftedQuotient d e T φ h p k
      (shiftedRayQuotientAction q β d n hn p (T.modulus k) H a) =
    shiftedRayQuotientAction q' β' e ⟨T n, T.map_mem n.property⟩
      (mappedRay_degree_pos d e T n hn) (T p) k
      (Units.map (PowerSeries.map φ).toMonoidHom H)
      (mapShiftedQuotient d e T φ h p k a) := by
  obtain ⟨b, rfl⟩ := (d.shiftedFiltration (grade q β) p).projection_surjective (T.modulus k) a
  simp only [shiftedRayQuotientAction_projection, mapShiftedQuotient_projection,
    mapShiftedCompletion_shiftedRayAction d e T φ h]

/-- Finite coefficient transport also intertwines inverse ray actions. -/
theorem mapShiftedQuotient_shiftedRayQuotientAction_symm
    (n : d.monoid) (hn : 0 < d.degree n)
    (p : Γ) (k : ℕ) (H : (PowerSeries R)ˣ)
    (a : (d.shiftedFiltration (grade q β) p).quotient (T.modulus k)) :
    mapShiftedQuotient d e T φ h p k
      ((shiftedRayQuotientAction q β d n hn p (T.modulus k) H).symm a) =
    (shiftedRayQuotientAction q' β' e ⟨T n, T.map_mem n.property⟩
      (mappedRay_degree_pos d e T n hn) (T p) k
      (Units.map (PowerSeries.map φ).toMonoidHom H)).symm
      (mapShiftedQuotient d e T φ h p k a) := by
  simpa only [map_inv, LinearEquiv.coe_inv] using
    mapShiftedQuotient_shiftedRayQuotientAction d e T φ h n hn p k (H⁻¹) a

end Mei.QuantumMonoidAlgebra
