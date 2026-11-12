/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Inclusion
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Transport

/-!
# Scalar and exponent transport of global quantum coefficients

Compatible scalar and positive degree maps induce semilinear maps on global
quantum coefficients. These maps agree with shifted completion transport in every
containing target chart, and respect identity and composition. No injectivity or
alternation hypothesis is needed.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ'] [DecidableEq Γ] [DecidableEq Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

private def targetChart (s : Multiset d.monoid) : Multiset e.monoid :=
  d.coefficientImageChart e T.toAddMonoidHom T.map_mem s

omit [DecidableEq Γ] [DecidableEq Γ'] in
private theorem targetChart_mem (s : Multiset d.monoid) :
    T (d.coefficientOrigin s) - e.coefficientOrigin (targetChart d e T s) ∈ e.monoid :=
  d.coefficientImageChart_mem e T.toAddMonoidHom T.map_mem s

/-- Transport global coefficients along compatible scalar and positive degree maps. -/
def mapShiftedDirectLimit :
    d.ShiftedDirectLimit (grade q β) →ₛₗ[φ] e.ShiftedDirectLimit (grade q' β') :=
  d.shiftedDirectLimitLift e T.toAddMonoidHom T.map_mem (grade q β) (grade q' β') φ
    (mapShiftedCompletion d e T φ h)
    (fun p r hpr x => mapShiftedCompletion_shiftedCompletedInclusion q β d e T φ h p r hpr x)

/-- Transport in a chart can use any target chart containing the mapped origin. -/
theorem mapShiftedDirectLimit_toShiftedDirectLimit (s : Multiset d.monoid)
    (t : Multiset e.monoid) (ht : T (d.coefficientOrigin s) - e.coefficientOrigin t ∈ e.monoid)
    (x : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s)) :
    mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimit (grade q β) s x) =
      e.toShiftedDirectLimitOfChart (grade q' β') (T (d.coefficientOrigin s)) t ht
        (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) x) :=
  d.shiftedDirectLimitLift_toShiftedDirectLimit e T.toAddMonoidHom T.map_mem
    (grade q β) (grade q' β') φ (mapShiftedCompletion d e T φ h)
    (fun p r hpr x => mapShiftedCompletion_shiftedCompletedInclusion q β d e T φ h p r hpr x)
    s t ht x

/-- Arbitrary-origin chart embeddings commute with global scalar and exponent transport. -/
theorem mapShiftedDirectLimit_toShiftedDirectLimitOfChart (p : Γ)
    (s : Multiset d.monoid) (hs : p - d.coefficientOrigin s ∈ d.monoid)
    (t : Multiset e.monoid) (ht : T p - e.coefficientOrigin t ∈ e.monoid)
    (x : d.ShiftedCoefficients (grade q β) p) :
    mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimitOfChart (grade q β) p s hs x) =
      e.toShiftedDirectLimitOfChart (grade q' β') (T p) t ht
        (mapShiftedCompletion d e T φ h p x) :=
  d.shiftedDirectLimitLift_toShiftedDirectLimitOfChart e T.toAddMonoidHom T.map_mem
    (grade q β) (grade q' β') φ (mapShiftedCompletion d e T φ h)
    (fun u r hur x => mapShiftedCompletion_shiftedCompletedInclusion q β d e T φ h u r hur x)
    p s hs t ht x

private theorem toShiftedDirectLimitOfChart_cast {p r : Γ} (hpr : p = r)
    (s : Multiset d.monoid) (hr : r - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients (grade q β) p) :
    d.toShiftedDirectLimitOfChart (grade q β) r s hr
        (cast (congrArg (d.ShiftedCoefficients (grade q β)) hpr) x) =
      d.toShiftedDirectLimitOfChart (grade q β) p s (by rwa [hpr]) x := by
  have hij : (⟨p, by rwa [hpr]⟩ : {u : Γ // u - d.coefficientOrigin s ∈ d.monoid}) =
      ⟨r, hr⟩ := Subtype.ext hpr
  simpa only [cast_eq] using
    (Function.cast_apply
      (A := fun u : {u : Γ // u - d.coefficientOrigin s ∈ d.monoid} =>
        d.ShiftedCoefficients (grade q β) u.val)
      (B := fun _ => d.ShiftedDirectLimit (grade q β))
      (fun u => (d.toShiftedDirectLimitOfChart (grade q β) u.val s u.property :
        d.ShiftedCoefficients (grade q β) u.val → d.ShiftedDirectLimit (grade q β))) hij x).symm

/-- Identity scalar and degree transport fixes every global coefficient. -/
@[simp]
theorem mapShiftedDirectLimit_id (x : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit (q' := q) (β' := β) d d (PositiveDegreeMap.id d)
      (RingHom.id R) (fun u v => by simp) x = x := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit (grade q β) x
  have hm := mapShiftedDirectLimit_toShiftedDirectLimit (q' := q) (β' := β)
    d d (PositiveDegreeMap.id d) (RingHom.id R) (fun u v => by simp) s s (by simp) a
  have hi := mapShiftedCompletion_id (q := q) (β := β) d (d.coefficientOrigin s) a
  have hc := toShiftedDirectLimitOfChart_cast d
    (PositiveDegreeMap.id_apply (d := d) (d.coefficientOrigin s)) s (by simp)
    (mapShiftedCompletion (q' := q) (β' := β) d d (PositiveDegreeMap.id d) (RingHom.id R)
      (fun u v => by simp) (d.coefficientOrigin s) a)
  exact hm.trans (hc.symm.trans ((congrArg
    (d.toShiftedDirectLimitOfChart (grade q β) (d.coefficientOrigin s) s (by simp)) hi).trans
      ((d.toShiftedDirectLimitOfChart_apply (grade q β) (d.coefficientOrigin s) s
        (by simp) a).trans
          (congrArg (d.toShiftedDirectLimit (grade q β) s)
            (d.shiftedCompletedInclusion_refl (grade q β) (d.coefficientOrigin s) a)))))

variable {U Γ'' : Type*} [CommRing U] [AddCommGroup Γ''] [DecidableEq Γ'']
  {q'' : Uˣ} {β'' : LinearMap.BilinForm ℤ Γ''}
  (a : PositiveDegrees Γ'') (T' : PositiveDegreeMap e a) (ψ : S →+* U)
  (h' : ∀ u v, Units.map ψ.toMonoidHom (q' ^ β' u v) = q'' ^ β'' (T' u) (T' v))

/-- Scalar and exponent transport compose on all global coefficients. -/
theorem mapShiftedDirectLimit_comp (x : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit (q' := q'') (β' := β'') d a (T'.comp T) (ψ.comp φ)
      (mapPositiveCompletion_comp_compat d e T φ h a T' ψ h') x =
      mapShiftedDirectLimit e a T' ψ h' (mapShiftedDirectLimit d e T φ h x) := by
  refine (d.exists_toShiftedDirectLimit (grade q β) x).elim fun s hs => ?_
  refine hs.elim fun z hz => ?_
  let r := targetChart d a (T'.comp T) s
  have hrc := targetChart_mem d a (T'.comp T) s
  have hr : T' (T (d.coefficientOrigin s)) - a.coefficientOrigin r ∈ a.monoid := by
    simpa only [PositiveDegreeMap.comp_apply] using hrc
  let hc : ∀ u v, Units.map (ψ.comp φ).toMonoidHom (q ^ β u v) =
      q'' ^ β'' ((T'.comp T) u) ((T'.comp T) v) :=
    mapPositiveCompletion_comp_compat d e T φ h a T' ψ h'
  have h₁ := mapShiftedDirectLimit_toShiftedDirectLimit d a (T'.comp T) (ψ.comp φ) hc
    s r hrc z
  have h₂ := mapShiftedCompletion_comp d e T φ h (d.coefficientOrigin s) a T' ψ h' z
  have h₃ := congrArg (mapShiftedDirectLimit e a T' ψ h')
    (mapShiftedDirectLimit_toShiftedDirectLimit d e T φ h s (targetChart d e T s)
      (targetChart_mem d e T s) z)
  have h₄ := mapShiftedDirectLimit_toShiftedDirectLimitOfChart e a T' ψ h'
    (T (d.coefficientOrigin s)) (targetChart d e T s) (targetChart_mem d e T s) r hr
    (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) z)
  have hcast := toShiftedDirectLimitOfChart_cast a
    (PositiveDegreeMap.comp_apply T' T (d.coefficientOrigin s)) r hr
    (mapShiftedCompletion d a (T'.comp T) (ψ.comp φ) hc (d.coefficientOrigin s) z)
  -- The composed map and the successive maps agree in one containing target chart.
  calc
    _ = _ := (congrArg (mapShiftedDirectLimit d a (T'.comp T) (ψ.comp φ) hc) hz).symm
    _ = _ := h₁
    _ = a.toShiftedDirectLimitOfChart (grade q'' β'') (T' (T (d.coefficientOrigin s))) r hr
        (cast (congrArg (a.ShiftedCoefficients (grade q'' β''))
          (PositiveDegreeMap.comp_apply T' T (d.coefficientOrigin s)))
          (mapShiftedCompletion d a (T'.comp T) (ψ.comp φ) hc (d.coefficientOrigin s) z)) :=
      hcast.symm
    _ = a.toShiftedDirectLimitOfChart (grade q'' β'') (T' (T (d.coefficientOrigin s))) r hr
        (mapShiftedCompletion e a T' ψ h' (T (d.coefficientOrigin s))
          (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) z)) :=
      congrArg (a.toShiftedDirectLimitOfChart (grade q'' β'')
        (T' (T (d.coefficientOrigin s))) r hr) h₂
    _ = _ := h₄.symm
    _ = _ := h₃.symm
    _ = _ := congrArg (fun y =>
      mapShiftedDirectLimit e a T' ψ h' (mapShiftedDirectLimit d e T φ h y)) hz

end Mei.QuantumMonoidAlgebra
