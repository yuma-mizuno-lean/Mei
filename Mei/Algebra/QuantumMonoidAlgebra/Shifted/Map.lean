/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Completion
public import Mei.Algebra.QuantumMonoidAlgebra.Completion
public import Mei.LinearAlgebra.LinearEquiv.RingHom
public import Mei.Logic.Function.Cast

/-!
# Scalar and exponent transport of shifted quantum coefficients

Positive completion transport conjugated by the monomial coordinate equivalences
provides a semilinear map on every shifted completion. The map agrees with the
ambient quantum coefficient map on finite translated coefficients. Neither the
scalar map nor the positive degree map is required to be injective.

Original finite quotients inherit semilinear transport from the completed map,
with source cutoff given by the positive degree map modulus.
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
  (p : Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "G" => positiveFiltration q' β' e.monoid e.degree (fun _ h => e.degree_nonneg h)
local notation "Ψ" => mapPositiveCompletion d e T φ h
local notation "E" => positiveCompletionShiftEquiv q β d p
local notation "E'" => positiveCompletionShiftEquiv q' β' e (T p)

/-- Transport shifted quantum coefficients along compatible scalar and positive degree maps. -/
def mapShiftedCompletion :
    d.ShiftedCoefficients (grade q β) p →ₛₗ[φ]
      e.ShiftedCoefficients (grade q' β') (T p) :=
  LinearEquiv.semilinearTransport (R := R) (S := S) (A := (F).completion) (B := (G).completion)
    φ Ψ (mapPositiveCompletion_algebraMap d e T φ h) E E'

/-- The shifted transport is the existing positive completion map in monomial coordinates. -/
theorem mapShiftedCompletion_apply (a : d.ShiftedCoefficients (grade q β) p) :
    mapShiftedCompletion d e T φ h p a = E' (Ψ ((E).symm a)) := by
  exact LinearEquiv.semilinearTransport_apply (R := R) (S := S)
    (A := (F).completion) (B := (G).completion) φ Ψ
    (mapPositiveCompletion_algebraMap d e T φ h) E E' a

/-- Positive coordinates commute with shifted coefficient transport. -/
@[simp]
theorem mapShiftedCompletion_coordinates (a : (F).completion) :
    mapShiftedCompletion d e T φ h p (E a) = E' (Ψ a) := by
  exact (mapShiftedCompletion_apply d e T φ h p ((E) a)).trans
    (congrArg (fun b => (E') (Ψ b)) ((E).symm_apply_apply a))

/-- Original translated coefficients map before or after passing to completion. -/
@[simp]
theorem mapShiftedCompletion_of_coordinates (a : positiveSubalgebra q β d.monoid) :
    mapShiftedCompletion d e T φ h p
      ((d.shiftedFiltration (grade q β) p).of (positiveShiftEquiv q β d p a)) =
    (e.shiftedFiltration (grade q' β') (T p)).of
      (positiveShiftEquiv q' β' e (T p)
        (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn) a)) := by
  have hi := congrArg (mapShiftedCompletion d e T φ h p)
    (positiveCompletionShiftEquiv_toCompletion q β d p a)
  have hm := congrArg (E') (mapPositiveCompletion_toCompletion d e T φ h a)
  exact hi.symm.trans ((mapShiftedCompletion_coordinates d e T φ h p
    ((F).toCompletion a)).trans (hm.trans
      (positiveCompletionShiftEquiv_toCompletion q' β' e (T p) _)))

/-- The finite coordinate formula transports the actual ambient quantum coefficient. -/
theorem map_positiveShiftEquiv (a : positiveSubalgebra q β d.monoid) :
    map φ T.toAddMonoidHom h (positiveShiftEquiv q β d p a) =
      (positiveShiftEquiv q' β' e (T p)
        (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn) a) :
          QuantumMonoidAlgebra q' β') := by
  simp only [coe_positiveShiftEquiv, _root_.map_mul, map_monomial, coe_positiveMap]

local notation "S₀" => d.shiftedFiltration (grade q β) p
local notation "S₁" => e.shiftedFiltration (grade q' β') (T p)

/-- Shifted transport obeys the degree map's cutoff modulus on relative filtrations. -/
theorem mapShiftedCompletion_mem_completedFiltration (k : ℕ)
    {a : (S₀).completion}
    (ha : a ∈ (S₀).completedFiltration.submodule (T.modulus k + 1)) :
    mapShiftedCompletion d e T φ h p a ∈
      (S₁).completedFiltration.submodule (k + 1) := by
  obtain ⟨x, rfl⟩ := (E).surjective a
  have hx := (positiveCompletionShiftEquiv_mem_iff q β d p (T.modulus k + 1) x).mp ha
  have hy : Ψ x ∈ (G).completionIdeal (k + 1) := by
    simp only [AlgFiltration.completionIdeal_succ, RingHom.mem_ker] at hx ⊢
    rw [projection_mapPositiveCompletion, hx, map_zero]
  have he := (positiveCompletionShiftEquiv_mem_iff q' β' e (T p) (k + 1) (Ψ x)).mpr hy
  simpa only [mapShiftedCompletion_coordinates] using he

/-- Transport original finite shifted quotients using the prescribed source cutoff. -/
def mapShiftedQuotient (k : ℕ) :
    (S₀).quotient (T.modulus k) →ₛₗ[φ] (S₁).quotient k :=
  ((S₁).completedQuotientEquiv k).toLinearMap.comp
    (((S₀).completedFiltration.submodule (T.modulus k + 1)).mapQ
      ((S₁).completedFiltration.submodule (k + 1))
      (mapShiftedCompletion d e T φ h p)
      (fun _ ha => mapShiftedCompletion_mem_completedFiltration d e T φ h p k ha) |>.comp
        ((S₀).completedQuotientEquiv (T.modulus k)).symm.toLinearMap)

/-- Projection computes shifted transport using its finite quotient map. -/
@[simp]
theorem mapShiftedQuotient_projection (k : ℕ) (a : (S₀).completion) :
    mapShiftedQuotient d e T φ h p k ((S₀).projection (T.modulus k) a) =
      (S₁).projection k (mapShiftedCompletion d e T φ h p a) := by
  let m := ((S₀).completedFiltration.submodule (T.modulus k + 1)).mapQ
    ((S₁).completedFiltration.submodule (k + 1))
    (mapShiftedCompletion d e T φ h p)
    (fun _ ha => mapShiftedCompletion_mem_completedFiltration d e T φ h p k ha)
  have he : ((S₀).completedQuotientEquiv (T.modulus k)).symm
      ((S₀).projection (T.modulus k) a) = Submodule.Quotient.mk a :=
    (congrArg ((S₀).completedQuotientEquiv (T.modulus k)).symm
      ((S₀).completedQuotientEquiv_mk (T.modulus k) a)).symm.trans
        (((S₀).completedQuotientEquiv (T.modulus k)).symm_apply_apply _)
  have hm : m (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (mapShiftedCompletion d e T φ h p a) :=
    Submodule.mapQ_apply _ _ _ a
  exact (congrArg (fun b => (S₁).completedQuotientEquiv k (m b)) he).trans
    ((congrArg ((S₁).completedQuotientEquiv k) hm).trans
      ((S₁).completedQuotientEquiv_mk k (mapShiftedCompletion d e T φ h p a)))

/-- Original translated representatives transport by the ambient coefficient map. -/
@[simp]
theorem mapShiftedQuotient_mk_coordinates (k : ℕ) (a : positiveSubalgebra q β d.monoid) :
    mapShiftedQuotient d e T φ h p k
      (Submodule.Quotient.mk (positiveShiftEquiv q β d p a)) =
    Submodule.Quotient.mk (positiveShiftEquiv q' β' e (T p)
      (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn) a)) := by
  have he := mapShiftedQuotient_projection d e T φ h p k
    ((S₀).of (positiveShiftEquiv q β d p a))
  simpa only [ModuleFiltration.projection_of, mapShiftedCompletion_of_coordinates] using he

/-- Shifted finite transport commutes with all transitions at the corresponding source cutoffs. -/
@[simp]
theorem transition_mapShiftedQuotient {k l : ℕ} (hkl : k ≤ l)
    (a : (S₀).quotient (T.modulus l)) :
    (S₁).transition hkl (mapShiftedQuotient d e T φ h p l a) =
      mapShiftedQuotient d e T φ h p k
        ((S₀).transition (T.monotone_modulus hkl) a) := by
  obtain ⟨b, rfl⟩ := (S₀).projection_surjective (T.modulus l) a
  simp only [mapShiftedQuotient_projection, ModuleFiltration.transition_projection]

/-- Identity scalar and exponent transport fixes every shifted completed coefficient. -/
@[simp]
theorem mapShiftedCompletion_id (x : d.ShiftedCoefficients (grade q β) p) :
    cast (congrArg (d.ShiftedCoefficients (grade q β)) (PositiveDegreeMap.id_apply (d := d) p))
      (mapShiftedCompletion (q' := q) (β' := β) d d (PositiveDegreeMap.id d) (RingHom.id R)
        (fun u v => by simp) p x) = x := by
  obtain ⟨b, rfl⟩ := (positiveCompletionShiftEquiv q β d p).surjective x
  let C := cast (congrArg (d.ShiftedCoefficients (grade q β))
    (PositiveDegreeMap.id_apply (d := d) p))
  have hm := mapShiftedCompletion_coordinates (q' := q) (β' := β) d d
    (PositiveDegreeMap.id d) (RingHom.id R) (fun u v => by simp) p b
  have hc (z : (F).completion) :
      C (positiveCompletionShiftEquiv q β d ((PositiveDegreeMap.id d) p) z) =
        positiveCompletionShiftEquiv q β d p z := by
    simpa only [cast_eq] using Function.cast_apply
      (fun r => (positiveCompletionShiftEquiv q β d r : (F).completion → _))
      (PositiveDegreeMap.id_apply (d := d) p) z
  have hi := RingHom.congr_fun (mapPositiveCompletion_id (q := q) (β := β) d) b
  exact ((congrArg C hm).trans (hc _)).trans
    (congrArg (positiveCompletionShiftEquiv q β d p) hi)

/-- Identity transport fixes every finite shifted quotient. -/
@[simp]
theorem mapShiftedQuotient_id (k : ℕ)
    (x : (d.shiftedFiltration (grade q β) p).quotient k) :
    cast (congrArg (fun r => (d.shiftedFiltration (grade q β) r).quotient k)
        (PositiveDegreeMap.id_apply (d := d) p))
      (mapShiftedQuotient (q' := q) (β' := β) d d (PositiveDegreeMap.id d) (RingHom.id R)
        (fun u v => by simp) p k
        (cast (congrArg (fun j => (d.shiftedFiltration (grade q β) p).quotient j)
          (PositiveDegreeMap.id_modulus (d := d) k).symm) x)) = x := by
  obtain ⟨a, rfl⟩ := (d.shiftedFiltration (grade q β) p).projection_surjective k x
  have hc : cast (congrArg (fun j => (d.shiftedFiltration (grade q β) p).quotient j)
      (PositiveDegreeMap.id_modulus (d := d) k).symm)
      ((d.shiftedFiltration (grade q β) p).projection k a) =
      (d.shiftedFiltration (grade q β) p).projection ((PositiveDegreeMap.id d).modulus k) a := by
    simpa only [cast_eq] using Function.cast_apply
      (fun j => ((d.shiftedFiltration (grade q β) p).projection j : (S₀).completion → _))
      (PositiveDegreeMap.id_modulus (d := d) k).symm a
  rw [hc, mapShiftedQuotient_projection]
  exact (Function.cast_apply
    (fun r => ((d.shiftedFiltration (grade q β) r).projection k :
      d.ShiftedCoefficients (grade q β) r → _)) (PositiveDegreeMap.id_apply (d := d) p) _).trans
        (congrArg ((d.shiftedFiltration (grade q β) p).projection k)
          (mapShiftedCompletion_id d p a))

variable {U Γ'' : Type*} [CommRing U] [AddCommGroup Γ'']
  {q'' : Uˣ} {β'' : LinearMap.BilinForm ℤ Γ''}
  (a : PositiveDegrees Γ'') (T' : PositiveDegreeMap e a) (ψ : S →+* U)
  (h' : ∀ u v, Units.map ψ.toMonoidHom (q' ^ β' u v) = q'' ^ β'' (T' u) (T' v))

/-- Completed transport composes across coefficient rings and exponent groups. -/
theorem mapShiftedCompletion_comp (x : d.ShiftedCoefficients (grade q β) p) :
    cast (congrArg (a.ShiftedCoefficients (grade q'' β''))
        (PositiveDegreeMap.comp_apply T' T p))
      (mapShiftedCompletion (q' := q'') (β' := β'') d a (T'.comp T) (ψ.comp φ)
        (mapPositiveCompletion_comp_compat d e T φ h a T' ψ h') p x) =
      mapShiftedCompletion e a T' ψ h' (T p) (mapShiftedCompletion d e T φ h p x) := by
  obtain ⟨b, rfl⟩ := (positiveCompletionShiftEquiv q β d p).surjective x
  let C := cast (congrArg (a.ShiftedCoefficients (grade q'' β''))
    (PositiveDegreeMap.comp_apply T' T p))
  let hc : ∀ u v, Units.map (ψ.comp φ).toMonoidHom (q ^ β u v) =
      q'' ^ β'' ((T'.comp T) u) ((T'.comp T) v) :=
    mapPositiveCompletion_comp_compat d e T φ h a T' ψ h'
  let Z := positiveCompletionShiftEquiv q'' β'' a (T' (T p))
  have h₁ := mapShiftedCompletion_coordinates d a (T'.comp T) (ψ.comp φ) hc p b
  have h₂ : C (positiveCompletionShiftEquiv q'' β'' a ((T'.comp T) p)
      (mapPositiveCompletion d a (T'.comp T) (ψ.comp φ) hc b)) =
      Z (mapPositiveCompletion d a (T'.comp T) (ψ.comp φ) hc b) := by
    simpa only [cast_eq] using Function.cast_apply
      (fun r => (positiveCompletionShiftEquiv q'' β'' a r :
        (positiveFiltration q'' β'' a.monoid a.degree
          (fun _ hu => a.degree_nonneg hu)).completion → _))
      (PositiveDegreeMap.comp_apply T' T p)
      (mapPositiveCompletion d a (T'.comp T) (ψ.comp φ) hc b)
  have h₃ := RingHom.congr_fun (mapPositiveCompletion_comp d e T φ h a T' ψ h') b
  have h₄ := mapShiftedCompletion_coordinates e a T' ψ h' (T p)
    (mapPositiveCompletion d e T φ h b)
  have h₅ := mapShiftedCompletion_coordinates d e T φ h p b
  exact (congrArg C h₁).trans (h₂.trans ((congrArg Z h₃).trans
    (h₄.symm.trans (congrArg (mapShiftedCompletion e a T' ψ h' (T p)) h₅.symm))))

/-- Finite transport composes with source cutoff `T.modulus (T'.modulus k)`. -/
theorem mapShiftedQuotient_comp (k : ℕ)
    (x : (d.shiftedFiltration (grade q β) p).quotient (T.modulus (T'.modulus k))) :
    cast (congrArg (fun r => (a.shiftedFiltration (grade q'' β'') r).quotient k)
        (PositiveDegreeMap.comp_apply T' T p))
      (mapShiftedQuotient (q' := q'') (β' := β'') d a (T'.comp T) (ψ.comp φ)
        (mapPositiveCompletion_comp_compat d e T φ h a T' ψ h') p k
        (cast (congrArg (fun j => (d.shiftedFiltration (grade q β) p).quotient j)
          (PositiveDegreeMap.comp_modulus T' T k).symm) x)) =
      mapShiftedQuotient e a T' ψ h' (T p) k
        (mapShiftedQuotient d e T φ h p (T'.modulus k) x) := by
  obtain ⟨b, rfl⟩ := (d.shiftedFiltration (grade q β) p).projection_surjective
    (T.modulus (T'.modulus k)) x
  let C := cast (congrArg (fun r => (a.shiftedFiltration (grade q'' β'') r).quotient k)
    (PositiveDegreeMap.comp_apply T' T p))
  let hc : ∀ u v, Units.map (ψ.comp φ).toMonoidHom (q ^ β u v) =
      q'' ^ β'' ((T'.comp T) u) ((T'.comp T) v) :=
    mapPositiveCompletion_comp_compat d e T φ h a T' ψ h'
  let m := mapShiftedQuotient d a (T'.comp T) (ψ.comp φ) hc p k
  have hs : cast (congrArg (fun j => (d.shiftedFiltration (grade q β) p).quotient j)
      (PositiveDegreeMap.comp_modulus T' T k).symm)
      ((d.shiftedFiltration (grade q β) p).projection (T.modulus (T'.modulus k)) b) =
      (d.shiftedFiltration (grade q β) p).projection ((T'.comp T).modulus k) b := by
    simpa only [cast_eq] using Function.cast_apply
      (fun j => ((d.shiftedFiltration (grade q β) p).projection j : (S₀).completion → _))
      (PositiveDegreeMap.comp_modulus T' T k).symm b
  have h₁ := congrArg (fun z => C (m z)) hs
  have h₂ := congrArg C (mapShiftedQuotient_projection d a (T'.comp T) (ψ.comp φ) hc p k b)
  have h₃ := Function.cast_apply
    (fun r => ((a.shiftedFiltration (grade q'' β'') r).projection k :
      a.ShiftedCoefficients (grade q'' β'') r → _))
    (PositiveDegreeMap.comp_apply T' T p)
    (mapShiftedCompletion d a (T'.comp T) (ψ.comp φ) hc p b)
  have h₄ := congrArg ((a.shiftedFiltration (grade q'' β'') (T' (T p))).projection k)
    (mapShiftedCompletion_comp d e T φ h p a T' ψ h' b)
  have h₅ := mapShiftedQuotient_projection e a T' ψ h' (T p) k
    (mapShiftedCompletion d e T φ h p b)
  have h₆ := congrArg (mapShiftedQuotient e a T' ψ h' (T p) k)
    (mapShiftedQuotient_projection d e T φ h p (T'.modulus k) b)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.symm.trans h₆.symm))))

end Mei.QuantumMonoidAlgebra
