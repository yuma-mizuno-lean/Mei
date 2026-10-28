/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Positive
public import Mei.Algebra.PositiveDegrees.Map
public import Mei.RingTheory.FilteredAlgebra.Map
public import Mei.RingTheory.FilteredAlgebra.Algebra

/-!
# Maps of completed positive quantum algebras

Simultaneous coefficient and exponent maps restrict to positive quantum algebras.
A positive degree map controls the required source cutoff, so these restrictions
extend to their degree completions. The extension is independent of the chosen
cutoff modulus and respects identity and composition. In particular, coefficient
specialization and changes of exponent lattice can be applied to quantum series,
including maps that merge exponents or kill coefficients.

The cutoff estimate is proved on homogeneous pieces of the existing positive
algebra. We use `QuantumMonoidAlgebra.map`, Mathlib's `RingHom.restrict`, and
`AlgFiltration.mapCompletion`; no new completion carrier is introduced.
The quantum coefficient convention follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Example 2.1(iii).
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S U Γ Γ' Γ'' : Type*}
  [CommRing R] [CommRing S] [CommRing U]
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  {q : Rˣ} {q' : Sˣ} {q'' : Uˣ}
  {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  {β'' : LinearMap.BilinForm ℤ Γ''}

variable (d : PositiveDegrees Γ) (e : PositiveDegrees Γ')
  (T : PositiveDegreeMap d e) (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ hn => d.degree_nonneg hn)
local notation "G" => positiveFiltration q' β' e.monoid e.degree (fun _ hn => e.degree_nonneg hn)

/-- The positive degree modulus bounds the source filtration needed at every target order.
Neither the coefficient homomorphism nor the exponent map need be injective. -/
theorem positiveMap_ideal_le (k : ℕ) :
    (F).ideal (T.modulus k + 1) ≤ ((G).ideal (k + 1)).comap
      (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn)) := by
  classical
  rw [positiveFiltration_ideal, GradedAlgebra.degreeIdeal_le_iff]
  intro n hn x hx
  by_cases hp : n ∈ d.monoid
  · have hd : (k + 1 : ℕ) ≤ e.degree (T n) := by
      have := T.degree_gt k hp (by omega)
      omega
    rw [Ideal.mem_comap, positiveFiltration_ideal]
    exact GradedAlgebra.le_degreeIdeal _ e.degree _ hd _
      (positiveMap_mem_grading φ T.toAddMonoidHom h d.monoid e.monoid
        (fun _ hn => T.map_mem hn) hx)
  · have hz := supportedSubalgebra_grading_eq_bot (grade q β) d.monoid hp
    have : x = 0 := by simpa only [hz, Submodule.mem_bot] using hx
    subst x
    simp

/-- Extend a quantum map to the degree completions of its positive coefficient algebras. -/
def mapPositiveCompletion : (F).completion →+* (G).completion :=
  (F).mapCompletion G
    (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn))
    T.modulus T.monotone_modulus (positiveMap_ideal_le d e T φ h)

/-- The order-`k` component is the induced quotient map at the prescribed source cutoff. -/
@[simp]
theorem projection_mapPositiveCompletion (k : ℕ) (x : (F).completion) :
    (G).projection k (mapPositiveCompletion d e T φ h x) =
      Ideal.quotientMap ((G).ideal (k + 1))
        (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn))
        (positiveMap_ideal_le d e T φ h k) ((F).projection (T.modulus k) x) :=
  (F).projection_mapCompletion _ _ _ _ _ k x

/-- Completed quantum maps agree with the original map on finite positive coefficients. -/
@[simp]
theorem mapPositiveCompletion_toCompletion (x : positiveSubalgebra q β d.monoid) :
    mapPositiveCompletion d e T φ h ((F).toCompletion x) =
      (G).toCompletion (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
        (fun _ hn => T.map_mem hn) x) :=
  (F).mapCompletion_toCompletion _ _ _ _ _ x

/-- The completed map applies the specified coefficient homomorphism to scalars. -/
@[simp]
theorem mapPositiveCompletion_algebraMap (r : R) :
    mapPositiveCompletion d e T φ h (algebraMap R (F).completion r) =
      algebraMap S (G).completion (φ r) := by
  have hF := ((F).toCompletionₐ (R := R)).commutes r
  have hG := ((G).toCompletionₐ (R := S)).commutes (φ r)
  simp only [AlgFiltration.toCompletionₐ_apply] at hF hG
  exact (congrArg (mapPositiveCompletion d e T φ h) hF.symm).trans
    ((mapPositiveCompletion_toCompletion d e T φ h (algebraMap R _ r)).trans
      ((congrArg (G).toCompletion
        (positiveMap_algebraMap φ T.toAddMonoidHom h d.monoid e.monoid
          (fun _ hn => T.map_mem hn) r)).trans hG))

/-- With fixed coefficients, a compatible exponent map extends as an algebra homomorphism. -/
def mapDomainPositiveCompletion
    (hβ : ∀ p r, q ^ β p r = q ^ β' (T p) (T r)) :
    (F).completion →ₐ[R]
      (positiveFiltration q β' e.monoid e.degree (fun _ hn => e.degree_nonneg hn)).completion where
  __ := mapPositiveCompletion d e T (RingHom.id R) (fun p r => by simpa using hβ p r)
  commutes' r := mapPositiveCompletion_algebraMap d e T (RingHom.id R) _ r

/-- The algebra map has the same underlying ring map as simultaneous quantum transport. -/
@[simp]
theorem coe_mapDomainPositiveCompletion
    (hβ : ∀ p r, q ^ β p r = q ^ β' (T p) (T r)) :
    (mapDomainPositiveCompletion d e T hβ : (F).completion →+*
      (positiveFiltration q β' e.monoid e.degree (fun _ hn => e.degree_nonneg hn)).completion) =
      mapPositiveCompletion d e T (RingHom.id R) (fun p r => by simpa using hβ p r) := (rfl)

/-- Enlarging the source cutoff modulus does not change the completed quantum map. -/
theorem mapPositiveCompletion_enlarge (μ : ℕ → ℕ) (hμ : Monotone μ)
    (hle : ∀ k, T.modulus k ≤ μ k) :
    mapPositiveCompletion d e (T.enlarge μ hμ hle) φ (fun p r => by
      simpa only [PositiveDegreeMap.enlarge_apply] using h p r) =
      mapPositiveCompletion d e T φ h := by
  have hf : (T.enlarge μ hμ hle).toAddMonoidHom = T.toAddMonoidHom := by
    ext n
    exact PositiveDegreeMap.enlarge_apply T μ hμ hle n
  unfold mapPositiveCompletion
  simp only [hf, PositiveDegreeMap.enlarge_modulus]
  exact ((F).mapCompletion_eq (G) _ T.monotone_modulus
    (positiveMap_ideal_le d e T φ h) μ hμ _).symm

/-- Identity quantum maps induce the identity on the positive degree completion. -/
@[simp]
theorem mapPositiveCompletion_id :
    mapPositiveCompletion (q := q) (β := β) d d (PositiveDegreeMap.id d)
      (RingHom.id R) (fun p r => by simp) = RingHom.id (F).completion := by
  have hf : (PositiveDegreeMap.id d).toAddMonoidHom = AddMonoidHom.id Γ := by
    ext n
    exact PositiveDegreeMap.id_apply n
  have hm : (PositiveDegreeMap.id d).modulus = id :=
    funext PositiveDegreeMap.id_modulus
  simpa only [mapPositiveCompletion, hf, hm, positiveMap_id] using (F).mapCompletion_id

variable (a : PositiveDegrees Γ'') (T' : PositiveDegreeMap e a) (ψ : S →+* U)
  (h' : ∀ p r, Units.map ψ.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (T' p) (T' r))

/-- Completed coefficient and exponent maps compose with the composed cutoff modulus. -/
theorem mapPositiveCompletion_comp :
    mapPositiveCompletion d a (T'.comp T) (ψ.comp φ) (fun p r => by
      rw [PositiveDegreeMap.comp_apply, PositiveDegreeMap.comp_apply, ← h', ← h]; rfl) =
      (mapPositiveCompletion e a T' ψ h').comp (mapPositiveCompletion d e T φ h) := by
  unfold mapPositiveCompletion
  rw [← (F).mapCompletion_comp]
  congr 1
  · have hf : (T'.comp T).toAddMonoidHom = T'.toAddMonoidHom.comp T.toAddMonoidHom := by
      ext n
      exact PositiveDegreeMap.comp_apply T' T n
    simpa only [hf] using (positiveMap_comp φ ψ T.toAddMonoidHom T'.toAddMonoidHom h h'
      d.monoid e.monoid a.monoid (fun _ hn => T.map_mem hn)
      (fun _ hn => T'.map_mem hn)).symm
  · exact funext (PositiveDegreeMap.comp_modulus T' T)

end Mei.QuantumMonoidAlgebra
