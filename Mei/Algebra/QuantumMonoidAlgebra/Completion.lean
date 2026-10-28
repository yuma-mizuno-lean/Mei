/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Hom
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

section Support

variable (φ : R →+* S) (f : Γ →+ Γ')
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
  (P : AddSubmonoid Γ) (P' : AddSubmonoid Γ') (hf : ∀ n ∈ P, f n ∈ P')

include hf in
/-- A quantum map carries coefficients supported on `P` to coefficients supported
on `P'` when the exponent map sends `P` into `P'`. -/
theorem map_mem_positiveSubalgebra {x : QuantumMonoidAlgebra q β}
    (hx : x ∈ positiveSubalgebra q β P) :
    map φ f h x ∈ positiveSubalgebra q' β' P' := by
  have hx' : x ∈ shiftedSubmodule (grade q β) P 0 := by
    rwa [← supportedSubalgebra_toSubmodule (grade q β) P]
  rw [shiftedSubmodule_def] at hx'
  refine Submodule.iSup_induction _
    (motive := fun x => map φ f h x ∈ positiveSubalgebra q' β' P') hx'
    (fun n x hx => ?_) (by simp) (fun x y hx hy => by
      simpa using (positiveSubalgebra q' β' P').add_mem hx hy)
  simp only [zero_add] at hx
  exact le_supportedSubalgebra (grade q' β') P' (hf n n.property)
    (map_mem_grade φ f h hx)

/-- Restrict a simultaneous quantum coefficient and exponent map to positive support. -/
def positiveMap : positiveSubalgebra q β P →+* positiveSubalgebra q' β' P' :=
  (map φ f h).restrict _ _ (fun _ hx => map_mem_positiveSubalgebra φ f h P P' hf hx)

/-- The restricted map agrees with the ambient quantum map. -/
@[simp]
theorem coe_positiveMap (x : positiveSubalgebra q β P) :
    (positiveMap φ f h P P' hf x : QuantumMonoidAlgebra q' β') = map φ f h x := (rfl)

/-- Positive quantum monomials map to the corresponding image monomials. -/
@[simp]
theorem positiveMap_positiveMonomial (p : P) :
    positiveMap φ f h P P' hf (positiveMonomial q β P p) =
      positiveMonomial q' β' P' ⟨f p, hf p p.property⟩ := by
  apply Subtype.ext
  simp

/-- The restricted map applies the coefficient homomorphism to scalars. -/
@[simp]
theorem positiveMap_algebraMap (r : R) :
    positiveMap φ f h P P' hf (algebraMap R _ r) = algebraMap S _ (φ r) := by
  apply Subtype.ext
  simp

/-- The restricted quantum map preserves the inherited homogeneous pieces. -/
theorem positiveMap_mem_grading {n : Γ} {x : positiveSubalgebra q β P}
    (hx : x ∈ (positiveSubalgebra q β P).grading (grade q β) n) :
    positiveMap φ f h P P' hf x ∈
      (positiveSubalgebra q' β' P').grading (grade q' β') (f n) := by
  rw [Subalgebra.mem_grading_iff] at hx ⊢
  simpa only [coe_positiveMap] using map_mem_grade φ f h hx

end Support

/-- Identity coefficient and exponent maps restrict to the identity on positive support. -/
@[simp]
theorem positiveMap_id (P : AddSubmonoid Γ) :
    positiveMap (q := q) (β := β) (RingHom.id R) (AddMonoidHom.id Γ)
      (fun _ _ => by simp) P P (fun _ hn => hn) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  simp only [coe_positiveMap, map_id, RingHom.id_apply]

/-- Positive quantum maps compose in both coefficients and exponents. -/
theorem positiveMap_comp (φ : R →+* S) (ψ : S →+* U) (f : Γ →+ Γ') (g : Γ' →+ Γ'')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (h' : ∀ p r, Units.map ψ.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (g p) (g r))
    (P : AddSubmonoid Γ) (P' : AddSubmonoid Γ') (P'' : AddSubmonoid Γ'')
    (hf : ∀ n ∈ P, f n ∈ P') (hg : ∀ n ∈ P', g n ∈ P'') :
    (positiveMap ψ g h' P' P'' hg).comp (positiveMap φ f h P P' hf) =
      positiveMap (ψ.comp φ) (g.comp f) (fun p r => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← h', ← h]; rfl)
        P P'' (fun n hn => hg _ (hf n hn)) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  simp

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
  have ht : ((F).ideal (T.modulus k + 1)).restrictScalars R ≤
      (((G).ideal (k + 1)).comap
        (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
          (fun _ hn => T.map_mem hn))).restrictScalars R := by
    rw [positiveFiltration_ideal_restrictScalars, Mei.DirectSum.degreeTail_def]
    simp only [iSup_le_iff]
    intro n hn x hx
    by_cases hp : n ∈ d.monoid
    · have hd : (k + 1 : ℕ) ≤ e.degree (T n) := by
        have := T.degree_gt k hp (by omega)
        omega
      have hm := Mei.DirectSum.le_degreeTail
        ((positiveSubalgebra q' β' e.monoid).grading (grade q' β')) e.degree hd
        (positiveMap_mem_grading φ T.toAddMonoidHom h d.monoid e.monoid
          (fun _ hn => T.map_mem hn) hx)
      rwa [← positiveFiltration_ideal_restrictScalars] at hm
    · have hz := supportedSubalgebra_grading_eq_bot (grade q β) d.monoid hp
      have : x = 0 := by simpa only [hz, Submodule.mem_bot] using hx
      subst x
      simp
  exact fun _ hx => ht hx

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
