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
An explicit degree bound on the whole coefficient monoid controls the source
cutoff, so these restrictions extend to nonnegative degree completions. Positive
degree maps give the standard specialization. The extension is independent of the chosen
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

section Instances

variable {P : AddSubmonoid Γ} {δ : Γ →+ ℤ} {hδ : ∀ n ∈ P, 0 ≤ δ n}

local notation "F" => positiveFiltration q β P δ hδ

-- Direct instances for the inherited structures: searching through the positive subalgebra,
-- quotient, product, and subring layers each time exceeds the instance search budget.
instance : Ring (F).completion := inferInstance

instance : Semigroup (F).completion := (inferInstance : Ring (F).completion).toSemigroup

instance : AddCommMonoid (F).completion := inferInstance

end Instances

section General

variable (φ : R →+* S) (f : Γ →+ Γ')
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
  (P : AddSubmonoid Γ) (P' : AddSubmonoid Γ') (hP : ∀ n ∈ P, f n ∈ P')
  (δ : Γ →+ ℤ) (δ' : Γ' →+ ℤ)
  (hδ : ∀ n ∈ P, 0 ≤ δ n) (hδ' : ∀ n ∈ P', 0 ≤ δ' n)

local notation "F" => positiveFiltration q β P δ hδ
local notation "G" => positiveFiltration q' β' P' δ' hδ'
local notation "ψ" => positiveMap φ f h P P' hP

variable (l : ℕ → ℕ) (hl : Monotone l)
  (hcut : ∀ k n, n ∈ P → (l k : ℤ) < δ n → (k : ℤ) < δ' (f n))

/-- Extend simultaneous scalar and exponent maps to general nonnegative coefficient
completions using their specified cutoff modulus. -/
def mapPositiveCompletionOfDegree : (F).completion →+* (G).completion :=
  (F).mapCompletion G ψ l hl (fun k =>
    positiveMap_ideal_le_of_degree φ f h P P' hP δ δ' hδ hδ' (l k + 1) (k + 1)
      (fun n hn hd => by have := hcut k n hn (by omega); omega))

/-- The order-`k` component uses the prescribed source cutoff. -/
@[simp]
theorem projection_mapPositiveCompletionOfDegree (k : ℕ) (x : (F).completion) :
    (G).projection k
        (mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut x) =
      Ideal.quotientMap ((G).ideal (k + 1)) ψ
        (positiveMap_ideal_le_of_degree φ f h P P' hP δ δ' hδ hδ' (l k + 1) (k + 1)
          (fun n hn hd => by have := hcut k n hn (by omega); omega))
        ((F).projection (l k) x) :=
  (F).projection_mapCompletion _ _ _ _ _ k x

/-- Completed transport agrees with the original map on finite coefficients. -/
@[simp]
theorem mapPositiveCompletionOfDegree_toCompletion (x : positiveSubalgebra q β P) :
    mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut
        ((F).toCompletion x) = (G).toCompletion (ψ x) :=
  (F).mapCompletion_toCompletion _ _ _ _ _ x

/-- Completed transport applies the specified coefficient homomorphism to scalars. -/
@[simp]
theorem mapPositiveCompletionOfDegree_algebraMap (r : R) :
    mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut
        (algebraMap R (F).completion r) = algebraMap S (G).completion (φ r) := by
  have hF := ((F).toCompletionₐ (R := R)).commutes r
  have hG := ((G).toCompletionₐ (R := S)).commutes (φ r)
  simp only [AlgFiltration.toCompletionₐ_apply] at hF hG
  exact (congrArg (mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut)
    hF.symm).trans
    ((mapPositiveCompletionOfDegree_toCompletion φ f h P P' hP δ δ' hδ hδ' l hl hcut
      (algebraMap R _ r)).trans
      ((congrArg (G).toCompletion (positiveMap_algebraMap φ f h P P' hP r)).trans hG))

/-- Completed coefficient transport is semilinear over its coefficient homomorphism. -/
@[simp high]
theorem mapPositiveCompletionOfDegree_smul (r : R) (x : (F).completion) :
    mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut (r • x) =
      φ r • mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut x := by
  let Φ := mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut
  calc
    Φ (r • x) = Φ (algebraMap R (F).completion r * x) := congrArg Φ (Algebra.smul_def r x)
    _ = Φ (algebraMap R (F).completion r) * Φ x := Φ.map_mul _ _
    _ = algebraMap S (G).completion (φ r) * Φ x :=
      congrArg (fun z => z * Φ x)
        (mapPositiveCompletionOfDegree_algebraMap φ f h P P' hP δ δ' hδ hδ' l hl hcut r)
    _ = φ r • Φ x := (Algebra.smul_def (φ r) (Φ x)).symm

/-- Any two valid cutoff moduli give the same completed quantum map. -/
theorem mapPositiveCompletionOfDegree_eq (m : ℕ → ℕ) (hm : Monotone m)
    (hcut' : ∀ k n, n ∈ P → (m k : ℤ) < δ n → (k : ℤ) < δ' (f n)) :
    mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut =
      mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' m hm hcut' :=
  (F).mapCompletion_eq _ _ _ _ m hm _

/-- Identity scalar and exponent maps act identically on the general completion. -/
@[simp]
theorem mapPositiveCompletionOfDegree_id :
    mapPositiveCompletionOfDegree (q := q) (β := β) (RingHom.id R) (AddMonoidHom.id Γ)
      (fun _ _ => by simp) P P (fun _ hn => hn) δ δ hδ hδ id monotone_id
      (fun _ _ _ hn => hn) = RingHom.id (F).completion := by
  simpa only [mapPositiveCompletionOfDegree, positiveMap_id] using (F).mapCompletion_id

variable (P'' : AddSubmonoid Γ'') (g : Γ' →+ Γ'') (ψ' : S →+* U)
  (h' : ∀ p r, Units.map ψ'.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (g p) (g r))
  (hP' : ∀ n ∈ P', g n ∈ P'') (δ'' : Γ'' →+ ℤ) (hδ'' : ∀ n ∈ P'', 0 ≤ δ'' n)
  (m : ℕ → ℕ) (hm : Monotone m)
  (hcut' : ∀ k n, n ∈ P' → (m k : ℤ) < δ' n → (k : ℤ) < δ'' (g n))

/-- Successive general quantum maps compose with the source cutoff `l ∘ m`. -/
theorem mapPositiveCompletionOfDegree_comp :
    mapPositiveCompletionOfDegree (ψ'.comp φ) (g.comp f) (fun p r => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← h', ← h]; rfl)
      P P'' (fun n hn => hP' _ (hP n hn)) δ δ'' hδ hδ'' (l ∘ m) (hl.comp hm)
      (fun k n hn hd => hcut' k (f n) (hP n hn) (hcut (m k) n hn hd)) =
      (mapPositiveCompletionOfDegree ψ' g h' P' P'' hP' δ' δ'' hδ' hδ'' m hm hcut').comp
        (mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut) := by
  unfold mapPositiveCompletionOfDegree
  rw [← (F).mapCompletion_comp]
  congr 1
  exact (positiveMap_comp φ ψ' f g h h' P P' P'' hP hP').symm

end General

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
  apply positiveMap_ideal_le_of_degree φ T.toAddMonoidHom h d.monoid e.monoid
    (fun _ hn => T.map_mem hn) d.degree e.degree
    (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn)
  intro n hn hd
  have := T.degree_gt k hn (by omega)
  omega

/-- Extend a quantum map to the degree completions of its positive coefficient algebras. -/
def mapPositiveCompletion : (F).completion →+* (G).completion :=
  mapPositiveCompletionOfDegree φ T.toAddMonoidHom h d.monoid e.monoid
    (fun _ hn => T.map_mem hn) d.degree e.degree
    (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn)
    T.modulus T.monotone_modulus (fun k _ hn hd => T.degree_gt k hn hd)

/-- The order-`k` component is the induced quotient map at the prescribed source cutoff. -/
@[simp]
theorem projection_mapPositiveCompletion (k : ℕ) (x : (F).completion) :
    (G).projection k (mapPositiveCompletion d e T φ h x) =
      Ideal.quotientMap ((G).ideal (k + 1))
        (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn))
        (positiveMap_ideal_le d e T φ h k) ((F).projection (T.modulus k) x) :=
  projection_mapPositiveCompletionOfDegree φ T.toAddMonoidHom h d.monoid e.monoid
    (fun _ hn => T.map_mem hn) d.degree e.degree
    (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn)
    T.modulus T.monotone_modulus (fun k _ hn hd => T.degree_gt k hn hd) k x

/-- Completed quantum maps agree with the original map on finite positive coefficients. -/
@[simp]
theorem mapPositiveCompletion_toCompletion (x : positiveSubalgebra q β d.monoid) :
    mapPositiveCompletion d e T φ h ((F).toCompletion x) =
      (G).toCompletion (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
        (fun _ hn => T.map_mem hn) x) :=
  mapPositiveCompletionOfDegree_toCompletion φ T.toAddMonoidHom h d.monoid e.monoid
    (fun _ hn => T.map_mem hn) d.degree e.degree
    (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn)
    T.modulus T.monotone_modulus (fun k _ hn hd => T.degree_gt k hn hd) x

/-- The completed map applies the specified coefficient homomorphism to scalars. -/
@[simp]
theorem mapPositiveCompletion_algebraMap (r : R) :
    mapPositiveCompletion d e T φ h (algebraMap R (F).completion r) =
      algebraMap S (G).completion (φ r) :=
  mapPositiveCompletionOfDegree_algebraMap φ T.toAddMonoidHom h d.monoid e.monoid
    (fun _ hn => T.map_mem hn) d.degree e.degree
    (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn)
    T.modulus T.monotone_modulus (fun k _ hn hd => T.degree_gt k hn hd) r

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
  exact mapPositiveCompletionOfDegree_eq φ T.toAddMonoidHom h d.monoid e.monoid
    (fun _ hn => T.map_mem hn) d.degree e.degree
    (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn)
    μ hμ _ T.modulus T.monotone_modulus _

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
  simpa only [mapPositiveCompletion, hf, hm] using
    mapPositiveCompletionOfDegree_id (q := q) (β := β) d.monoid d.degree
      (fun _ hn => d.degree_nonneg hn)

variable (a : PositiveDegrees Γ'') (T' : PositiveDegreeMap e a) (ψ : S →+* U)
  (h' : ∀ p r, Units.map ψ.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (T' p) (T' r))

include h h' in
/-- The factor-set condition for completed transport is preserved by positive degree composition. -/
theorem mapPositiveCompletion_comp_compat (p r : Γ) :
    Units.map (ψ.comp φ).toMonoidHom (q ^ β p r) =
      q'' ^ β'' ((T'.comp T) p) ((T'.comp T) r) := by
  simpa only [PositiveDegreeMap.comp_apply, AddMonoidHom.comp_apply] using
    map_comp_compat φ ψ T.toAddMonoidHom T'.toAddMonoidHom h h' p r

/-- Completed coefficient and exponent maps compose with the composed cutoff modulus. -/
theorem mapPositiveCompletion_comp :
    mapPositiveCompletion d a (T'.comp T) (ψ.comp φ)
      (mapPositiveCompletion_comp_compat d e T φ h a T' ψ h') =
      (mapPositiveCompletion e a T' ψ h').comp (mapPositiveCompletion d e T φ h) := by
  have hf : (T'.comp T).toAddMonoidHom = T'.toAddMonoidHom.comp T.toAddMonoidHom := by
    ext n
    exact PositiveDegreeMap.comp_apply T' T n
  have hm : (T'.comp T).modulus = T.modulus ∘ T'.modulus :=
    funext (PositiveDegreeMap.comp_modulus T' T)
  simpa only [mapPositiveCompletion, hf, hm] using
    mapPositiveCompletionOfDegree_comp φ T.toAddMonoidHom h d.monoid e.monoid
      (fun _ hn => T.map_mem hn) d.degree e.degree
      (fun _ hn => d.degree_nonneg hn) (fun _ hn => e.degree_nonneg hn)
      T.modulus T.monotone_modulus (fun k _ hn hd => T.degree_gt k hn hd)
      a.monoid T'.toAddMonoidHom ψ h' (fun _ hn => T'.map_mem hn) a.degree
      (fun _ hn => a.degree_nonneg hn) T'.modulus T'.monotone_modulus
      (fun k _ hn hd => T'.degree_gt k hn hd)

end Mei.QuantumMonoidAlgebra
