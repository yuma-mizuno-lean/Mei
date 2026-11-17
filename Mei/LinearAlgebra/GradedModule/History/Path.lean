/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.LinearAlgebra.Graded.History.Expansion
public import Mei.Algebra.DirectSum.Map
public import Mei.Combinatorics.Quiver.Path
public import TauCeti.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Regrading homogeneous histories along quiver paths

Tau Ceti supplies degree histories, homogeneous projections along a path and their finite
expansion. Vertexwise linear intertwiners transport such histories along degree maps.
Several source degrees can merge and cancel, so a target history is the sum of the images
of its source refinements. Injective degree maps give componentwise transport and an
injective final map reflects selected expansion identities.

For a one-object quiver, degree histories of `Quiver.SingleObj.pathOfFn` identify with
functions on the positions.
-/

public noncomputable section

universe u v w x y

namespace Quiver.Path

variable {Q : Type x} [Quiver.{y} Q] {a : Q}

variable {ι : Q → Type w}

/-- Vertex-selected degrees split into the selections on the two path blocks. -/
@[simp]
theorem degreesComp_degreesOfVertices (s : ∀ q, ι q) {b c : Q}
    (p : Path a b) (q : Path b c) :
    degreesComp (ι := ι) p q ((p.comp q).degreesOfVertices s) =
      (p.degreesOfVertices s, q.degreesOfVertices s) := by
  induction q with
  | nil =>
    rw [degreesComp_nil, degreesOfVertices_nil]
    rfl
  | cons q e ih =>
    erw [degreesOfVertices_cons s (p.comp q) e, degreesComp_cons,
      degreesOfVertices_cons s q e]
    exact congrArg (fun d : p.Degrees ι × q.Degrees ι => (d.1, (d.2, s _))) ih

/-- Transport degree histories along vertexwise degree maps. -/
def Degrees.map {κ : Q → Type*} (σ : ∀ q, ι q → κ q) :
    ∀ {b : Q} (p : Path a b), p.Degrees ι → p.Degrees κ
  | _, nil, _ => PUnit.unit
  | _, cons p _, d => (Degrees.map σ p d.1, σ _ d.2)

@[simp]
theorem Degrees.map_cons {κ : Q → Type*} (σ : ∀ q, ι q → κ q) {b c : Q} (p : Path a b)
    (e : b ⟶ c) (d : p.Degrees ι) (i : ι c) :
    Degrees.map σ (p.cons e) ((d, i) : (p.cons e).Degrees ι) =
      ((Degrees.map σ p d, σ c i) : (p.cons e).Degrees κ) := (rfl)

/-- Identity degree maps retain the entire history. -/
@[simp]
theorem Degrees.map_id : ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
    Degrees.map (fun _ => id) p d = d
  | _, nil, _ => rfl
  | _, cons p _, d => by
    exact Prod.ext (Degrees.map_id p d.1) rfl

/-- Successive vertexwise degree maps act on every degree of a history by composition. -/
@[simp]
theorem Degrees.map_map {κ ξ : Q → Type*} (σ : ∀ q, ι q → κ q)
    (τ : ∀ q, κ q → ξ q) : ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
    Degrees.map τ p (Degrees.map σ p d) = Degrees.map (fun q => τ q ∘ σ q) p d
  | _, nil, _ => rfl
  | _, cons p _, d => by
    exact Prod.ext (Degrees.map_map σ τ p d.1) rfl

/-- Vertexwise degree equivalences reindex complete histories, retaining every arrow. -/
def Degrees.mapEquiv {κ : Q → Type*} (σ : ∀ q, ι q ≃ κ q) :
    ∀ {b : Q} (p : Path a b), p.Degrees ι ≃ p.Degrees κ
  | _, nil => Equiv.equivPUnit _
  | _, @cons _ _ _ _ c p _ => (Degrees.mapEquiv σ p).prodCongr (σ c)

/-- The history equivalence applies the degree maps at every visited vertex. -/
@[simp]
theorem Degrees.mapEquiv_apply {κ : Q → Type*} (σ : ∀ q, ι q ≃ κ q) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      Degrees.mapEquiv σ p d = Degrees.map (fun q => σ q) p d
  | _, nil, _ => rfl
  | _, cons p e, d => by
    simpa only [Degrees.mapEquiv, Equiv.prodCongr_apply, Degrees.map_cons] using
      Prod.ext (Degrees.mapEquiv_apply σ p d.1) (rfl : σ _ d.2 = σ _ d.2)

/-- The inverse equivalence applies the inverse degree maps at every encountered vertex. -/
@[simp]
theorem Degrees.mapEquiv_symm_apply {κ : Q → Type*} (σ : ∀ q, ι q ≃ κ q) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees κ),
      (Degrees.mapEquiv σ p).symm d = Degrees.map (fun q => (σ q).symm) p d
  | _, nil, _ => rfl
  | _, cons p e, d => by
    obtain ⟨d, i⟩ := d
    simp only [Degrees.mapEquiv, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
      Degrees.map_cons]
    exact Prod.ext (Degrees.mapEquiv_symm_apply σ p d) rfl

/-- Degree maps commute with the decomposition of histories along a
concatenation. The two outer pair components retain the degrees of the two
blocks after regrading. -/
theorem Degrees.map_comp {κ : Q → Type*} (σ : ∀ q, ι q → κ q) {b : Q} (p : Path a b) :
    ∀ {c : Q} (q : Path b c) (d : (p.comp q).Degrees ι),
      degreesComp (ι := κ) p q (Degrees.map σ (p.comp q) d) =
        (Degrees.map σ p (degreesComp (ι := ι) p q d).1,
          Degrees.map σ q (degreesComp (ι := ι) p q d).2)
  | _, nil, _ => by
    rw [degreesComp_nil, degreesComp_nil]
    rfl
  | _, cons q e, d => by
    obtain ⟨d, i⟩ := d
    -- Fix the dependent path and history types before applying the induction hypothesis.
    change degreesComp (ι := κ) p (q.cons e) (Degrees.map σ ((p.comp q).cons e)
      ((d, i) : ((p.comp q).cons e).Degrees ι)) =
      (Degrees.map σ p (degreesComp (ι := ι) p (q.cons e)
        ((d, i) : ((p.comp q).cons e).Degrees ι)).1,
        Degrees.map σ (q.cons e) (degreesComp (ι := ι) p (q.cons e)
          ((d, i) : ((p.comp q).cons e).Degrees ι)).2)
    rw [Degrees.map_cons, degreesComp_cons, Degrees.map_comp σ p q d]
    rw [degreesComp_cons p q e d i, Degrees.map_cons σ q e _ i]

section Linear

variable {R : Type u} [Semiring R]
  {M : Q → Type v} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)

variable {ι : Q → Type w} [∀ q, DecidableEq (ι q)] (ℳ : ∀ q, ι q → Submodule R (M q))
  [∀ q, DirectSum.Decomposition (ℳ q)]

open Classical in
private theorem historySupport_cons_disjoint {b c : Q} (p : Path a b) (e : b ⟶ c)
    (x : M a) :
    Set.PairwiseDisjoint (↑(p.historySupport T ℳ x) : Set (p.Degrees ι)) fun d =>
      (DirectSum.decompose (ℳ c) (T e (p.homogeneousHistory T ℳ d x))).support.image
        fun i => ((d, i) : (p.cons e).Degrees ι) := by
  intro d _ d' _ hdd'
  refine Finset.disjoint_left.mpr fun y hy hy' => ?_
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨i', _, he⟩ := Finset.mem_image.mp hy'
  exact hdd' (congrArg Prod.fst he).symm

section Regrading

variable {N : Q → Type*} [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]
  (U : ∀ {b c : Q}, (b ⟶ c) → N b →ₗ[R] N c)
  {κ : Q → Type*} [∀ q, DecidableEq (κ q)] (𝓝 : ∀ q, κ q → Submodule R (N q))
  [∀ q, DirectSum.Decomposition (𝓝 q)]
  (r : ∀ q, M q →ₗ[R] N q) (σ : ∀ q, ι q → κ q)
  (hr : ∀ {b c : Q} (_ : b ⟶ c) (i : ι c) (x : M c), x ∈ ℳ c i → r c x ∈ 𝓝 c (σ c i))
  (hT : ∀ {b c : Q} (e : b ⟶ c), (r c).comp (T e) = (U e).comp (r b))

include hr hT

/-- Along injective degree maps, intertwining vertex maps send each history to the history
with the transported degrees. -/
theorem map_homogeneousHistory_of_injective
    (hσ : ∀ {b c : Q} (_ : b ⟶ c), Function.Injective (σ c)) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι) (x : M a),
      r b (p.homogeneousHistory T ℳ d x) =
        p.homogeneousHistory U 𝓝 (Degrees.map σ p d) (r a x)
  | _, nil, _, _ => by simp only [homogeneousHistory_nil, LinearMap.id_apply]
  | _, cons p e, d, x => by
    obtain ⟨d, i⟩ := d
    rw [Degrees.map_cons, homogeneousHistory_cons_apply, homogeneousHistory_cons_apply,
      ← map_homogeneousHistory_of_injective hσ p d x, ← LinearMap.comp_apply (U e),
      ← hT e, LinearMap.comp_apply]
    exact DirectSum.map_decompose_shift (ℳ _) (𝓝 _) (r _).toAddMonoidHom (σ _) (hσ e)
      (hr e) i _

open Classical in
/-- A target history is the finite sum of the images of its source refinements. Neither
the degree maps nor their fibers need be finite, and refinements with the same image are
added before the target component is formed. -/
theorem homogeneousHistory_map_eq_sum :
    ∀ {b : Q} (p : Path a b) (d' : p.Degrees κ) (x : M a),
      p.homogeneousHistory U 𝓝 d' (r a x) =
        ∑ d ∈ p.historySupport T ℳ x,
          if Degrees.map σ p d = d' then r b (p.homogeneousHistory T ℳ d x) else 0
  | _, nil, d', x => by
    have hd : ∀ d : (nil : Path a a).Degrees ι, Degrees.map σ nil d = d' := fun _ => rfl
    simp only [hd, ↓reduceIte]
    rw [← map_sum, sum_homogeneousHistory, homogeneousHistory_nil,
      composeLinear_nil, LinearMap.id_apply, LinearMap.id_apply]
  | _, cons p e, d', x => by
    obtain ⟨d', i'⟩ := d'
    rw [homogeneousHistory_cons_apply, homogeneousHistory_map_eq_sum p d' x]
    simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    rw [historySupport_cons, Finset.sum_biUnion (historySupport_cons_disjoint T ℳ p e x)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_image fun i _ j _ h => congrArg Prod.snd h]
    by_cases hd : Degrees.map σ p d = d'
    · simp only [hd, ↓reduceIte, Degrees.map_cons, Prod.mk.injEq, true_and]
      have hcomm := LinearMap.congr_fun (hT e) (p.homogeneousHistory T ℳ d x)
      simp only [LinearMap.comp_apply] at hcomm
      rw [← hcomm]
      have h := DirectSum.decompose_map_eq_sum (ℳ _) (𝓝 _) (r _).toAddMonoidHom (σ _) (hr e)
        (T e (p.homogeneousHistory T ℳ d x)) i'
      rw [Finset.sum_filter] at h
      simpa only [homogeneousHistory_cons_apply, LinearMap.toAddMonoidHom_coe] using h
    · simp only [hd, ↓reduceIte, Degrees.map_cons, Prod.mk.injEq, false_and, map_zero,
        DirectSum.decompose_zero, Finset.sum_const_zero]
      rfl

open Classical in
/-- Refinements killed by the vertex maps are omitted from the regrouped sum. -/
theorem homogeneousHistory_map_eq_sum_surviving {b : Q} (p : Path a b) (d' : p.Degrees κ)
    (x : M a) :
    p.homogeneousHistory U 𝓝 d' (r a x) =
      ∑ d ∈ (p.historySupport T ℳ x).filter
          (fun d => Degrees.map σ p d = d' ∧ r b (p.homogeneousHistory T ℳ d x) ≠ 0),
        r b (p.homogeneousHistory T ℳ d x) := by
  rw [homogeneousHistory_map_eq_sum T ℳ U 𝓝 r σ hr hT p d' x, ← Finset.sum_filter]
  simpa only [Finset.filter_filter] using
    (Finset.sum_filter_ne_zero (f := fun d => r b (p.homogeneousHistory T ℳ d x))
      ((p.historySupport T ℳ x).filter fun d => Degrees.map σ p d = d')).symm

/-- A nonzero target history admits a source refinement whose decoration survives. -/
theorem exists_homogeneousHistory_ne_zero_of_map_ne_zero {b : Q} (p : Path a b)
    (d' : p.Degrees κ) {x : M a} (hx : p.homogeneousHistory U 𝓝 d' (r a x) ≠ 0) :
    ∃ d : p.Degrees ι, Degrees.map σ p d = d' ∧ r b (p.homogeneousHistory T ℳ d x) ≠ 0 := by
  classical
  rw [homogeneousHistory_map_eq_sum T ℳ U 𝓝 r σ hr hT p d' x] at hx
  obtain ⟨d, _, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  split_ifs at hd with h
  · exact ⟨d, h, hd⟩
  · exact (hd rfl).elim

open Classical in
/-- Selecting target histories commutes with the vertex maps when source histories are
selected by their transported degrees. Source histories with the same image are added
before vanishing target histories are discarded. -/
theorem map_sum_ite_homogeneousHistory {b : Q} (p : Path a b) (E : p.Degrees κ → Prop)
    (x : M a) :
    r b (∑ d ∈ p.historySupport T ℳ x,
      if E (Degrees.map σ p d) then p.homogeneousHistory T ℳ d x else 0) =
      ∑ d' ∈ p.historySupport U 𝓝 (r a x),
        if E d' then p.homogeneousHistory U 𝓝 d' (r a x) else 0 := by
  let S := p.historySupport T ℳ x
  let D := S.image (Degrees.map σ p)
  have hsub : p.historySupport U 𝓝 (r a x) ⊆ D := by
    intro d' hd'
    obtain ⟨d, hd, hn⟩ := exists_homogeneousHistory_ne_zero_of_map_ne_zero T ℳ U 𝓝 r σ hr hT
      p d' ((mem_historySupport ..).mp hd')
    exact Finset.mem_image.mpr ⟨d, (mem_historySupport ..).mpr fun hz => hn (by simp [hz]),
      hd⟩
  rw [map_sum]
  calc
    _ = ∑ d' ∈ D, ∑ d ∈ S with Degrees.map σ p d = d',
        r b (if E (Degrees.map σ p d) then p.homogeneousHistory T ℳ d x else 0) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun d hd => Finset.mem_image_of_mem (Degrees.map σ p) hd) _).symm
    _ = ∑ d' ∈ D, if E d' then p.homogeneousHistory U 𝓝 d' (r a x) else 0 := by
      refine Finset.sum_congr rfl fun d' _ => ?_
      rw [homogeneousHistory_map_eq_sum T ℳ U 𝓝 r σ hr hT p d' x, Finset.sum_filter]
      by_cases hE : E d'
      · simp only [hE, ↓reduceIte]
        refine Finset.sum_congr rfl fun d _ => ?_
        by_cases hd : Degrees.map σ p d = d' <;> simp [hd, hE]
      · simp only [hE, ↓reduceIte]
        refine Finset.sum_eq_zero fun d _ => ?_
        by_cases hd : Degrees.map σ p d = d' <;> simp [hd, hE]
    _ = _ := (Finset.sum_subset hsub fun d' _ hd' => by
      have hz : p.homogeneousHistory U 𝓝 d' (r a x) = 0 := by
        simpa only [mem_historySupport, not_not] using hd'
      simp [hz]).symm

end Regrading

section Uniform

variable {E : Type*} [AddCommMonoid E] [Module R E] {b : Q} (p : Path a b)
  (f : E →ₗ[R] M a)

section Regrading

variable {N : Q → Type*} [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]
  (U : ∀ {b c : Q}, (b ⟶ c) → N b →ₗ[R] N c)
  {κ : Q → Type*} [∀ q, DecidableEq (κ q)] (𝓝 : ∀ q, κ q → Submodule R (N q))
  [∀ q, DirectSum.Decomposition (𝓝 q)]
  (r : ∀ q, M q →ₗ[R] N q) (σ : ∀ q, ι q → κ q)
  (hr : ∀ {b c : Q} (_ : b ⟶ c) (i : ι c) (x : M c), x ∈ ℳ c i → r c x ∈ 𝓝 c (σ c i))
  (hT : ∀ {b c : Q} (e : b ⟶ c), (r c).comp (T e) = (U e).comp (r b))

include hr hT

/-- A source uniform support gives a target uniform support by transport. -/
theorem homogeneousHistory_comp_eq_zero_of_notMem_image (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) (d' : p.Degrees κ)
    (hd' : d' ∉ S.image (Degrees.map σ p)) :
    (p.homogeneousHistory U 𝓝 d').comp ((r a).comp f) = 0 := by
  ext y
  by_contra hy
  obtain ⟨d, hd, hne⟩ := exists_homogeneousHistory_ne_zero_of_map_ne_zero T ℳ U 𝓝 r σ hr hT
    p d' hy
  have hmem : d ∈ S := by
    by_contra h
    have hz := LinearMap.congr_fun (hS d h) y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    exact hne (by rw [hz, map_zero])
  exact hd' (Finset.mem_image.mpr ⟨d, hmem, hd⟩)

open Classical in
/-- Grouped transport of selected histories as an identity of linear maps. Neither the
degree maps nor the vertex maps need be injective, and cancelling groups are allowed. -/
theorem map_sum_ite_homogeneousHistory_comp (S : Finset (p.Degrees ι))
    (S' : Finset (p.Degrees κ)) (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0)
    (hS' : ∀ d' ∉ S', (p.homogeneousHistory U 𝓝 d').comp ((r a).comp f) = 0)
    (P : p.Degrees κ → Prop) :
    (r b).comp (∑ d ∈ S,
      if P (Degrees.map σ p d) then (p.homogeneousHistory T ℳ d).comp f else 0) =
      ∑ d' ∈ S', if P d' then (p.homogeneousHistory U 𝓝 d').comp ((r a).comp f) else 0 := by
  ext y
  simp only [LinearMap.comp_apply]
  rw [sum_ite_homogeneousHistory_comp_apply T ℳ p f S hS,
    sum_ite_homogeneousHistory_comp_apply U 𝓝 p ((r a).comp f) S' hS']
  simpa only [LinearMap.comp_apply] using
    map_sum_ite_homogeneousHistory T ℳ U 𝓝 r σ hr hT p P (f y)

open Classical in
/-- Grouped transport needs only a source uniform support: its image supplies the target
index set, including groups with zero total weight. -/
theorem map_sum_ite_homogeneousHistory_comp_image (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) (P : p.Degrees κ → Prop) :
    (r b).comp (∑ d ∈ S,
      if P (Degrees.map σ p d) then (p.homogeneousHistory T ℳ d).comp f else 0) =
      ∑ d' ∈ S.image (Degrees.map σ p),
        if P d' then (p.homogeneousHistory U 𝓝 d').comp ((r a).comp f) else 0 :=
  map_sum_ite_homogeneousHistory_comp T ℳ p f U 𝓝 r σ hr hT S _ hS
    (homogeneousHistory_comp_eq_zero_of_notMem_image T ℳ p f U 𝓝 r σ hr hT S hS) P

open Classical in
/-- An injective final vertex map reflects selected expansion identities: a source sum of
histories equals `X` once the regrouped target sum equals the image of `X`. -/
theorem sum_ite_homogeneousHistory_comp_eq_of_injective (hr0 : Function.Injective (r b))
    (S : Finset (p.Degrees ι)) (S' : Finset (p.Degrees κ))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0)
    (hS' : ∀ d' ∉ S', (p.homogeneousHistory U 𝓝 d').comp ((r a).comp f) = 0)
    (P : p.Degrees κ → Prop) (X : E →ₗ[R] M b)
    (hX : ∑ d' ∈ S', (if P d' then (p.homogeneousHistory U 𝓝 d').comp ((r a).comp f)
      else 0) = (r b).comp X) :
    ∑ d ∈ S, (if P (Degrees.map σ p d) then (p.homogeneousHistory T ℳ d).comp f else 0) =
      X := by
  refine LinearMap.ext fun y => hr0 ?_
  have h := LinearMap.congr_fun
    ((map_sum_ite_homogeneousHistory_comp T ℳ p f U 𝓝 r σ hr hT S S' hS hS' P).trans hX) y
  simpa only [LinearMap.comp_apply] using h

end Regrading

end Uniform

end Linear

end Quiver.Path

namespace Quiver.SingleObj

variable {α : Type x}

/-- With a constant degree type, a degree history of `pathOfFn T` is a function on the
positions of `T`; index zero is the degree after the last arrow. -/
def degreesPathOfFn (ι : Type w) :
    {n : ℕ} → (T : Fin n → α) → (Fin n → ι) ≃ (pathOfFn T).Degrees fun _ => ι
  | 0, _ => Equiv.equivPUnit _
  | _ + 1, T => (Fin.consEquiv fun _ => ι).symm.trans
      ((Equiv.prodComm _ _).trans ((degreesPathOfFn ι fun j => T j.succ).prodCongr
        (Equiv.refl ι)))

@[simp]
theorem degreesPathOfFn_succ_apply (ι : Type w) {n : ℕ} (T : Fin (n + 1) → α)
    (p : Fin (n + 1) → ι) :
    degreesPathOfFn ι T p =
      ((degreesPathOfFn ι (fun j => T j.succ) (fun j => p j.succ), p 0) :
        (pathOfFn T).Degrees fun _ => ι) := (rfl)

/-- The terminal degree of a sequence history is its first tuple entry, or the
original input degree when the sequence is empty. -/
@[simp]
theorem terminalDegree_degreesPathOfFn {ι : Type w} {n : ℕ} (T : Fin n → α) (d : Fin n → ι)
    (i : ι) :
    Path.Degrees.terminalDegree i (pathOfFn T) (degreesPathOfFn ι T d) =
      Fin.snoc (α := fun _ => ι) d i 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    exact (congrArg Prod.snd (degreesPathOfFn_succ_apply ι T d)).trans
      (Fin.snoc_castSucc (α := fun _ : Fin (n + 2) => ι) i d 0).symm

/-- Transporting degrees along a map commutes with the identification of degree histories
with functions. -/
@[simp]
theorem map_degreesPathOfFn {ι : Type w} {κ : Type*} (σ : ι → κ) :
    ∀ {n : ℕ} (T : Fin n → α) (p : Fin n → ι),
      Path.Degrees.map (fun _ => σ) (pathOfFn T) (degreesPathOfFn ι T p) =
        degreesPathOfFn κ T (σ ∘ p)
  | 0, _, _ => rfl
  | _ + 1, T, p => by
    rw [degreesPathOfFn_succ_apply, degreesPathOfFn_succ_apply]
    exact Prod.ext (map_degreesPathOfFn σ (fun j => T j.succ) fun j => p j.succ) rfl

end Quiver.SingleObj
