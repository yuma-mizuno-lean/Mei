/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.DirectSum.Component
public import Mei.Algebra.DirectSum.Map
public import Mei.Combinatorics.Quiver.Path
public import TauCeti.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Homogeneous histories along quiver paths

Let every vertex `q` of a quiver carry a module `M q` with an internal direct-sum
decomposition `ℳ q : ι q → Submodule R (M q)`, and every arrow `e : b ⟶ c` a linear map
`T e : M b → M c`. The modules and the degree types may differ from vertex to vertex.
A path then has the composite `Quiver.Path.composeLinear T p` of its arrow maps.

A *degree history* of a path selects a degree in the target of each of its arrows
(`Quiver.Path.Degrees`). Inserting the homogeneous projection to the selected degree
after every arrow gives `Quiver.Path.homogeneousHistory`. It retains whole homogeneous
decorations: a nonzero final value forces every intermediate decoration to be nonzero.

This is the finite component expansion of transfer compositions between graded modules.
* For a fixed input only finitely many histories are nonzero, and they sum to the
  composite; no finiteness of the degree types is needed.
* Concatenation of paths concatenates histories and composes their maps, and an arrow
  carrying the identity selects a component of the previous decoration. The final
  selection of a degree keeps a history of that terminal degree and kills the others.
* Linear output maps preserve a uniformly supported expansion. Along a nonempty path,
  restricting that sum to a last degree gives its terminal homogeneous component.
* A finite set containing the contributing histories of every input in the range of a
  linear map gives an identity of linear maps; finite generation of the input range is
  a sufficient condition.
* Vertexwise linear maps intertwining two arrow families and carrying homogeneous
  pieces along degree maps preserve the expansion; homogeneity and injectivity are
  needed only at targets of arrows. A target history is the sum of the images of the
  source histories over it, where several source degrees may merge and cancel;
  injective degree maps give componentwise naturality. Families of degree
  isomorphisms lift to isomorphisms of histories, including their inverses.
  An injective final map reflects
  selected linear-map identities from the target expansion to the source.

In a one-object quiver, `Quiver.SingleObj.pathOfFn` turns a finite sequence of arrows
into a path, and `Quiver.SingleObj.degreesPathOfFn` identifies its degree histories with
functions on the positions. This recovers the single-module histories of
`Mei.LinearAlgebra.GradedModule.History.Basic`.

Paths are Mathlib's `Quiver.Path`; concatenation is `Quiver.Path.comp`, and the composite
is Mathlib's `CategoryTheory.composePath` in semimodules. The finiteness
and regrouping arguments use `DirectSum.sum_support_decompose`,
`DirectSum.decompose_map_eq_sum` and Tau Ceti's `DirectSum.map_decompose_shift`.
-/

public noncomputable section

open Mei

universe u v w x y

namespace Quiver.Path

variable {Q : Type x} [Quiver.{y} Q] {a : Q}

/-- A degree history of a path: a degree of the target of each arrow, the latest arrow
last. It is reducible and exposed, so that a degree history of `p.cons e` is a pair
for instance search and rewriting. -/
@[expose, reducible]
def Degrees (ι : Q → Type w) : {b : Q} → Path a b → Type w
  | _, nil => PUnit
  | _, @cons _ _ _ _ c p _ => Degrees ι p × ι c

variable {ι : Q → Type w}

/-- Degree histories have decidable equality when the degree types do. -/
instance decidableEqDegrees [∀ q, DecidableEq (ι q)] :
    ∀ {b : Q} (p : Path a b), DecidableEq (p.Degrees ι)
  | _, nil => inferInstanceAs (DecidableEq PUnit)
  | _, cons p _ => @instDecidableEqProd _ _ (decidableEqDegrees p) _

/-- A degree history of a concatenation is a pair of degree histories. -/
def degreesComp {b : Q} (p : Path a b) :
    ∀ {c : Q} (q : Path b c), (p.comp q).Degrees ι ≃ p.Degrees ι × q.Degrees ι
  | _, nil => (Equiv.prodPUnit _).symm
  | _, cons q _ => ((degreesComp p q).prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

/-- Concatenating with the empty path appends the trivial history. Not a simp lemma:
simp already normalizes `p.comp nil` in the type of the equivalence. -/
theorem degreesComp_nil {b : Q} (p : Path a b) (d : (p.comp nil).Degrees ι) :
    degreesComp (ι := ι) p (nil : Path b b) d = (d, PUnit.unit) := (rfl)

theorem degreesComp_symm_nil {b : Q} (p : Path a b) (d : p.Degrees ι) (u : PUnit) :
    (degreesComp (ι := ι) p (nil : Path b b)).symm (d, u) = d := (rfl)

/-- Concatenating with a path ending in an arrow splits off its last degree. -/
theorem degreesComp_cons {b c e : Q} (p : Path a b) (q : Path b c) (f : c ⟶ e)
    (d : (p.comp q).Degrees ι) (i : ι e) :
    degreesComp (ι := ι) p (q.cons f) ((d, i) : ((p.comp q).cons f).Degrees ι) =
      ((degreesComp (ι := ι) p q d).1, ((degreesComp (ι := ι) p q d).2, i)) := (rfl)

theorem degreesComp_symm_cons {b c e : Q} (p : Path a b) (q : Path b c) (f : c ⟶ e)
    (d : p.Degrees ι) (d' : q.Degrees ι) (i : ι e) :
    (degreesComp (ι := ι) p (q.cons f)).symm (d, (d', i)) =
      (((degreesComp (ι := ι) p q).symm (d, d'), i) : ((p.comp q).cons f).Degrees ι) := (rfl)

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

/-- Lift a family of degree isomorphisms to an isomorphism of all histories
of a path. -/
def Degrees.mapEquiv {κ : Q → Type*} (σ : ∀ q, ι q ≃ κ q) :
    ∀ {b : Q} (p : Path a b), p.Degrees ι ≃ p.Degrees κ
  | _, nil => Equiv.ofUnique _ _
  | _, cons p _ => (Degrees.mapEquiv σ p).prodCongr (σ _)

/-- The forward map of a lifted degree isomorphism is the existing degree map. -/
@[simp]
theorem Degrees.mapEquiv_apply {κ : Q → Type*} (σ : ∀ q, ι q ≃ κ q)
    {b : Q} (p : Path a b) (d : p.Degrees ι) :
    Degrees.mapEquiv σ p d = Degrees.map (fun q => σ q) p d := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    obtain ⟨d, i⟩ := d
    simp only [Degrees.mapEquiv, Equiv.prodCongr_apply, Prod.map_apply,
      Degrees.map_cons, ih]

/-- The inverse of a lifted degree isomorphism is the inverse degree map. -/
@[simp]
theorem Degrees.mapEquiv_symm_apply {κ : Q → Type*} (σ : ∀ q, ι q ≃ κ q)
    {b : Q} (p : Path a b) (d : p.Degrees κ) :
    (Degrees.mapEquiv σ p).symm d = Degrees.map (fun q => (σ q).symm) p d := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    obtain ⟨d, i⟩ := d
    simp only [Degrees.mapEquiv, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
      Prod.map_apply, Degrees.map_cons, ih]

section Linear

variable {R : Type u} [Semiring R]
  {M : Q → Type v} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)

/-- The composite of the arrow maps along a path: Mathlib's `composePath` of the image of
the path in semimodules. The latest arrow acts last. -/
def composeLinear {b : Q} (p : Path a b) : M a →ₗ[R] M b :=
  (CategoryTheory.composePath
    (({ obj q := SemimoduleCat.of R (M q), map e := SemimoduleCat.ofHom (T e) } :
      Q ⥤q SemimoduleCat.{v} R).mapPath p)).hom

@[simp]
theorem composeLinear_nil : (nil : Path a a).composeLinear T = LinearMap.id := (rfl)

@[simp]
theorem composeLinear_cons {b c : Q} (p : Path a b) (e : b ⟶ c) :
    (p.cons e).composeLinear T = (T e).comp (p.composeLinear T) := (rfl)

/-- The composite along a concatenation is the composite of the two composites. -/
@[simp]
theorem composeLinear_comp {b c : Q} (p : Path a b) (q : Path b c) :
    (p.comp q).composeLinear T = (q.composeLinear T).comp (p.composeLinear T) := by
  rw [composeLinear, Prefunctor.mapPath_comp, CategoryTheory.composePath_comp,
    SemimoduleCat.hom_comp]
  rfl

variable {ι : Q → Type w} [∀ q, DecidableEq (ι q)] (ℳ : ∀ q, ι q → Submodule R (M q))
  [∀ q, DirectSum.Decomposition (ℳ q)]

/-- Propagation along a path, keeping only the selected homogeneous component after each
arrow. The empty path leaves the input unchanged. -/
def homogeneousHistory : {b : Q} → (p : Path a b) → p.Degrees ι → M a →ₗ[R] M b
  | _, nil, _ => LinearMap.id
  | _, cons p e, d =>
    (homogeneousComponent (ℳ _) d.2).comp ((T e).comp (homogeneousHistory p d.1))

@[simp]
theorem homogeneousHistory_nil (d : (nil : Path a a).Degrees ι) :
    (nil : Path a a).homogeneousHistory T ℳ d = LinearMap.id := (rfl)

/-- One more arrow applies its map to the history and selects the whole component of
the recorded degree. -/
theorem homogeneousHistory_cons {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι)
    (i : ι c) :
    (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) =
      (homogeneousComponent (ℳ c) i).comp ((T e).comp (p.homogeneousHistory T ℳ d)) :=
  (rfl)

theorem homogeneousHistory_cons_apply {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) (x : M a) :
    (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) x =
      (DirectSum.decompose (ℳ c) (T e (p.homogeneousHistory T ℳ d x)) i : M c) := by
  rw [homogeneousHistory_cons, LinearMap.comp_apply, LinearMap.comp_apply,
    homogeneousComponent_apply]

/-- The output of a nonempty history lies in its last selected homogeneous piece. -/
theorem homogeneousHistory_cons_mem {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι)
    (i : ι c) (x : M a) :
    (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) x ∈ ℳ c i := by
  rw [homogeneousHistory_cons, LinearMap.comp_apply]
  exact homogeneousComponent_mem (ℳ c) i _

/-- A vanished intermediate decoration cannot yield a nonzero final history. -/
theorem homogeneousHistory_ne_zero_of_cons {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) {x : M a}
    (h : (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) x ≠ 0) :
    p.homogeneousHistory T ℳ d x ≠ 0 := by
  intro hz
  apply h
  rw [homogeneousHistory_cons, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero,
    map_zero]

/-- Selecting the terminal degree of a nonempty history returns that history. -/
@[simp]
theorem homogeneousComponent_comp_homogeneousHistory_cons {b c : Q} (p : Path a b)
    (e : b ⟶ c) (d : p.Degrees ι) (i : ι c) :
    (homogeneousComponent (ℳ c) i).comp
        ((p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι)) =
      (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) := by
  ext x
  exact homogeneousComponent_apply_of_mem (ℳ c) (homogeneousHistory_cons_mem T ℳ p e d i x)

/-- A nonempty history has no component in a degree other than its terminal degree. -/
@[simp]
theorem homogeneousComponent_comp_homogeneousHistory_cons_of_ne {b c : Q} (p : Path a b)
    (e : b ⟶ c) (d : p.Degrees ι) (i η : ι c) (h : i ≠ η) :
    (homogeneousComponent (ℳ c) η).comp
        ((p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι)) = 0 := by
  ext x
  exact homogeneousComponent_apply_of_mem_ne (ℳ c) (homogeneousHistory_cons_mem T ℳ p e d i x) h

/-- An arrow carrying the identity selects a component of the previous decoration. -/
theorem homogeneousHistory_cons_of_eq_id {b : Q} (p : Path a b) (e : b ⟶ b)
    (he : T e = LinearMap.id) (d : p.Degrees ι) (i : ι b) :
    (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) =
      (homogeneousComponent (ℳ b) i).comp (p.homogeneousHistory T ℳ d) := by
  rw [homogeneousHistory_cons, he, LinearMap.id_comp]

/-- Inserting an identity arrow after a nonempty history keeps that history in its
terminal degree and kills it in every other degree. -/
theorem homogeneousHistory_cons_cons_of_eq_id {b c : Q} (p : Path a b) (e : b ⟶ c)
    (e' : c ⟶ c) (he : T e' = LinearMap.id) (d : p.Degrees ι) (i η : ι c) :
    ((p.cons e).cons e').homogeneousHistory T ℳ
        (((d, i), η) : ((p.cons e).cons e').Degrees ι) =
      if i = η then (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι)
      else 0 := by
  rw [homogeneousHistory_cons_of_eq_id T ℳ _ e' he]
  split_ifs with h
  · subst h
    exact homogeneousComponent_comp_homogeneousHistory_cons T ℳ p e d i
  · exact homogeneousComponent_comp_homogeneousHistory_cons_of_ne T ℳ p e d i η h

/-- Along a concatenation, the history of a pair of degree histories is the composite of
the two histories. -/
theorem homogeneousHistory_comp {b : Q} (p : Path a b) :
    ∀ {c : Q} (q : Path b c) (d : p.Degrees ι) (d' : q.Degrees ι),
      (p.comp q).homogeneousHistory T ℳ ((degreesComp (ι := ι) p q).symm (d, d')) =
        (q.homogeneousHistory T ℳ d').comp (p.homogeneousHistory T ℳ d)
  | _, nil, d, _ => (LinearMap.id_comp _).symm
  | _, cons q e, d, d' => by
    calc _ = (homogeneousComponent (ℳ _) d'.2).comp ((T e).comp
          ((p.comp q).homogeneousHistory T ℳ ((degreesComp (ι := ι) p q).symm (d, d'.1)))) :=
        homogeneousHistory_cons T ℳ (p.comp q) e _ d'.2
      _ = _ := by
        rw [homogeneousHistory_comp p q d d'.1, homogeneousHistory_cons T ℳ q e d'.1 d'.2]
        rfl

section Finite

/-- Only finitely many degree histories have nonzero whole decorations for a fixed input.
Neither the degree types nor the homogeneous supports need be finite. -/
theorem finite_support_homogeneousHistory :
    ∀ {b : Q} (p : Path a b) (x : M a),
      (Function.support fun d : p.Degrees ι => p.homogeneousHistory T ℳ d x).Finite
  | _, nil, _ => Set.toFinite _
  | _, cons p e, x => by
    classical
    have hS := finite_support_homogeneousHistory p x
    apply (Finset.finite_toSet (hS.toFinset.biUnion fun d =>
      (DirectSum.decompose (ℳ _) (T e (p.homogeneousHistory T ℳ d x))).support.image
        fun i => ((d, i) : (p.cons e).Degrees ι))).subset
    rintro ⟨d, i⟩ hd
    have hd' : (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) x ≠ 0 := hd
    refine Finset.mem_biUnion.mpr ⟨d, (Set.Finite.mem_toFinset _).mpr
      (homogeneousHistory_ne_zero_of_cons T ℳ p e d i hd'), Finset.mem_image.mpr
        ⟨i, DFinsupp.mem_support_iff.mpr fun h => hd' ?_, rfl⟩⟩
    rw [homogeneousHistory_cons_apply, h]
    rfl

/-- The finite set of degree histories whose final whole decoration is nonzero. -/
def historySupport {b : Q} (p : Path a b) (x : M a) : Finset (p.Degrees ι) :=
  (finite_support_homogeneousHistory T ℳ p x).toFinset

/-- Membership retains precisely the histories with nonzero decoration. -/
@[simp]
theorem mem_historySupport {b : Q} (p : Path a b) (x : M a) (d : p.Degrees ι) :
    d ∈ p.historySupport T ℳ x ↔ p.homogeneousHistory T ℳ d x ≠ 0 :=
  Set.Finite.mem_toFinset _

/-- Zero input has no contributing histories. -/
@[simp]
theorem historySupport_zero {b : Q} (p : Path a b) : p.historySupport T ℳ 0 = ∅ := by
  ext d
  simp

open Classical in
/-- Extend each contributing history by exactly the nonzero output components of the
next arrow. -/
theorem historySupport_cons {b c : Q} (p : Path a b) (e : b ⟶ c) (x : M a) :
    (p.cons e).historySupport T ℳ x =
      (p.historySupport T ℳ x).biUnion fun d =>
        (DirectSum.decompose (ℳ c) (T e (p.homogeneousHistory T ℳ d x))).support.image
          fun i => ((d, i) : (p.cons e).Degrees ι) := by
  ext ⟨d, i⟩
  rw [mem_historySupport, Finset.mem_biUnion]
  constructor
  · intro h
    refine ⟨d, (mem_historySupport ..).mpr (homogeneousHistory_ne_zero_of_cons T ℳ p e d i h),
      Finset.mem_image.mpr ⟨i, DFinsupp.mem_support_iff.mpr fun hz => h ?_, rfl⟩⟩
    rw [homogeneousHistory_cons_apply, hz]
    rfl
  · rintro ⟨d', _, hy⟩
    obtain ⟨i', hi, he⟩ := Finset.mem_image.mp hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rw [homogeneousHistory_cons_apply]
    exact fun hz => DFinsupp.mem_support_iff.mp hi (Subtype.val_injective hz)

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

/-- Summing exactly the nonzero histories recovers the composite along the path. -/
@[simp]
theorem sum_homogeneousHistory :
    ∀ {b : Q} (p : Path a b) (x : M a),
      ∑ d ∈ p.historySupport T ℳ x, p.homogeneousHistory T ℳ d x = p.composeLinear T x
  | _, nil, x => by
    classical
    by_cases hx : x = 0
    · rw [hx, historySupport_zero, Finset.sum_empty, map_zero]
    · have hs : (nil : Path a a).historySupport T ℳ x = {PUnit.unit} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_historySupport ..).mpr hx, fun _ _ => rfl⟩
      rw [hs, Finset.sum_singleton]
      rfl
  | _, cons p e, x => by
    classical
    rw [historySupport_cons, Finset.sum_biUnion (historySupport_cons_disjoint T ℳ p e x)]
    trans ∑ d ∈ p.historySupport T ℳ x, T e (p.homogeneousHistory T ℳ d x)
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_image fun i _ j _ h => congrArg Prod.snd h]
      simp only [homogeneousHistory_cons_apply]
      exact DirectSum.sum_support_decompose (ℳ _) _
    · rw [← map_sum, sum_homogeneousHistory p x]
      rfl

end Finite

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
  | _, nil, _, _ => rfl
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
    rw [← map_sum, sum_homogeneousHistory]
    rfl
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

/-- A uniform support of history maps contains the pointwise support of every input. -/
theorem historySupport_subset_of_comp_eq_zero (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) (y : E) :
    p.historySupport T ℳ (f y) ⊆ S := by
  intro d hd
  by_contra h
  exact (mem_historySupport T ℳ p (f y) d).mp hd (LinearMap.congr_fun (hS d h) y)

/-- Uniform finite contributing support on the input range gives the expansion as an
identity of linear maps. -/
theorem sum_homogeneousHistory_comp_eq (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) :
    ∑ d ∈ S, (p.homogeneousHistory T ℳ d).comp f = (p.composeLinear T).comp f := by
  ext y
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← sum_homogeneousHistory T ℳ p (f y)]
  exact (Finset.sum_subset (historySupport_subset_of_comp_eq_zero T ℳ p f S hS y)
    fun d _ hd => by simpa using hd).symm

/-- A linear output map commutes with the uniformly supported history expansion.
The support bound is imposed before the output map. -/
theorem sum_comp_homogeneousHistory_comp_eq {O : Type*} [AddCommMonoid O] [Module R O]
    (g : M b →ₗ[R] O) (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) :
    ∑ d ∈ S, g.comp ((p.homogeneousHistory T ℳ d).comp f) =
      g.comp ((p.composeLinear T).comp f) := by
  rw [← sum_homogeneousHistory_comp_eq T ℳ p f S hS]
  ext y
  simp

open Classical in
/-- Within a uniformly supported expansion along a nonempty path, selecting the
histories with last degree `η` isolates the final `η`-component of the composite.
The ambient gradings and the intermediate degree types need not be finite. -/
theorem sum_homogeneousHistory_cons_terminal_comp_eq {b c : Q} (p : Path a b)
    (e : b ⟶ c) (η : ι c) (S : Finset ((p.cons e).Degrees ι))
    (hS : ∀ d ∉ S, ((p.cons e).homogeneousHistory T ℳ d).comp f = 0) :
    ∑ d ∈ S.filter (fun d => d.2 = η),
      ((p.cons e).homogeneousHistory T ℳ d).comp f =
        ((homogeneousComponent (ℳ c) η).comp ((p.cons e).composeLinear T)).comp f := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ d ∈ S, (homogeneousComponent (ℳ c) η).comp
        (((p.cons e).homogeneousHistory T ℳ d).comp f) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      obtain ⟨d, i⟩ := d
      by_cases hi : i = η
      · subst η
        simp only [↓reduceIte]
        rw [← LinearMap.comp_assoc, homogeneousComponent_comp_homogeneousHistory_cons]
      · simp only [hi, ↓reduceIte]
        rw [← LinearMap.comp_assoc,
          homogeneousComponent_comp_homogeneousHistory_cons_of_ne T ℳ p e d i η hi,
          LinearMap.zero_comp]
    _ = _ := by
      simpa only [LinearMap.comp_assoc] using
        sum_comp_homogeneousHistory_comp_eq T ℳ (p.cons e) f
          (homogeneousComponent (ℳ c) η) S hS

/-- A finite generating set of inputs gives a uniform finite history support on its span. -/
theorem exists_uniform_historySupport_of_fg (P : Submodule R (M a)) (hP : P.FG) :
    ∃ S : Finset (p.Degrees ι), ∀ d ∉ S, ∀ y ∈ P, p.homogeneousHistory T ℳ d y = 0 := by
  classical
  obtain ⟨s, hs⟩ := hP
  refine ⟨s.biUnion (p.historySupport T ℳ), fun d hd y hy => ?_⟩
  have hker : P ≤ LinearMap.ker (p.homogeneousHistory T ℳ d) := by
    rw [← hs]
    refine Submodule.span_le.mpr fun z hz => LinearMap.mem_ker.mpr ?_
    by_contra hne
    exact hd (Finset.mem_biUnion.mpr ⟨z, hz, (mem_historySupport T ℳ p z d).mpr hne⟩)
  exact hker hy

/-- Finite generation of the input range ensures a uniform finite history support. -/
theorem exists_uniform_historySupport (hf : (LinearMap.range f).FG) :
    ∃ S : Finset (p.Degrees ι), ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0 := by
  obtain ⟨S, hS⟩ := exists_uniform_historySupport_of_fg T ℳ p _ hf
  exact ⟨S, fun d hd => LinearMap.ext fun y => hS d hd (f y) (LinearMap.mem_range_self f y)⟩

open Classical in
/-- Selecting histories in a uniform support gives the same value as selecting in the
pointwise nonzero support. -/
theorem sum_ite_homogeneousHistory_comp_apply (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) (P : p.Degrees ι → Prop)
    (y : E) :
    (∑ d ∈ S, if P d then (p.homogeneousHistory T ℳ d).comp f else 0) y =
      ∑ d ∈ p.historySupport T ℳ (f y),
        if P d then p.homogeneousHistory T ℳ d (f y) else 0 := by
  trans ∑ d ∈ S, if P d then p.homogeneousHistory T ℳ d (f y) else 0
  · simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun d _ => by split_ifs <;> rfl
  exact (Finset.sum_subset (historySupport_subset_of_comp_eq_zero T ℳ p f S hS y)
    fun d _ hd => by
      have hz : p.homogeneousHistory T ℳ d (f y) = 0 := by simpa using hd
      simp [hz]).symm

open Classical in
/-- Selected linear-map sums agree over any two uniform supports. -/
theorem sum_ite_homogeneousHistory_comp_eq (S S' : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0)
    (hS' : ∀ d ∉ S', (p.homogeneousHistory T ℳ d).comp f = 0) (P : p.Degrees ι → Prop) :
    (∑ d ∈ S, if P d then (p.homogeneousHistory T ℳ d).comp f else 0) =
      ∑ d ∈ S', if P d then (p.homogeneousHistory T ℳ d).comp f else 0 := by
  ext y
  rw [sum_ite_homogeneousHistory_comp_apply T ℳ p f S hS,
    sum_ite_homogeneousHistory_comp_apply T ℳ p f S' hS']

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
