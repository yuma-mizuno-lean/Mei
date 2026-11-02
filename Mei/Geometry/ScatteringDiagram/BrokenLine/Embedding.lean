/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.CoefficientMap
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries

/-!
# Coefficient embeddings of decorated broken lines

An injective coefficient map with an additive equivalence of degrees, compatible with
the signed propagation maps and the geometric velocities, gives a bijection between the
decorated admissible rays for an incoming coefficient and the rays for its image. The
inverse lifts every target degree history through the inverse degree equivalence. Whole
geometric realizations, encounter parameters, incoming tails and final decorations are
retained.

The construction is stated for one fixed signed encounter itinerary. Since the
coefficient and degree maps are injective, no histories merge and no cancellation
occurs; the comparison of general coefficient maps with merging histories is the
separate weighted evaluation identity.

The argument uses `map_homogeneousHistory_of_injective` and
`AdmissibleRayRealization.congrVelocity`. It is the injective half of the coefficient
comparison for whole-component broken lines of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Definitions 3.1–3.3 (arXiv:1411.1394v2),
and Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 and Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M N Γ Δ V J K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommGroup Γ] [AddCommGroup Δ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

section FixedItinerary

variable {n : ℕ} {T : Fin n → Module.End R M} {U : Fin n → Module.End R N}
  [DecidableEq Γ] [DecidableEq Δ]
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  {𝓝 : Δ → Submodule R N} [DirectSum.Decomposition 𝓝]
  {r : M →ₗ[R] N} {σ : Γ ≃+ Δ}
  {hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p)} {hr_injective : Function.Injective r}
  {hT : ∀ j, r.comp (T j) = (U j).comp r}
  {p₀ : Γ} {a : ℳ p₀} {v : Γ → V} {w : Δ → V}
  {hv : ∀ p, v p = w (σ p)}
  {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

include hT hv

/-- The image of an incoming coefficient in the target degree. -/
def coefficientImage (a : ℳ p₀) : 𝓝 (σ p₀) :=
  ⟨r a, hr p₀ a a.property⟩

omit [DecidableEq Γ] [DecidableEq Δ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  [NormedAddCommGroup V] [NormedSpace ℝ V] hT hv in
@[simp]
theorem coefficientImage_coe (a : ℳ p₀) :
    (coefficientImage (r := r) (σ := σ) (hr := hr) (𝓝 := 𝓝) a : N) = r a := (rfl)

omit [DecidableEq Γ] [DecidableEq Δ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  [NormedAddCommGroup V] [NormedSpace ℝ V] hT hv in
/-- The degree equivalence sends `Fin.snoc` to the corresponding `Fin.snoc` of the
pointwise image history. -/
theorem map_snoc (p : Fin n → Γ) (i : Fin (n + 1)) :
    σ (Fin.snoc (α := fun _ => Γ) p p₀ i) =
      Fin.snoc (α := fun _ => Δ) (fun j => σ (p j)) (σ p₀) i := by
  cases i using Fin.lastCases <;> simp

/-- An injective intertwining coefficient map sends each surviving history of the
source support to the pointwise reindexed target history. -/
theorem decoratedHistoryEmbedding (hr_injective : Function.Injective r) (p : Fin n → Γ)
    (hp : p ∈ decoratedHistorySupport ℳ T p₀ a v f ε) :
    (fun j => σ (p j)) ∈
      decoratedHistorySupport 𝓝 U (σ p₀)
        (coefficientImage (r := r) (σ := σ) (hr := hr) (𝓝 := 𝓝) a) w f ε := by
  rw [mem_decoratedHistorySupport] at hp ⊢
  refine ⟨?_, fun j => ?_⟩
  · intro hz
    have he := map_homogeneousHistory_of_injective ℳ 𝓝 r σ hr σ.injective T U hT p a
    apply hp.1
    apply hr_injective
    have hz' : (homogeneousHistory 𝓝 U (σ ∘ p)) (r a) = 0 := by
      simpa only [Function.comp_def, coefficientImage, Subtype.coe_mk] using hz
    rw [he, hz', map_zero]
  · constructor
    · calc
        f j (w (σ (p j))) = f j (v (p j)) := by rw [hv (p j)]
        _ = f j (v (Fin.snoc (α := fun _ => Γ) p p₀ j.succ)) := (hp.2 j).1
        _ = f j (w (σ (Fin.snoc (α := fun _ => Γ) p p₀ j.succ))) := by rw [hv]
        _ = f j (w (Fin.snoc (α := fun _ => Δ) (fun j => σ (p j)) (σ p₀) j.succ)) :=
          congrArg (fun x => f j (w x)) (map_snoc (σ := σ) (p := p) (p₀ := p₀) j.succ)
    · simpa only [hv] using (hp.2 j).2

/-- A target surviving history has the inverse degree history as a preimage in the
source support. -/
theorem decoratedHistoryPreimage (q : Fin n → Δ)
    (hq : q ∈ decoratedHistorySupport 𝓝 U (σ p₀)
      (coefficientImage (r := r) (σ := σ) (hr := hr) (𝓝 := 𝓝) a) w f ε) :
    (fun j => σ.symm (q j)) ∈ decoratedHistorySupport ℳ T p₀ a v f ε := by
  rw [mem_decoratedHistorySupport] at hq ⊢
  refine ⟨?_, fun j => ?_⟩
  · intro hz
    have he := map_homogeneousHistory_of_injective ℳ 𝓝 r σ hr σ.injective T U hT
      (fun j => σ.symm (q j)) a
    have hcomp : (fun j => σ (σ.symm (q j))) = q := by
      funext j
      simp
    have he' : r ((homogeneousHistory ℳ T (fun j => σ.symm (q j))) ↑a) =
        (homogeneousHistory 𝓝 U (fun j => σ (σ.symm (q j)))) (r a) := by
      simpa only [Function.comp_def, coefficientImage, Subtype.coe_mk] using he
    rw [hcomp] at he'
    apply hq.1
    change (homogeneousHistory 𝓝 U q) (r a) = 0
    rw [← he', hz, map_zero]
  · constructor
    · calc
        f j (v (σ.symm (q j))) = f j (w (σ (σ.symm (q j)))) := by rw [hv]
        _ = f j (w (q j)) := by simp
        _ = f j (w (Fin.snoc (α := fun _ => Δ) q (σ p₀) j.succ)) := (hq.2 j).1
        _ = f j (w (σ (Fin.snoc (α := fun _ => Γ)
              (fun j => σ.symm (q j)) p₀ j.succ))) := by
          rw [map_snoc]
          simp
        _ = f j (v (Fin.snoc (α := fun _ => Γ)
              (fun j => σ.symm (q j)) p₀ j.succ)) := by rw [hv]
    · calc
        SignType.sign (f j (v (σ.symm (q j)))) =
            SignType.sign (f j (w (σ (σ.symm (q j))))) := by rw [hv]
        _ = SignType.sign (f j (w (q j))) := by simp
        _ = ε j := (hq.2 j).2

/-- The fixed-itinerary coefficient embedding of decorated admissible rays. -/
def decoratedRayMap (hr_injective : Function.Injective r)
    (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    DecoratedAdmissibleRay 𝓝 U (σ p₀)
      (coefficientImage (r := r) (σ := σ) (hr := hr) (𝓝 := 𝓝) a) w f c ε P W S C Q :=
  ⟨⟨fun j => σ (β.1.val j),
    decoratedHistoryEmbedding (σ := σ) (r := r) (hr := hr) (hT := hT) (hv := hv)
      hr_injective β.1.val β.1.property⟩,
    β.2.congrVelocity (v' := fun j => w (Fin.snoc (α := fun _ => Δ)
      (fun j => σ (β.1.val j)) (σ p₀) j)) (by
      funext i
      calc
        v (Fin.snoc (α := fun _ => Γ) β.1.val p₀ i) =
            w (σ (Fin.snoc (α := fun _ => Γ) β.1.val p₀ i)) := hv _
        _ = w (Fin.snoc (α := fun _ => Δ) (fun j => σ (β.1.val j)) (σ p₀) i) := by
          rw [map_snoc])⟩

/-- The map retains the entire geometric realization. -/
@[simp]
theorem decoratedRayMap_ray (hr_injective : Function.Injective r)
    (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    (decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀) (a := a)
      (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr)
      hr_injective β).2.ray = β.2.ray := by
  simp [decoratedRayMap]

/-- The map retains all encounter parameters, including unchanged-degree encounters. -/
@[simp]
theorem decoratedRayMap_parameter (hr_injective : Function.Injective r)
    (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    (decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀) (a := a)
      (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr)
      hr_injective β).2.parameter =
      β.2.parameter := by
  simp [decoratedRayMap]

/-- The final whole decoration of the image is the coefficient image of the source
final decoration. -/
theorem decoratedRayMap_decoration (hr_injective : Function.Injective r)
    (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    (decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀) (a := a)
      (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr)
      hr_injective β).decoration 0 =
      r (β.decoration 0) := by
  rw [DecoratedAdmissibleRay.decoration_zero, DecoratedAdmissibleRay.decoration_zero]
  exact (map_homogeneousHistory_of_injective ℳ 𝓝 r σ hr σ.injective T U hT
    β.1.val a).symm

/-- The fixed-itinerary coefficient embedding is injective. -/
theorem decoratedRayMap_injective (hr_injective : Function.Injective r) :
    Function.Injective (decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀) (a := a)
      (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr) hr_injective) := by
  intro x y hxy
  have hval := congrArg (fun z => z.1.val) hxy
  have hhist : x.1.val = y.1.val := by
    funext j
    exact σ.injective (congrFun hval j)
  have hsub : x.1 = y.1 := Subtype.ext hhist
  apply Sigma.ext hsub
  exact Subsingleton.helim (by rw [hsub]) x.2 y.2

/-- The fixed-itinerary coefficient embedding is surjective: the inverse degree history
provides a preimage. -/
theorem decoratedRayMap_surjective (hr_injective : Function.Injective r) :
    Function.Surjective (decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀) (a := a)
      (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr) hr_injective) := by
  intro y
  let z : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q :=
    ⟨⟨fun j => σ.symm (y.1.val j),
      decoratedHistoryPreimage (σ := σ) (r := r) (hr := hr) (hT := hT) (hv := hv)
        y.1.val y.1.property⟩,
    y.2.congrVelocity (v' := fun j => v (Fin.snoc (α := fun _ => Γ)
      (fun j => σ.symm (y.1.val j)) p₀ j)) (by
      funext i
      calc
        w (Fin.snoc (α := fun _ => Δ) y.1.val (σ p₀) i) =
            w (σ (Fin.snoc (α := fun _ => Γ) (fun j => σ.symm (y.1.val j)) p₀ i)) := by
          rw [map_snoc]
          simp
        _ = v (Fin.snoc (α := fun _ => Γ) (fun j => σ.symm (y.1.val j)) p₀ i) :=
          (hv _).symm)⟩
  refine ⟨z, ?_⟩
  have hhist : (decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀)
      (a := a) (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr)
      hr_injective z).1.val = y.1.val := by
    funext j
    simp [z, decoratedRayMap]
  have hsub : (decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀)
      (a := a) (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr)
      hr_injective z).1 = y.1 := Subtype.ext hhist
  apply Sigma.ext hsub
  exact Subsingleton.helim (by rw [hsub]) _ _

/-- The fixed-itinerary coefficient embedding is a bijection of decorated rays. -/
def decoratedRayEquiv (hr_injective : Function.Injective r) :
    DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q ≃
      DecoratedAdmissibleRay 𝓝 U (σ p₀)
        (coefficientImage (r := r) (σ := σ) (hr := hr) (𝓝 := 𝓝) a) w f c ε P W S C Q :=
  Equiv.ofBijective (decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀) (a := a)
      (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr) hr_injective)
    ⟨decoratedRayMap_injective hr_injective, decoratedRayMap_surjective hr_injective⟩

/-- The bijection acts by the fixed-itinerary coefficient embedding. -/
@[simp]
theorem decoratedRayEquiv_apply (hr_injective : Function.Injective r)
    (β : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q) :
    (decoratedRayEquiv (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀) (a := a)
      (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
      (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr)
      hr_injective) β =
      decoratedRayMap (T := T) (U := U) (ℳ := ℳ) (𝓝 := 𝓝) (p₀ := p₀) (a := a)
        (v := v) (w := w) (hv := hv) (hT := hT) (f := f) (c := c) (ε := ε)
        (P := P) (W := W) (S := S) (C := C) (Q := Q) (σ := σ) (r := r) (hr := hr)
        hr_injective β := (rfl)

end FixedItinerary

end Mei
