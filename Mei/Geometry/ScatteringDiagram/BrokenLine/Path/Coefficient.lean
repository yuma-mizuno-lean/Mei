/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family

/-!
# Coefficient comparisons for varying-chamber ray families

Vertexwise coefficient maps intertwining the transfer maps, together with degree
bijections preserving velocities, identify target rays with exactly the source
rays whose whole final decorations survive. The comparison retains every
encounter, all encounter parameters, and the entire incoming path. Injectivity
of the final chamber map gives a bijection of the unrestricted fibers.

The comparison uses `Quiver.Path.map_homogeneousHistory_of_injective`; intermediate
coefficient modules and degree sets may differ between chambers. In particular,
coefficient cancellation is allowed, and no basis or positive grading is needed.
Whole-component propagation follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M N : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]
  {ι κ : Q → Type*} [∀ q, DecidableEq (ι q)] [∀ q, DecidableEq (κ q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (U : ∀ {b c : Q}, (b ⟶ c) → N b →ₗ[R] N c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  (𝓝 : ∀ q, κ q → Submodule R (N q)) [∀ q, DirectSum.Decomposition (𝓝 q)]
  (r : ∀ q, M q →ₗ[R] N q) (σ : ∀ q, ι q ≃ κ q)
  (hr : ∀ q d x, x ∈ ℳ q d → r q x ∈ 𝓝 q (σ q d))
  (hT : ∀ {b c : Q} (e : b ⟶ c), (r c).comp (T e) = (U e).comp (r b))
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V) (w : ∀ q, κ q → V)
  (hv : ∀ q d, w q (σ q d) = v q d)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)

local notation "x'" => (Subtype.mk (r a x) (hr a i₀ x x.property) : 𝓝 a (σ a i₀))
local notation "src" p:max => pathDecoratedHistorySupport T ℳ i₀ x v ν ε p
local notation "tgt" p:max => pathDecoratedHistorySupport U 𝓝 (σ a i₀) x' w ν ε p
local notation "mapD" p:max => Path.Degrees.mapEquiv σ p

include hr hT hv

/-- A regraded complete history contributes precisely when its source history
obeys the normal rules and its mapped whole decoration is nonzero. -/
theorem mem_pathDecoratedHistorySupport_map_iff (p : Path a b) (d : p.Degrees ι) :
    (mapD p) d ∈ tgt p ↔ d ∈ src p ∧ r b (p.homogeneousHistory T ℳ d x) ≠ 0 := by
  have hm := p.map_homogeneousHistory_of_injective T ℳ U 𝓝 r (fun q => σ q)
    (fun _ => hr _) hT (fun {_ _} _ => (σ _).injective) d x
  have hd := Path.Degrees.reverseVertexLabels_map (fun q => σ q) v w hv i₀ p d
  simp only [Path.Degrees.mapEquiv_apply, mem_pathDecoratedHistorySupport, hd, ← hm]
  constructor
  · rintro ⟨hne, hnorm⟩
    exact ⟨⟨fun hz => hne (by rw [hz, map_zero]), hnorm⟩, hne⟩
  · rintro ⟨⟨_, hnorm⟩, hne⟩
    exact ⟨hne, hnorm⟩

/-- Reindex the surviving complete histories. No coefficient injectivity is
required; the final nonvanishing condition discards every killed history. -/
def pathDecoratedHistoryCoefficientEquiv (p : Path a b) :
    {d : (src p : Type _) // r b (p.homogeneousHistory T ℳ d.val x) ≠ 0} ≃
      (tgt p : Type _) :=
  (Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    ((mapD p).subtypeEquiv fun d =>
      (mem_pathDecoratedHistorySupport_map_iff T U ℳ 𝓝 r σ hr hT i₀ x v w hv ν ε p d).symm)

/-- Reindexing retains the whole history, applying the chosen degree bijections. -/
@[simp]
theorem pathDecoratedHistoryCoefficientEquiv_val (p : Path a b)
    (d : {d : (src p : Type _) // r b (p.homogeneousHistory T ℳ d.val x) ≠ 0}) :
    (pathDecoratedHistoryCoefficientEquiv T U ℳ 𝓝 r σ hr hT i₀ x v w hv ν ε p d).val =
      (mapD p) d.val.val := (rfl)

/-- Every segment velocity is unchanged by the history comparison. This also
identifies the extended closed-chart paths at endpoints where they are not admissible. -/
@[simp↓] -- Preserve the velocity comparison before reindexing its history.
theorem pathDecoratedHistoryCoefficientEquiv_reverseVertexLabels (p : Path a b)
    (d : {d : (src p : Type _) // r b (p.homogeneousHistory T ℳ d.val x) ≠ 0}) :
    Path.Degrees.reverseVertexLabels w (σ a i₀) p
      (pathDecoratedHistoryCoefficientEquiv T U ℳ 𝓝 r σ hr hT
        i₀ x v w hv ν ε p d).val =
      Path.Degrees.reverseVertexLabels v i₀ p d.val.val := by
  rw [pathDecoratedHistoryCoefficientEquiv_val, Path.Degrees.mapEquiv_apply]
  exact Path.Degrees.reverseVertexLabels_map (fun q => σ q) v w hv i₀ p d.val.val

variable (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "SrcRay" p:max X:max => PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X
local notation "TgtRay" p:max X:max => PathDecoratedRay U 𝓝 (σ a i₀) x' w ν ε c P W S C p X
local notation "E" p:max => pathDecoratedHistoryCoefficientEquiv T U ℳ 𝓝 r σ hr hT
  i₀ x v w hv ν ε p

/-- The actual target ray fiber is the surviving source fiber. The same geometric
ray, incoming tail, and all encounter parameters are retained. -/
def pathDecoratedRayCoefficientEquiv (p : Path a b) (X : V) :
    {s : SrcRay p X // r b s.decoration ≠ 0} ≃ TgtRay p X where
  toFun s := ⟨(E p) ⟨s.val.1, by simpa only [PathDecoratedRay.decoration_def] using s.property⟩,
    s.val.2.congrVelocity
      (pathDecoratedHistoryCoefficientEquiv_reverseVertexLabels T U ℳ 𝓝 r σ hr hT
        i₀ x v w hv ν ε p
        ⟨s.val.1, by simpa only [PathDecoratedRay.decoration_def] using s.property⟩).symm⟩
  invFun t :=
    let d := (E p).symm t.1
    ⟨⟨d.val, t.2.congrVelocity (by
      have hd := pathDecoratedHistoryCoefficientEquiv_reverseVertexLabels
        T U ℳ 𝓝 r σ hr hT i₀ x v w hv ν ε p d
      rw [(E p).apply_symm_apply t.1] at hd
      exact hd)⟩,
      by simpa only [PathDecoratedRay.decoration_def] using d.property⟩
  left_inv s := by
    apply Subtype.ext
    apply PathDecoratedRay.ext_history
    exact congrArg (fun d => d.val.val) ((E p).symm_apply_apply
      ⟨s.val.1, by simpa only [PathDecoratedRay.decoration_def] using s.property⟩)
  right_inv t := by
    apply PathDecoratedRay.ext_history
    exact congrArg Subtype.val ((E p).apply_symm_apply t.1)

local notation "F" p:max X:max => pathDecoratedRayCoefficientEquiv T U ℳ 𝓝 r σ hr hT
  i₀ x v w hv ν ε c P W S C p X

/-- The comparison applies the degree bijection to every recorded segment. -/
@[simp]
theorem pathDecoratedRayCoefficientEquiv_history (p : Path a b) (X : V)
    (s : {s : SrcRay p X // r b s.decoration ≠ 0}) :
    ((F p X) s).1.val = (mapD p) s.val.1.val := (rfl)

/-- The whole path and incoming half-line are unchanged under coefficient comparison. -/
@[simp]
theorem pathDecoratedRayCoefficientEquiv_ray (p : Path a b) (X : V)
    (s : {s : SrcRay p X // r b s.decoration ≠ 0}) :
    ((F p X) s).2.ray = s.val.2.ray := by
  simp only [pathDecoratedRayCoefficientEquiv, Equiv.coe_fn_mk,
    AdmissibleRayRealization.ray_congrVelocity]

/-- Unchanged-degree encounters retain their parameters as well as their order. -/
@[simp]
theorem pathDecoratedRayCoefficientEquiv_parameter (p : Path a b) (X : V)
    (s : {s : SrcRay p X // r b s.decoration ≠ 0}) :
    ((F p X) s).2.parameter = s.val.2.parameter := by
  simp only [pathDecoratedRayCoefficientEquiv, Equiv.coe_fn_mk,
    AdmissibleRayRealization.parameter_congrVelocity]

/-- The final whole decoration is the image of the original final decoration. -/
@[simp↓] -- Map the whole decoration before expanding its component history.
theorem pathDecoratedRayCoefficientEquiv_decoration (p : Path a b) (X : V)
    (s : {s : SrcRay p X // r b s.decoration ≠ 0}) :
    ((F p X) s).decoration = r b s.val.decoration := by
  rw [PathDecoratedRay.decoration_def, pathDecoratedRayCoefficientEquiv_history,
    Path.Degrees.mapEquiv_apply, PathDecoratedRay.decoration_def]
  exact (p.map_homogeneousHistory_of_injective T ℳ U 𝓝 r (fun q => σ q)
    (fun _ => hr _) hT (fun {_ _} _ => (σ _).injective) s.val.1.val x).symm

/-- Injectivity in the final chamber identifies the unrestricted ray fibers.
No injectivity assumption is needed in the intermediate chambers. -/
def pathDecoratedRayEmbeddingEquiv (hinj : Function.Injective (r b))
    (p : Path a b) (X : V) : SrcRay p X ≃ TgtRay p X :=
  (Equiv.subtypeUnivEquiv (fun s : SrcRay p X =>
    fun hz => s.decoration_ne_zero (hinj (hz.trans (map_zero (r b)).symm)))).symm.trans
      (F p X)

/-- The unrestricted embedding comparison is the surviving-ray comparison on
its automatically surviving input. -/
@[simp]
theorem pathDecoratedRayEmbeddingEquiv_apply (hinj : Function.Injective (r b))
    (p : Path a b) (X : V) (s : SrcRay p X) :
    pathDecoratedRayEmbeddingEquiv T U ℳ 𝓝 r σ hr hT i₀ x v w hv ν ε c P W S C hinj p X s =
      (F p X) ⟨s, fun hz => s.decoration_ne_zero (hinj (hz.trans (map_zero (r b)).symm))⟩ :=
  (rfl)

/-- Coefficient maps commute with the finite evaluation over any itinerary
inventory. Killed whole decorations contribute zero and are then discarded;
no coefficient injectivity or endpoint genericity is assumed. -/
theorem map_pathDecoratedEvaluation (s : Finset (Path a b)) (X : V) :
    r b (pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X) =
      pathDecoratedEvaluation U 𝓝 (σ a i₀) x' s w ν ε c P W S C X := by
  classical
  let : ∀ p : (s : Type _), Fintype (SrcRay p.val X) := fun _ => Fintype.ofFinite _
  let : ∀ p : (s : Type _), Fintype (TgtRay p.val X) := fun _ => Fintype.ofFinite _
  simp only [pathDecoratedEvaluation_def, map_sum]
  -- The evaluation chooses finite enumerations independently of the sigma enumeration.
  rw [Subsingleton.elim (Fintype.ofFinite (Σ p : (s : Type _), SrcRay p.val X))
    (inferInstance : Fintype (Σ p : (s : Type _), SrcRay p.val X)),
    Subsingleton.elim (Fintype.ofFinite (Σ p : (s : Type _), TgtRay p.val X))
      (inferInstance : Fintype (Σ p : (s : Type _), TgtRay p.val X))]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  let A : Type _ := SrcRay p.val X
  let B : Set A := {z | r b z.decoration ≠ 0}
  let : Fintype A := inferInstanceAs (Fintype (SrcRay p.val X))
  let : Fintype B := inferInstanceAs
    (Fintype {z : SrcRay p.val X // r b z.decoration ≠ 0})
  calc
    _ = ∑ z : B, r b z.val.decoration :=
      Finset.sum_congr_set B _ _ (fun _ _ => rfl) (fun _ hz => not_ne_iff.mp hz)
    _ = _ := Fintype.sum_equiv (F p.val X) _ _ fun z =>
      (pathDecoratedRayCoefficientEquiv_decoration T U ℳ 𝓝 r σ hr hT i₀ x v w hv
        ν ε c P W S C p.val X z).symm

end Mei
