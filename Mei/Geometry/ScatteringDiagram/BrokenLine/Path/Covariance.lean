/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
public import Mei.Geometry.Convex.Sweep.Admissible.Affine

/-!
# Affine covariance of rays through varying chamber modules

Changing developed affine coordinates identifies actual decorated rays through
independently graded chamber modules. The comparison retains the entire encounter
path, degree history and whole terminal decoration. It maps the full geometric
path, including its original incoming tail, and preserves all encounter times.
Finite weighted evaluations are therefore invariant under this coordinate change.
Complete type domains have affine images and homeomorphic closures; their continuous
path extensions transform even at collapsed, terminal and singular limits. This
lets closed endpoint charts retain their global histories under coordinate changes,
without asserting that a boundary path is admissible.

Selected supports, unrecorded walls, singular obstacles and the incoming source
move together. Normals transform by the inverse linear map and offsets include
the translation. No endpoint genericity, coefficient basis, common chamber module
or finite degree set is needed; repeated and unchanged-direction encounters remain.

The construction combines `Quiver.Path.homogeneousHistory` with
`Mei.Convex.admissibleRayAffineEquiv`. The geometric interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2), and whole-component propagation follows Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3
(arXiv:1601.07081v4).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {Q R V V' J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (e : V ≃ᴬ[ℝ] V')

local notation "u" => fun q d => e.toAffineEquiv.linear (v q d)
local notation "μ" => fun {b c : Q} (l : b ⟶ c) =>
  ContinuousLinearMap.comp (ν l) e.symm.toContinuousAffineMap.contLinear

/-- Affine coordinate changes preserve exactly the surviving component histories
and their signed normal-velocity conditions through every chamber. -/
@[simp]
theorem pathDecoratedHistorySupport_affine (p : Path a b) :
    pathDecoratedHistorySupport T ℳ i₀ x u μ ε p =
      pathDecoratedHistorySupport T ℳ i₀ x v ν ε p := by
  classical
  have hν := p.reverseArrowLabels_comp ν
    (fun l => ContinuousLinearMap.comp l e.symm.toContinuousAffineMap.contLinear)
  ext d
  simp only [mem_pathDecoratedHistorySupport, hν,
    Path.Degrees.reverseVertexLabels_comp, Function.comp_apply,
    ContinuousLinearMap.comp_symm_contLinear_linear]

variable (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "c'" => fun {b c₁ : Q} (l : b ⟶ c₁) => c l - ν l (e.symm 0)
local notation "P'" => fun {b c : Q} (l : b ⟶ c) => e '' P l
local notation "W'" => fun j => e '' W j
local notation "S'" => fun j => e '' S j
local notation "Source" p:max X:max => PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X
local notation "Target" p:max X:max => PathDecoratedRay T ℳ i₀ x u μ ε c' P' W' S' (e '' C) p (e X)

/-- Affine coordinate changes identify the actual varying-chamber ray fibers.
All encounter and obstacle constraints, and the global incoming source, move
with the coordinates. -/
def pathDecoratedRayAffineEquiv (p : Path a b) (X : V) : Source p X ≃ Target p X := by
  have hν := p.reverseArrowLabels_comp ν
    (fun l => ContinuousLinearMap.comp l e.symm.toContinuousAffineMap.contLinear)
  have hc := p.reverseArrowLabels_map₂ c ν (fun z l => z - l (e.symm 0))
  have hP := p.reverseArrowLabels_comp P (fun A => e '' A)
  have hv (d : p.Degrees ι) := Path.Degrees.reverseVertexLabels_comp v
    (fun z => e.toAffineEquiv.linear z) i₀ p d
  let E (d : p.Degrees ι) := admissibleRayAffineEquiv
    (p.reverseArrowLabels ν) (p.reverseArrowLabels c)
    (Path.Degrees.reverseVertexLabels v i₀ p d) (p.reverseArrowLabels P) W S C e X
  refine {
    toFun := fun r => ⟨⟨r.1.val, by
      rw [pathDecoratedHistorySupport_affine]; exact r.1.property⟩,
      (E r.1.val r.2).congrData hν.symm hc.symm (hv r.1.val).symm hP.symm⟩
    invFun := fun r => ⟨⟨r.1.val, by
      rw [← pathDecoratedHistorySupport_affine T ℳ i₀ x v ν ε e p]; exact r.1.property⟩,
      (E r.1.val).symm (r.2.congrData hν hc (hv r.1.val) hP)⟩
    left_inv := fun r => PathDecoratedRay.ext_history _ r rfl
    right_inv := fun r => PathDecoratedRay.ext_history _ r rfl }

/-- The entire degree history is retained by the forward comparison. -/
@[simp]
theorem pathDecoratedRayAffineEquiv_history (p : Path a b) (X : V) (r : Source p X) :
    (pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p X r).1.val = r.1.val := (rfl)

/-- Inverse coordinate transport retains the entire degree history. -/
@[simp]
theorem pathDecoratedRayAffineEquiv_symm_history (p : Path a b) (X : V) (r : Target p X) :
    ((pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p X).symm r).1.val =
      r.1.val := (rfl)

/-- The whole terminal component in the final chamber module is unchanged. -/
@[simp↓]
theorem pathDecoratedRayAffineEquiv_decoration (p : Path a b) (X : V) (r : Source p X) :
    (pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p X r).decoration =
      r.decoration := by
  simp only [PathDecoratedRay.decoration_def, pathDecoratedRayAffineEquiv_history]

/-- Inverse transport preserves the whole terminal component as well. -/
@[simp↓]
theorem pathDecoratedRayAffineEquiv_symm_decoration (p : Path a b) (X : V) (r : Target p X) :
    ((pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p X).symm r).decoration =
      r.decoration := by
  simp only [PathDecoratedRay.decoration_def, pathDecoratedRayAffineEquiv_symm_history]

/-- Forward transport maps the full path and its incoming tail by the affine map. -/
@[simp]
theorem pathDecoratedRayAffineEquiv_ray (p : Path a b) (X : V) (r : Source p X) :
    (pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p X r).2.ray =
      r.2.ray.map e.toAffineEquiv.toAffineMap := by
  simp only [pathDecoratedRayAffineEquiv, Equiv.coe_fn_mk,
    AdmissibleRayRealization.ray_congrData, admissibleRayAffineEquiv_ray]

/-- Every recorded encounter keeps its original parameter. -/
@[simp]
theorem pathDecoratedRayAffineEquiv_parameter (p : Path a b) (X : V) (r : Source p X) :
    (pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p X r).2.parameter =
      r.2.parameter := by
  simp only [pathDecoratedRayAffineEquiv, Equiv.coe_fn_mk,
    AdmissibleRayRealization.parameter_congrData, admissibleRayAffineEquiv_parameter]

/-- Inverse transport maps the entire path by the inverse affine map. -/
@[simp]
theorem pathDecoratedRayAffineEquiv_symm_ray (p : Path a b) (X : V) (r : Target p X) :
    ((pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p X).symm r).2.ray =
      r.2.ray.map e.symm.toAffineEquiv.toAffineMap := by
  simp only [pathDecoratedRayAffineEquiv, Equiv.symm_mk, Equiv.coe_fn_mk,
    admissibleRayAffineEquiv_symm_ray, AdmissibleRayRealization.ray_congrData]

/-- Inverse transport also retains every encounter parameter. -/
@[simp]
theorem pathDecoratedRayAffineEquiv_symm_parameter (p : Path a b) (X : V) (r : Target p X) :
    ((pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p X).symm r).2.parameter =
      r.2.parameter := by
  simp only [pathDecoratedRayAffineEquiv, Equiv.symm_mk, Equiv.coe_fn_mk,
    admissibleRayAffineEquiv_symm_parameter, AdmissibleRayRealization.parameter_congrData]

/-- Finite weighted evaluation through varying chambers is unchanged by affine
coordinates. Multiplicities and the whole global incoming histories are retained. -/
@[simp]
theorem pathDecoratedEvaluation_affine (s : Finset (Path a b)) (X : V) :
    pathDecoratedEvaluation T ℳ i₀ x s u μ ε c' P' W' S' (e '' C) (e X) =
      pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X := by
  classical
  let E := Equiv.sigmaCongrRight fun p : (s : Type _) =>
    pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p.val X
  let := Fintype.ofFinite (Σ p : (s : Type _), Source p.val X)
  let := Fintype.ofFinite (Σ p : (s : Type _), Target p.val X)
  simp only [pathDecoratedEvaluation_def]
  exact (Fintype.sum_equiv E _ _ (fun r =>
    (pathDecoratedRayAffineEquiv_decoration T ℳ i₀ x v ν ε e c P W S C r.1.val X r.2).symm)).symm

section TypeTransport

variable (s : Finset (Path a b))

local notation "Types" => PathDecoratedType T ℳ i₀ x s v ν ε
local notation "Types'" => PathDecoratedType T ℳ i₀ x s u μ ε

/-- Affine transport of complete path and degree-history labels for a finite
inventory. No label is removed, even when its endpoint domain is empty. -/
def pathDecoratedTypeAffineEquiv : Types ≃ Types' :=
  Equiv.sigmaCongrRight fun p =>
    Equiv.subtypeEquivRight fun d => by rw [pathDecoratedHistorySupport_affine]

local notation "E" => pathDecoratedTypeAffineEquiv T ℳ i₀ x v ν ε e s

/-- Every encounter path, including repeated arrows, is retained. -/
@[simp]
theorem pathDecoratedTypeAffineEquiv_itinerary (t : Types) : (E t).1 = t.1 := (rfl)

/-- Every intermediate chamber degree is retained. -/
@[simp]
theorem pathDecoratedTypeAffineEquiv_history (t : Types) : HEq (E t).2.val t.2.val := (HEq.rfl)

/-- The inverse comparison retains the encounter path. -/
@[simp]
theorem pathDecoratedTypeAffineEquiv_symm_itinerary (t : Types') :
    ((E).symm t).1 = t.1 := (rfl)

/-- The inverse comparison retains the complete degree history. -/
@[simp]
theorem pathDecoratedTypeAffineEquiv_symm_history (t : Types') :
    HEq ((E).symm t).2.val t.2.val := (HEq.rfl)

local notation "dirs(" t ")" => Path.Degrees.reverseVertexLabels v i₀ (Subtype.val (Sigma.fst t))
  (Subtype.val (Sigma.snd t))
local notation "dirs'(" t ")" => Path.Degrees.reverseVertexLabels u i₀ (Subtype.val (Sigma.fst t))
  (Subtype.val (Sigma.snd t))
local notation "D(" t ")" => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs(t))
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C
local notation "D'(" t ")" => admissibleBackwardDomain
  (Path.reverseArrowLabels μ (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c' (Subtype.val (Sigma.fst t))) (dirs'(t))
  (Path.reverseArrowLabels P' (Subtype.val (Sigma.fst t))) W' S' (e '' C)
local notation "β(" t ")" => backwardPath (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs(t))
local notation "β'(" t ")" => backwardPath (Path.reverseArrowLabels μ (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c' (Subtype.val (Sigma.fst t))) (dirs'(t))

/-- A complete type is admitted at exactly the transported endpoints. This
compares all avoidance and incoming-source constraints of the actual rays. -/
@[simp↓]
theorem mem_pathDecoratedTypeAffineEquiv_domain (t : Types) (X : V) :
    e X ∈ D'(E t) ↔ X ∈ D(t) := by
  have hν := t.1.val.reverseArrowLabels_comp ν
    (fun l => ContinuousLinearMap.comp l e.symm.toContinuousAffineMap.contLinear)
  have hc := t.1.val.reverseArrowLabels_map₂ c ν (fun z l => z - l (e.symm 0))
  have hP := t.1.val.reverseArrowLabels_comp P (fun A => e '' A)
  have hi := pathDecoratedTypeAffineEquiv_itinerary T ℳ i₀ x v ν ε e s t
  have hh := pathDecoratedTypeAffineEquiv_history T ℳ i₀ x v ν ε e s t
  -- Identify the dependent encounter path before rewriting its degree history.
  generalize ht : E t = t' at hi hh ⊢
  obtain ⟨p', d'⟩ := t'
  dsimp at hi hh
  cases hi
  rw [eq_of_heq hh]
  simp only [hν, hc, hP, Path.Degrees.reverseVertexLabels_comp, Function.comp_def]
  rw [← nonempty_admissibleRayRealization_iff, ← nonempty_admissibleRayRealization_iff]
  exact (admissibleRayAffineEquiv (t.1.val.reverseArrowLabels ν)
    (t.1.val.reverseArrowLabels c) (dirs(t))
    (t.1.val.reverseArrowLabels P) W S C e X).nonempty_congr.symm

/-- The full endpoint domain of a transported complete type is its affine image. -/
theorem pathDecoratedTypeAffineEquiv_domain (t : Types) : D'(E t) = e '' D(t) := by
  ext Y
  obtain ⟨X, rfl⟩ := e.surjective Y
  simp only [mem_pathDecoratedTypeAffineEquiv_domain, e.injective.mem_set_image]

/-- All closed degenerations of the original domain are transported, including
collapsed, terminal and singular encounters. No boundary admissibility is asserted. -/
theorem pathDecoratedTypeAffineEquiv_closure_domain (t : Types) :
    closure (D'(E t)) = e '' closure (D(t)) := by
  rw [pathDecoratedTypeAffineEquiv_domain]
  exact (e.toHomeomorph.image_closure _).symm

/-- Affine covariance of the continuous whole-path extensions at every endpoint,
including points outside the actual admission domain and its boundary. -/
@[simp↓]
theorem pathDecoratedTypeAffineEquiv_path (t : Types) (X : V) (r : ℝ) :
    β'(E t) (e X) r = e (β(t) X r) := by
  have hν := t.1.val.reverseArrowLabels_comp ν
    (fun l => ContinuousLinearMap.comp l e.symm.toContinuousAffineMap.contLinear)
  have hc := t.1.val.reverseArrowLabels_map₂ c ν (fun z l => z - l (e.symm 0))
  have hi := pathDecoratedTypeAffineEquiv_itinerary T ℳ i₀ x v ν ε e s t
  have hh := pathDecoratedTypeAffineEquiv_history T ℳ i₀ x v ν ε e s t
  -- Identify the dependent encounter path before rewriting its degree history.
  generalize ht : E t = t' at hi hh ⊢
  obtain ⟨p', d'⟩ := t'
  dsimp at hi hh
  cases hi
  rw [eq_of_heq hh]
  simp only [hν, hc, Path.Degrees.reverseVertexLabels_comp, Function.comp_def]
  exact backwardPath_affine _ _ _ e X r

/-- The type comparison agrees with affine transport of actual fibers, so chart
labels and the geometric whole histories describe the same coordinate change. -/
@[simp↓]
theorem pathDecoratedRayAffineEquiv_type (p : (s : Type _)) (X : V) (r : Source p.val X) :
    (⟨p, (pathDecoratedRayAffineEquiv T ℳ i₀ x v ν ε e c P W S C p.val X r).1⟩ : Types') =
      E ⟨p, r.1⟩ := (rfl)

/-- The closed endpoint domains are homeomorphic under the original affine
coordinate map. Thus the comparison also preserves compact endpoint sets. -/
def pathDecoratedTypeClosedDomainHomeomorph (t : Types) :
    closure (D(t)) ≃ₜ closure (D'(E t)) :=
  e.toHomeomorph.subtype fun X => by
    rw [pathDecoratedTypeAffineEquiv_closure_domain]
    exact e.injective.mem_set_image.symm

/-- The closed-domain comparison uses the same endpoint coordinate map. -/
@[simp]
theorem pathDecoratedTypeClosedDomainHomeomorph_apply (t : Types) (X : closure (D(t))) :
    (pathDecoratedTypeClosedDomainHomeomorph T ℳ i₀ x v ν ε e c P W S C s t X).val =
      e X.val := (rfl)

/-- The inverse closed-domain comparison uses the inverse endpoint map. -/
@[simp]
theorem pathDecoratedTypeClosedDomainHomeomorph_symm_apply (t : Types)
    (X : closure (D'(E t))) :
    ((pathDecoratedTypeClosedDomainHomeomorph T ℳ i₀ x v ν ε e c P W S C s t).symm X).val =
      e.symm X.val := (rfl)

end TypeTransport

end Mei
