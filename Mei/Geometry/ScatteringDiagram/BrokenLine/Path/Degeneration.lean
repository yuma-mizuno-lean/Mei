/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
public import Mei.Geometry.Convex.Sweep.Admissible.Boundary

/-!
# Closed limits of varying-chamber decorated rays

Every complete type of a finite inventory of decorated rays through varying
chamber modules has the backward path family of its encounter path and degree
history. A surviving history preserves normal velocity at every recorded
encounter, so the regularity and boundary theorems for admissible backward
domains apply to each type: regular limits have no collapsed encounters or
unrecorded wall contacts, and a frontier endpoint is terminal, singular, or has
its incoming tail in a tight tangential source face.

For the whole family, compact-open limits of actual rays are exactly the paths of
closed type domains, and over a compact endpoint set these form a compact family.
Any sequence of actual rays with compactly confined endpoints has a subsequence of
one complete type, whose endpoints and paths converge together and whose whole
final decoration is constant. With closed selected supports and a convex
polyhedral source, a regular type limit is realized by an actual ray of the same
type, so sequences whose possible limits are regular converge to actual rays.

No admissibility is asserted for singular limits. The closed-family
interpretation follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)

local notation "dirs" => Path.Degrees.reverseVertexLabels v i₀

/-- A surviving history preserves normal velocity at every recorded encounter,
so its type path satisfies the hypothesis of the regular-limit theorems. -/
theorem normal_succ_eq_of_mem_pathDecoratedHistorySupport {p : Path a b} {d : p.Degrees ι}
    (hd : d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p) (j : Fin p.length) :
    p.reverseArrowLabels ν j (dirs p d j.succ) =
      p.reverseArrowLabels ν j (dirs p d j.castSucc) :=
  (((mem_pathDecoratedHistorySupport T ℳ i₀ x v ν ε p d).mp hd).2 j).1.symm

variable (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)
  (s : Finset (Path a b))

local notation "Labels" => PathDecoratedType T ℳ i₀ x s v ν ε
local notation "D" => fun t : Labels => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t)))
  (dirs (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C
local notation "path" => fun t : Labels => backwardPath
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t)))
  (dirs (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
local notation "Rays(" X ")" => Σ p : (s : Type _),
  PathDecoratedRay T ℳ i₀ x v ν ε c P W S C (Subtype.val p) X

/-- All compact-open limits of the actual rays of a finite inventory are paths of
closed type domains. A limit may pass through singular sets or have collapsed
encounters; distinct types remain indexed separately even when their paths
coincide. -/
theorem closure_range_pathDecoratedRay :
    closure (range fun z : Σ X, Rays(X) => z.2.2.2.ray.toContinuousMap) =
      ⋃ t : Labels, path t '' closure (D t) := by
  have hrange : (range fun z : Σ X, Rays(X) => z.2.2.2.ray.toContinuousMap) =
      ⋃ t : Labels, path t '' D t := by
    ext γ
    constructor
    · rintro ⟨⟨X, p, r⟩, rfl⟩
      exact mem_iUnion.mpr ⟨⟨p, r.1⟩, X, r.2.mem_admissibleBackwardDomain, r.path_eq.symm⟩
    · intro hγ
      obtain ⟨t, X, hX, rfl⟩ := mem_iUnion.mp hγ
      let r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C t.1.val X :=
        ⟨t.2, admissibleRayRealization _ _ _ _ _ _ _ _ hX⟩
      exact ⟨⟨X, t.1, r⟩, PathDecoratedRay.path_eq r⟩
  rw [hrange, closure_iUnion_of_finite]
  simp_rw [closure_image_backwardPath_admissibleBackwardDomain]

/-- Closing every complete type domain gives a compact family of paths over any
compact endpoint set, as a finite union of type-indexed images. -/
theorem isCompact_pathDecoratedRay_closedFamily {B : Set V} (hB : IsCompact B) :
    IsCompact (⋃ t : Labels, path t '' (B ∩ closure (D t))) :=
  isCompact_iUnion fun t => (hB.inter_right isClosed_closure).image (path t).continuous

/-- Any sequence of actual rays with compactly confined endpoints has a
subsequence of one complete type. Endpoints and paths converge together, and the
entire final decoration remains that of the type. -/
theorem PathDecoratedRay.exists_type_tendsto_subseq {B : Set V} (hB : IsCompact B)
    {X : ℕ → V} (hX : ∀ n, X n ∈ B) (r : ∀ n, Rays(X n)) :
    ∃ (t : Labels) (q : V) (φ : ℕ → ℕ),
      q ∈ B ∩ closure (D t) ∧ StrictMono φ ∧
      (∀ n, (⟨(r (φ n)).1, (r (φ n)).2.1⟩ : Labels) = t) ∧
      (∀ n, (r (φ n)).2.decoration = t.1.val.homogeneousHistory T ℳ t.2.val x) ∧
      Tendsto (X ∘ φ) atTop (𝓝 q) ∧
      Tendsto (fun n => (r (φ n)).2.2.ray.toContinuousMap) atTop (𝓝 (path t q)) := by
  let types : ℕ → Labels := fun n => ⟨(r n).1, (r n).2.1⟩
  have hfreq : ∃ᶠ n in atTop, ∃ t, types n = t :=
    (Eventually.of_forall fun n => ⟨types n, rfl⟩).frequently
  obtain ⟨t, ht⟩ := frequently_exists.mp hfreq
  obtain ⟨ψ, hψ, htψ⟩ := extraction_of_frequently_atTop ht
  obtain ⟨q, hqB, η, hη, hq⟩ := hB.tendsto_subseq (fun n => hX (ψ n))
  let φ := ψ ∘ η
  have htφ : ∀ n, types (φ n) = t := fun n => htψ (η n)
  have hdom (n : ℕ) : X (φ n) ∈ D t := by
    have h : X (φ n) ∈ D (types (φ n)) := (r (φ n)).2.2.mem_admissibleBackwardDomain
    rwa [htφ n] at h
  have hq' : Tendsto (X ∘ φ) atTop (𝓝 q) := hq
  refine ⟨t, q, φ, ⟨hqB, isClosed_closure.mem_of_tendsto hq'
    (Eventually.of_forall fun n => subset_closure (hdom n))⟩, hψ.comp hη, htφ,
    fun n => ?_, hq', ?_⟩
  · rw [PathDecoratedRay.decoration_def]
    exact congrArg (fun u : Labels => u.1.val.homogeneousHistory T ℳ u.2.val x) (htφ n)
  · have hp := (path t).continuous.tendsto q |>.comp hq'
    convert hp using 1
    funext n
    exact (r (φ n)).2.path_eq.trans (congrArg (fun u : Labels => path u (X (φ n))) (htφ n))

section Regular

variable {O : Type*} (wall : ∀ {b c : Q}, (b ⟶ c) → J)
  (hPclosed : ∀ {b c : Q} (e : b ⟶ c), IsClosed (P e))
  (hWclosed : ∀ j, IsClosed (W j))
  (hP : ∀ {b c : Q} (e : b ⟶ c), P e ⊆ W (wall e))
  (hheight : ∀ {b b' : Q} (e : b ⟶ b') y, y ∈ W (wall e) → ν e y = c e)
  (μ : J → V →L[ℝ] ℝ) (z : J → ℝ)
  (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {y | μ j y = z j})
  (hC : TauCeti.IsConvexPolyhedron C)

include hPclosed hWclosed hP hheight hspan hC

/-- A regular closed type limit is realized by an actual ray with the same
complete type, whole final decoration and compact-open path. Selected supports
must be closed and the incoming source a convex polyhedron. -/
theorem exists_pathDecoratedRay_of_mem_closure_of_regular_limit (t : Labels)
    {X : V} (hX : X ∈ closure (D t)) (hoff : ∀ j, X ∉ W j)
    (hregular : ∀ s ≤ 0, path t X s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → path t X s ∉ S j) :
    ∃ r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C t.1.val X,
      r.1 = t.2 ∧ r.2.ray.toContinuousMap = path t X := by
  have hheight' (j : Fin t.1.val.length) (y : V)
      (hy : y ∈ W (t.1.val.reverseArrowLabels wall j)) :
      t.1.val.reverseArrowLabels ν j y = t.1.val.reverseArrowLabels c j := by
    have h := Path.reverseArrowLabels_forall₂ ν (fun e => (c e, wall e))
      (fun l q => ∀ y ∈ W q.2, l y = q.1) (fun e => hheight e) t.1.val j
    rw [Path.reverseArrowLabels_map₂ c wall Prod.mk] at h
    exact h y hy
  have hmem := mem_admissibleBackwardDomain_of_regular_limit _ _ _ _ W S C
    (Path.reverseArrowLabels_forall P IsClosed hPclosed t.1.val)
    (t.1.val.reverseArrowLabels wall) hWclosed
    (Path.reverseArrowLabels_forall₂ P wall (fun A j => A ⊆ W j) hP t.1.val) hheight'
    (normal_succ_eq_of_mem_pathDecoratedHistorySupport T ℳ i₀ x v ν ε t.2.property)
    μ z hspan hC hX hoff hregular havoid
  let r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C t.1.val X :=
    ⟨t.2, admissibleRayRealization _ _ _ _ _ _ _ _ hmem⟩
  exact ⟨r, rfl, PathDecoratedRay.path_eq r⟩

/-- If every possible closed type limit over a compact endpoint set is regular,
any sequence of actual rays has a subsequence converging to an actual ray. The
subsequence retains the limit ray's entire type and whole final decoration. -/
theorem PathDecoratedRay.exists_actual_tendsto_subseq_of_regular
    {B : Set V} (hB : IsCompact B) (hoff : ∀ X ∈ B, ∀ j, X ∉ W j)
    (hregular : ∀ (t : Labels) X, X ∈ B ∩ closure (D t) →
      (∀ s ≤ 0, path t X s ∉ singularSupport W) ∧ ∀ j s, s ≤ 0 → path t X s ∉ S j)
    {X : ℕ → V} (hX : ∀ n, X n ∈ B) (r : ∀ n, Rays(X n)) :
    ∃ (q : V) (_ : q ∈ B) (r₀ : Rays(q)) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ n, (⟨(r (φ n)).1, (r (φ n)).2.1⟩ : Labels) = ⟨r₀.1, r₀.2.1⟩) ∧
      (∀ n, (r (φ n)).2.decoration = r₀.2.decoration) ∧
      Tendsto (X ∘ φ) atTop (𝓝 q) ∧
      Tendsto (fun n => (r (φ n)).2.2.ray.toContinuousMap) atTop
        (𝓝 r₀.2.2.ray.toContinuousMap) := by
  obtain ⟨t, q, φ, hq, hφ, ht, hd, hend, hp⟩ :=
    PathDecoratedRay.exists_type_tendsto_subseq T ℳ i₀ x v ν ε c P W S C s hB hX r
  obtain ⟨hr, hs⟩ := hregular t q hq
  obtain ⟨r₀, ht₀, hp₀⟩ := exists_pathDecoratedRay_of_mem_closure_of_regular_limit
    T ℳ i₀ x v ν ε c P W S C s wall hPclosed hWclosed hP hheight μ z hspan hC t hq.2
    (hoff q hq.1) hr hs
  have hlabel : (⟨t.1, r₀.1⟩ : Labels) = t := Sigma.ext rfl (heq_of_eq ht₀)
  refine ⟨q, hq.1, ⟨t.1, r₀⟩, φ, hφ, fun n => (ht n).trans hlabel.symm, fun n => ?_, hend,
    ?_⟩
  · rw [hd n, PathDecoratedRay.decoration_def, ht₀]
  · rwa [hp₀]

end Regular

end Mei
