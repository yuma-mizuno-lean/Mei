/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
public import Mei.Geometry.Convex.Sweep.Admissible.Itinerary
public import Mei.Geometry.Convex.Sweep.Admissible.Terminal
public import Mei.Geometry.Convex.Sweep.Admissible.Straight
public import Mei.Geometry.Convex.Sweep.Admissible.WallEvent
public import Mei.Algebra.Lie.Graded.Shifted.Support

/-!
# Leading coefficients of path ray sums

Suppose every arrow raises degrees in a positive degree monoid: a nonzero component of
degree `m` of the image of a homogeneous element of degree `n` has `m - n` positive. Then
along a surviving whole history the terminal degree exceeds the incoming degree, and a
history whose terminal degree equals its incoming degree keeps that degree at every vertex.
If the arrows also fix the incoming component, such a leading history carries its whole
input unchanged.

For decorated rays along the paths of a one-object quiver, a leading ray follows the
incoming straight half-line through its endpoint. When at every point of that half-line at
most one label with the prescribed crossing sign is incident, there is at most one leading
ray over all paths, so the incoming component of the weighted evaluation is the input when
a leading ray exists and zero otherwise. Encounters that preserve degree remain recorded.

For canonical signed simultaneous wall events, an admissible incoming straight realization
supplies the leading ray. Off one exceptional arrangement depending only on the wall
geometry and the incoming direction, the incoming component of the weighted evaluation is
the input, for every diagonal-preserving degree-raising propagation and every finite
inventory exhausting the endpoint fiber. Finite shifted BCH actions satisfy both
conditions. This supplies the initial coefficient in the last-change recursion of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

section Degrees

variable {Q R Γ : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, Γ → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  (hshift : ∀ {b c : Q} (e : b ⟶ c) (n m : Γ) (y : M b), y ∈ ℳ b n →
    (DirectSum.decompose (ℳ c) (T e y) m : M c) ≠ 0 → m - n ∈ d.monoid)
  {a : Q} (i₀ : Γ) (x : M a) (hx : x ∈ ℳ a i₀)

include hshift hx

/-- When every arrow raises degrees, the terminal degree of a surviving whole history
exceeds its incoming degree by a positive degree. -/
theorem terminalDegree_sub_mem_of_homogeneousHistory_ne_zero :
    ∀ {b : Q} (p : Path a b) (dd : p.Degrees fun _ => Γ),
      p.homogeneousHistory T ℳ dd x ≠ 0 → Path.Degrees.terminalDegree i₀ p dd - i₀ ∈ d.monoid
  | _, .nil, _, _ => by
    rw [Path.Degrees.terminalDegree_nil, sub_self]
    exact d.monoid.zero_mem
  | _, .cons p e, di, h => by
    obtain ⟨dd, i⟩ := di
    have ih := terminalDegree_sub_mem_of_homogeneousHistory_ne_zero p dd
      (p.homogeneousHistory_ne_zero_of_cons T ℳ e dd i h)
    rw [Path.homogeneousHistory_cons_apply] at h
    have hstep := hshift e _ i _ (p.homogeneousHistory_mem_vertex dd i₀ x hx) h
    rw [Path.Degrees.terminalDegree_cons]
    simpa only [sub_add_sub_cancel] using d.monoid.add_mem hstep ih

/-- When every arrow raises degrees, a surviving whole history ending in its incoming
degree keeps that degree at every vertex. -/
theorem eq_degreesOfVertices_of_terminalDegree_eq :
    ∀ {b : Q} (p : Path a b) (dd : p.Degrees fun _ => Γ),
      p.homogeneousHistory T ℳ dd x ≠ 0 → Path.Degrees.terminalDegree i₀ p dd = i₀ →
        dd = p.degreesOfVertices fun _ => i₀
  | _, .nil, _, _, _ => by rw [Path.degreesOfVertices_nil]
  | _, .cons p e, di, h, hi => by
    obtain ⟨dd, i⟩ := di
    rw [Path.Degrees.terminalDegree_cons] at hi
    rw [hi] at h
    have hp := p.homogeneousHistory_ne_zero_of_cons T ℳ e dd i₀ h
    have hle := terminalDegree_sub_mem_of_homogeneousHistory_ne_zero d T ℳ hshift i₀ x hx p dd hp
    rw [Path.homogeneousHistory_cons_apply] at h
    have hge := hshift e _ i₀ _ (p.homogeneousHistory_mem_vertex dd i₀ x hx) h
    have heq : Path.Degrees.terminalDegree i₀ p dd = i₀ :=
      sub_eq_zero.mp (d.eq_zero_of_mem_of_neg_mem hle (by rwa [neg_sub]))
    rw [Path.degreesOfVertices_cons, hi,
      eq_degreesOfVertices_of_terminalDegree_eq p dd hp heq]

end Degrees

section Constant

variable {Q R M Γ A : Type*} [Quiver Q] [Semiring R] [AddCommMonoid M] [Module R M]
  (T : ∀ {b c : Q}, (b ⟶ c) → M →ₗ[R] M)
  (ℳ : Γ → Submodule R M) {a : Q} (i₀ : Γ)

/-- The constant degree history ends in its degree. -/
@[simp]
theorem terminalDegree_degreesOfVertices_const :
    ∀ {b : Q} (p : Path a b),
      Path.Degrees.terminalDegree i₀ p (p.degreesOfVertices fun _ => i₀) = i₀
  | _, .nil => by rw [Path.degreesOfVertices_nil, Path.Degrees.terminalDegree_nil]
  | _, .cons p e => by rw [Path.degreesOfVertices_cons, Path.Degrees.terminalDegree_cons]

/-- The constant degree history labels every vertex by the same value. -/
@[simp]
theorem reverseVertexLabels_degreesOfVertices_const (w : Γ → A) :
    ∀ {b : Q} (p : Path a b),
      Path.Degrees.reverseVertexLabels (fun _ => w) i₀ p (p.degreesOfVertices fun _ => i₀) =
        fun _ => w i₀
  | _, .nil => by rw [Path.degreesOfVertices_nil, Path.Degrees.reverseVertexLabels_nil]
  | _, .cons p e => by
    rw [Path.degreesOfVertices_cons, Path.Degrees.reverseVertexLabels_cons,
      reverseVertexLabels_degreesOfVertices_const w p]
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

/-- If every arrow fixes the component of degree `i₀`, the constant history of
degree `i₀` carries a homogeneous input of that degree unchanged. -/
theorem homogeneousHistory_degreesOfVertices_of_decompose_self [DecidableEq Γ]
    [DirectSum.Decomposition ℳ] (hT : ∀ {b c : Q} (e : b ⟶ c) (y : M), y ∈ ℳ i₀ →
      (DirectSum.decompose ℳ (T e y) i₀ : M) = y) {x : M} (hx : x ∈ ℳ i₀) :
    ∀ {b : Q} (p : Path a b),
      p.homogeneousHistory (M := fun _ => M) T (fun _ => ℳ)
        (p.degreesOfVertices fun _ => i₀) x = x
  | _, .nil => by rw [Path.homogeneousHistory_nil, LinearMap.id_apply]
  | _, .cons p e => by
    rw [Path.degreesOfVertices_cons, Path.homogeneousHistory_cons_apply,
      homogeneousHistory_degreesOfVertices_of_decompose_self hT hx p]
    exact hT e x hx

end Constant

/-- The word of a one-object path lists its backward arrow labels. -/
theorem _root_.Quiver.SingleObj.pathToList_eq_ofFn_reverseArrowLabels {α : Type*} :
    ∀ {x : SingleObj α} (p : Path (SingleObj.star α) x),
      SingleObj.pathToList p = List.ofFn (p.reverseArrowLabels fun e => (e : α))
  | _, .nil => by rw [Path.reverseArrowLabels_nil]; rfl
  | _, .cons p e => by
    rw [SingleObj.pathToList, Quiver.SingleObj.pathToList_eq_ofFn_reverseArrowLabels p]
    refine Eq.trans ?_
      (List.ofFn_succ (n := p.length) (f := (p.cons e).reverseArrowLabels fun e => e)).symm
    have h0 : (p.cons e).reverseArrowLabels (fun e => (e : α)) (0 : Fin (p.length + 1)) = e :=
      (congrFun (Path.reverseArrowLabels_cons (fun e => (e : α)) p e)
        (0 : Fin (p.length + 1))).trans (Fin.cons_zero ..)
    have hs (j : Fin p.length) :
        (p.cons e).reverseArrowLabels (fun e => (e : α)) j.succ =
          p.reverseArrowLabels (fun e => (e : α)) j :=
      (congrFun (Path.reverseArrowLabels_cons (fun e => (e : α)) p e) j.succ).trans
        (Fin.cons_succ ..)
    rw [h0]
    simp only [hs]

section SingleObj

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P : J → Set V} {W : I → Set V} {S : K → Set V} {C : Set V} {Q : V}

local notation "PRay" p:max => PathDecoratedRay (Q := SingleObj J) (M := fun _ => M)
  (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
  (fun e => ε e) (fun e => c e) (fun e => P e) W S C p Q
local notation "Paths" => Path (SingleObj.star J) (SingleObj.star J)

namespace PathDecoratedRay

variable (hshift : ∀ j n m (y : M), y ∈ ℳ n →
  (DirectSum.decompose ℳ (T j y) m : M) ≠ 0 → m - n ∈ d.monoid)

include hshift

/-- A leading ray keeps degree zero at every vertex. -/
theorem history_eq_of_terminalDegree_eq_zero {p : Paths} (r : PRay p)
    (hr : Path.Degrees.terminalDegree (0 : Γ) p r.1.val = 0) :
    r.1.val = p.degreesOfVertices fun _ => (0 : Γ) :=
  eq_degreesOfVertices_of_terminalDegree_eq d (fun e => T e) (fun _ => ℳ)
    (fun e => hshift e) 0 (a : M) a.property p r.1.val
    ((mem_pathDecoratedHistorySupport ..).mp r.1.property).1 hr

/-- Every segment of a leading ray has the incoming direction. -/
theorem directions_eq_of_terminalDegree_eq_zero {p : Paths} (r : PRay p)
    (hr : Path.Degrees.terminalDegree (0 : Γ) p r.1.val = 0) :
    Path.Degrees.reverseVertexLabels (fun _ => v) 0 p r.1.val = fun _ => v 0 := by
  rw [r.history_eq_of_terminalDegree_eq_zero hshift hr,
    reverseVertexLabels_degreesOfVertices_const]

/-- A leading ray carries its whole input when every label fixes the incoming
component. -/
theorem decoration_eq_of_terminalDegree_eq_zero
    (hT : ∀ j y, y ∈ ℳ 0 → (DirectSum.decompose ℳ (T j y) 0 : M) = y)
    {p : Paths} (r : PRay p) (hr : Path.Degrees.terminalDegree (0 : Γ) p r.1.val = 0) :
    r.decoration = (a : M) := by
  rw [decoration_def, r.history_eq_of_terminalDegree_eq_zero hshift hr]
  exact homogeneousHistory_degreesOfVertices_of_decompose_self (fun e => T e) ℳ 0
    (fun e => hT e) a.property p

/-- A leading ray follows the incoming straight half-line through the endpoint.
Recorded encounters that preserve degree remain present. -/
theorem ray_eq_of_terminalDegree_eq_zero {p : Paths} (r : PRay p)
    (hr : Path.Degrees.terminalDegree (0 : Γ) p r.1.val = 0) {t : ℝ} (ht : t ≤ 0) :
    r.2.ray t = Q - t • v 0 := by
  have hdirs := r.directions_eq_of_terminalDegree_eq_zero hshift hr
  have h := r.2.ray_eq_endpoint_sub_smul_of_directions_eq
    (fun i => by simp only [hdirs]) ht
  simpa only [hdirs] using h

/-- Leading rays are unique across all paths. Every recorded support must lie on an
obstacle, and at a point on the incoming straight path, at most one incident label has
the prescribed crossing sign. Neither existence nor a nonzero incoming direction is
assumed. -/
theorem eq_of_terminalDegree_eq_zero {p p' : Paths} (r : PRay p) (r' : PRay p')
    (hr : Path.Degrees.terminalDegree (0 : Γ) p r.1.val = 0)
    (hr' : Path.Degrees.terminalDegree (0 : Γ) p' r'.1.val = 0)
    (hP : ∀ j, P j ⊆ ⋃ b, W b)
    (hsep : ∀ t < (0 : ℝ), ∀ j l,
      Q - t • v 0 ∈ P j → Q - t • v 0 ∈ P l →
      SignType.sign (f j (v 0)) = ε j →
      SignType.sign (f l (v 0)) = ε l → j = l) :
    (⟨p, r⟩ : Σ p : Paths, PRay p) = ⟨p', r'⟩ := by
  have hlab (q : Paths) : q.reverseArrowLabels (fun e => P e) =
      P ∘ q.reverseArrowLabels fun e => (e : J) :=
    Path.reverseArrowLabels_comp (fun e => (e : J)) P q
  have hparam := r.2.encounterParameters_eq_of_ray_eq r'.2
    (fun t ht => (r.ray_eq_of_terminalDegree_eq_zero hshift hr ht).trans
      (r'.ray_eq_of_terminalDegree_eq_zero hshift hr' ht).symm)
    (fun j => by rw [hlab]; exact hP _) (fun j => by rw [hlab]; exact hP _)
  -- The leading rays meet the same labels at the same encounters.
  have hsign {q : Paths} (s : PRay q) (hs : Path.Degrees.terminalDegree (0 : Γ) q s.1.val = 0)
      (j : Fin q.length) :
      SignType.sign (f (q.reverseArrowLabels (fun e => (e : J)) j) (v 0)) =
        ε (q.reverseArrowLabels (fun e => (e : J)) j) := by
    have hn := (((mem_pathDecoratedHistorySupport ..).mp s.1.property).2 j).2
    rw [s.directions_eq_of_terminalDegree_eq_zero hshift hs] at hn
    simpa only [Path.reverseArrowLabels_comp (fun e => (e : J)) f q,
      Path.reverseArrowLabels_comp (fun e => (e : J)) ε q, Function.comp_apply] using hn
  have hinc {q : Paths} (s : PRay q) (hs : Path.Degrees.terminalDegree (0 : Γ) q s.1.val = 0)
      (j : Fin q.length) (hneg : s.2.parameter j.succ < 0) :
      Q - s.2.parameter j.succ • v 0 ∈ P (q.reverseArrowLabels (fun e => (e : J)) j) := by
    have h : Q - s.2.parameter j.succ • v 0 ∈ q.reverseArrowLabels (fun e => P e) j := by
      rw [← s.ray_eq_of_terminalDegree_eq_zero hshift hs hneg.le]
      exact s.2.incidence j
    rwa [congrFun (hlab q) j] at h
  have hneg {q : Paths} (s : PRay q) (j : Fin q.length) : s.2.parameter j.succ < 0 := by
    simpa only [s.2.parameter_zero] using s.2.strictAnti_parameter (Fin.succ_pos j)
  have hl : p.length = p'.length := by
    simpa only [List.length_ofFn] using congrArg List.length hparam
  have hword : SingleObj.pathToList p = SingleObj.pathToList p' := by
    rw [SingleObj.pathToList_eq_ofFn_reverseArrowLabels,
      SingleObj.pathToList_eq_ofFn_reverseArrowLabels]
    apply List.ext_get (by simpa only [List.length_ofFn] using hl)
    intro i hi hi'
    let j : Fin p.length := ⟨i, by simpa only [List.length_ofFn] using hi⟩
    let l : Fin p'.length := ⟨i, by simpa only [List.length_ofFn] using hi'⟩
    have ht : r.2.parameter j.succ = r'.2.parameter l.succ := by
      have he := congrArg (fun ts : List ℝ => ts[i]?) hparam
      have hj : i < p.length := j.isLt
      have hl' : i < p'.length := l.isLt
      simpa [j, l, hj, hl'] using he
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    refine hsep _ (hneg r j) _ _ (hinc r hr j (hneg r j)) ?_ (hsign r hr j) (hsign r' hr' l)
    rw [ht]
    exact hinc r' hr' l (hneg r' l)
  have hp : p = p' := SingleObj.pathEquivList.injective hword
  subst hp
  have hh : r.1 = r'.1 := Subtype.ext ((r.history_eq_of_terminalDegree_eq_zero hshift hr).trans
    (r'.history_eq_of_terminalDegree_eq_zero hshift hr').symm)
  obtain ⟨h, g⟩ := r
  obtain ⟨h', g'⟩ := r'
  dsimp only at hh
  subst hh
  rw [Subsingleton.elim g g']

end PathDecoratedRay

variable (T a f c ε P W S C) in
/-- An admissible incoming straight realization along a word with the prescribed
crossing signs is a leading ray along the path of that word, for a nonzero input fixed by
every label in degree zero. -/
theorem exists_pathDecoratedRay_of_straight {n : ℕ} (g : Fin n → J)
    (r : AdmissibleRayRealization (fun j => f (g j)) (fun j => c (g j)) (fun _ => v 0)
      (fun j => P (g j)) W S C Q)
    (hε : ∀ j, SignType.sign (f (g j) (v 0)) = ε (g j))
    (hT : ∀ j y, y ∈ ℳ 0 → (DirectSum.decompose ℳ (T j y) 0 : M) = y)
    (ha : (a : M) ≠ 0) :
    ∃ r' : PRay (SingleObj.pathOfFn g),
      Path.Degrees.terminalDegree (0 : Γ) (SingleObj.pathOfFn g) r'.1.val = 0 := by
  let p := SingleObj.pathOfFn g
  have hlen := SingleObj.length_pathOfFn g
  have hdirs := reverseVertexLabels_degreesOfVertices_const (Q := SingleObj J) (0 : Γ) v p
  have hmem : (p.degreesOfVertices fun _ => (0 : Γ)) ∈ pathDecoratedHistorySupport
      (Q := SingleObj J) (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a
      (fun _ => v) (fun e => f e) (fun e => ε e) p := by
    refine (mem_pathDecoratedHistorySupport ..).mpr ⟨?_, fun j => ?_⟩
    · rwa [homogeneousHistory_degreesOfVertices_of_decompose_self (fun e => T e) ℳ 0
        (fun e => hT e) a.property p]
    · rw [hdirs]
      refine ⟨rfl, ?_⟩
      obtain ⟨j, rfl⟩ := (Fin.castOrderIso hlen.symm).surjective j
      simp only [Fin.castOrderIso_apply]
      rw [SingleObj.reverseArrowLabels_pathOfFn, SingleObj.reverseArrowLabels_pathOfFn,
        Fin.cast_cast, Fin.cast_eq_self]
      exact hε j
  refine ⟨⟨⟨_, hmem⟩, r.congrLength hlen.symm _ _ _ _
    (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn, Fin.cast_cast, Fin.cast_eq_self])
    (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn, Fin.cast_cast, Fin.cast_eq_self])
    (fun j => by rw [hdirs])
    (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn, Fin.cast_cast, Fin.cast_eq_self])⟩,
    ?_⟩
  exact terminalDegree_degreesOfVertices_const (0 : Γ) p

variable (hT : ∀ j y, y ∈ ℳ 0 → (DirectSum.decompose ℳ (T j y) 0 : M) = y)
  (hshift : ∀ j n m (y : M), y ∈ ℳ n →
    (DirectSum.decompose ℳ (T j y) m : M) ≠ 0 → m - n ∈ d.monoid)
  (hP : ∀ j, P j ⊆ ⋃ b, W b)
  (hsep : ∀ t < (0 : ℝ), ∀ j l,
    Q - t • v 0 ∈ P j → Q - t • v 0 ∈ P l →
    SignType.sign (f j (v 0)) = ε j →
    SignType.sign (f l (v 0)) = ε l → j = l)
  (s : Finset (Path (SingleObj.star J) (SingleObj.star J)))

local notation "evaluation" => pathDecoratedEvaluation (Q := SingleObj J) (M := fun _ => M)
  (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v) (fun e => f e)
  (fun e => ε e) (fun e => c e) (fun e => P e) W S C Q

include hT hshift hP hsep

open Classical in
/-- The incoming component of the weighted evaluation is the input if a leading ray
exists along a path of the inventory, and zero otherwise. Signed separation prevents
overcounting across different paths. Source admission and all avoidance conditions
remain part of the existence test. -/
theorem decompose_pathDecoratedEvaluation_zero_eq_ite :
    (DirectSum.decompose ℳ evaluation 0 : M) =
      if ∃ (p : (s : Type _)) (r : PRay p.val),
        Path.Degrees.terminalDegree (0 : Γ) p.val r.1.val = 0 then (a : M) else 0 := by
  classical
  let := Fintype.ofFinite (Σ p : (s : Type _), PRay p.val)
  let leading (z : Σ p : (s : Type _), PRay p.val) : Prop :=
    Path.Degrees.terminalDegree (0 : Γ) z.1.val z.2.1.val = 0
  have hcomponent (z : Σ p : (s : Type _), PRay p.val) :
      (DirectSum.decompose ℳ z.2.decoration 0 : M) = if leading z then (a : M) else 0 := by
    split_ifs with hz
    · rw [z.2.decoration_eq_of_terminalDegree_eq_zero hshift hT hz]
      exact DirectSum.decompose_of_mem_same ℳ a.property
    · exact DirectSum.decompose_of_mem_ne ℳ z.2.decoration_mem hz
  have hunique (z z' : Σ p : (s : Type _), PRay p.val) (hz : leading z) (hz' : leading z') :
      z = z' := by
    have he := z.2.eq_of_terminalDegree_eq_zero hshift z'.2 hz hz' hP hsep
    obtain ⟨⟨p, hp⟩, r⟩ := z
    obtain ⟨⟨p', hp'⟩, r'⟩ := z'
    dsimp only at he
    obtain ⟨rfl, hr⟩ := Sigma.mk.inj_iff.mp he
    cases eq_of_heq hr
    rfl
  rw [pathDecoratedEvaluation_def]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  simp_rw [hcomponent]
  by_cases hex : ∃ z, leading z
  · obtain ⟨z, hz⟩ := hex
    rw [ite_eq_left ⟨z.1, z.2, hz⟩, Finset.sum_eq_single z]
    · exact ite_eq_left hz
    · intro z' _ hz'z
      exact ite_eq_right fun hz' => hz'z (hunique z' z hz' hz)
    · simp
  · rw [ite_eq_right fun ⟨p, r, hr⟩ => hex ⟨⟨p, r⟩, hr⟩]
    exact Finset.sum_eq_zero fun z _ => ite_eq_right fun hz => hex ⟨z, hz⟩

/-- An admissible incoming straight realization recovers the input as the incoming
component of the weighted evaluation over any inventory exhausting the endpoint fiber. The
input may vanish. -/
theorem decompose_pathDecoratedEvaluation_zero {n : ℕ} (g : Fin n → J)
    (r : AdmissibleRayRealization (fun j => f (g j)) (fun j => c (g j)) (fun _ => v 0)
      (fun j => P (g j)) W S C Q)
    (hε : ∀ j, SignType.sign (f (g j) (v 0)) = ε (g j))
    (hs : ∀ p, PRay p → p ∈ s) :
    (DirectSum.decompose ℳ evaluation 0 : M) = (a : M) := by
  classical
  by_cases ha : (a : M) = 0
  · have ha' : a = 0 := Subtype.ext ha
    subst ha'
    simp
  · rw [decompose_pathDecoratedEvaluation_zero_eq_ite hT hshift hP hsep]
    obtain ⟨r', hr'⟩ := exists_pathDecoratedRay_of_straight T a f c ε P W S C g r hε hT ha
    exact ite_eq_left ⟨⟨_, hs _ r'⟩, r', hr'⟩

end SingleObj

section WallEvent

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {f : ι → V →L[ℝ] ℝ} {c : ι → ℝ}
  {R M Γ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  {T : WallEvent ι → Module.End R M} {a : ℳ 0} {v : Γ → V} {Q : V} {C : Set V}

local notation "PRay" p:max => PathDecoratedRay (Q := SingleObj (WallEvent ι))
  (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v)
  (fun e => WallEvent.normal e f) (fun e => Prod.snd e) (fun e => WallEvent.offset e c)
  (fun e => WallEvent.support e W) W (fun _ : Unit => singularSupport W) C p Q

/-- A complete straight incoming realization recovers the input as the incoming component
after replacing its arbitrary wall representatives by canonical signed events. All
coincident indexed walls and every unchanged encounter are retained. -/
theorem decompose_pathDecoratedEvaluation_zero_of_wallEvents
    {n : ℕ} {u : Fin n → ι}
    (r : AdmissibleRayRealization (fun j => f (u j)) (fun j => c (u j))
      (fun _ => v 0) (fun j => W (u j)) W (fun _ : Unit => singularSupport W) C Q)
    (hker : ∀ j, (f j).toLinearMap.ker = (affineSpan ℝ (W j)).direction)
    (hc : ∀ j x, x ∈ W j → f j x = c j)
    (hT : ∀ e y, y ∈ ℳ 0 → (DirectSum.decompose ℳ (T e y) 0 : M) = y)
    (hshift : ∀ e n m (y : M), y ∈ ℳ n →
      (DirectSum.decompose ℳ (T e y) m : M) ≠ 0 → m - n ∈ d.monoid)
    (s : Finset (Path (SingleObj.star (WallEvent ι)) (SingleObj.star (WallEvent ι))))
    (hs : ∀ p, PRay p → p ∈ s) :
    (DirectSum.decompose ℳ
      (pathDecoratedEvaluation (Q := SingleObj (WallEvent ι)) (M := fun _ => M)
        (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v)
        (fun e => WallEvent.normal e f) (fun e => Prod.snd e) (fun e => WallEvent.offset e c)
        (fun e => WallEvent.support e W) W (fun _ : Unit => singularSupport W) C Q) 0 : M) =
      a := by
  have hregular (j : Fin n) : r.ray (r.parameter j.succ) ∉ singularSupport W := by
    apply r.avoids_singular ()
    simpa only [r.parameter_zero] using r.strictAnti_parameter.antitone (Fin.zero_le j.succ)
  exact decompose_pathDecoratedEvaluation_zero (d := d) (T := T) (a := a) (v := v)
    (f := fun e => e.normal f) (c := fun e => e.offset c) (ε := Prod.snd)
    (P := fun e => e.support W) (W := W) (S := fun _ : Unit => singularSupport W) (C := C)
    (Q := Q) hT hshift
    (fun e => (e.support_subset W e.1.property.choose_spec).trans (subset_iUnion W _))
    (fun _ _ e e' hx hx' he he' => e.eq_of_mem_support_of_normal_sign_eq e' W f (v 0)
      hx hx' he he') s r.wallEvents (r.withWallEvents hker hregular hc)
    r.normal_sign_wallEvents hs

/-- Geometry alone supplies an arrangement on whose complement the incoming component of
the signed-event weighted evaluation is the input, simultaneously for every inventory
exhausting the endpoint fiber, every diagonal-preserving degree-raising propagation and
every input. There is no nonzero-velocity hypothesis. -/
theorem exists_pathDecoratedEvaluation_leadingArrangement [FiniteDimensional ℝ V]
    (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V)
    (hker : ∀ j, (f j).toLinearMap.ker = (affineSpan ℝ (W j)).direction)
    (hc : ∀ j x, x ∈ W j → f j x = c j) (v : Γ → V) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      ∀ (T : WallEvent ι → Module.End R M),
        (∀ e y, y ∈ ℳ 0 → (DirectSum.decompose ℳ (T e y) 0 : M) = y) →
        (∀ e n m (y : M), y ∈ ℳ n →
          (DirectSum.decompose ℳ (T e y) m : M) ≠ 0 → m - n ∈ d.monoid) →
      ∀ (a : ℳ 0)
        (s : Finset (Path (SingleObj.star (WallEvent ι)) (SingleObj.star (WallEvent ι)))),
        (∀ p, PathDecoratedRay (Q := SingleObj (WallEvent ι))
          (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v)
          (fun e => WallEvent.normal e f) (fun e => Prod.snd e) (fun e => WallEvent.offset e c)
          (fun e => WallEvent.support e W) W (fun _ : Unit => singularSupport W) univ p Q →
            p ∈ s) →
        (DirectSum.decompose ℳ
          (pathDecoratedEvaluation (Q := SingleObj (WallEvent ι)) (M := fun _ => M)
            (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v)
            (fun e => WallEvent.normal e f) (fun e => Prod.snd e)
            (fun e => WallEvent.offset e c) (fun e => WallEvent.support e W) W
            (fun _ : Unit => singularSupport W) univ Q) 0 : M) = a := by
  obtain ⟨A, hA⟩ := exists_straightRayRealizationArrangement f c hpoly hdim hker hc {v 0}
  refine ⟨A, fun Q hQ T hT hshift a s hs => ?_⟩
  obtain ⟨n, u, r, _⟩ := hA Q hQ (v 0) (Finset.mem_singleton_self _)
  exact decompose_pathDecoratedEvaluation_zero_of_wallEvents r hker hc hT hshift s hs

end WallEvent

namespace PositiveDegrees

variable {Γ : Type} {R L M V ι : Type*}
  [AddCommGroup Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [DirectSum.Decomposition ℳ]
  [SetLike.GradedBracket ℒ ℳ] (p : Γ)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {f : ι → V →L[ℝ] ℝ} {c : ι → ℝ}

/-- The incoming component of finite shifted BCH path ray sums is the input off one
geometric arrangement, at every cutoff and over every inventory exhausting the endpoint
fiber. Signed labels may be inverses or products of simultaneous wall labels. No
consistency, faithfulness, coefficient basis or nonzero spatial direction is required. -/
theorem exists_pathDecoratedEvaluation_leadingArrangement_shiftedBCHAction
    [FiniteDimensional ℝ V]
    (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V)
    (hker : ∀ j, (f j).toLinearMap.ker = (affineSpan ℝ (W j)).direction)
    (hc : ∀ j x, x ∈ W j → f j x = c j) (v : Γ → V) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q → ∀ (k : ℕ)
      (g : WallEvent ι → d.truncatedGroup ℒ k)
      (a : (d.shiftedQuotientGrading ℳ p k).piece 0)
      (s : Finset (Path (SingleObj.star (WallEvent ι)) (SingleObj.star (WallEvent ι)))),
      (∀ q, PathDecoratedRay (Q := SingleObj (WallEvent ι))
        (M := fun _ => (d.shiftedLieFiltration ℒ ℳ p).quotient k) (ι := fun _ => Γ)
        (fun e => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k (g e)).toLinearMap)
        (fun _ => (d.shiftedQuotientGrading ℳ p k).piece) 0 a (fun _ => v)
        (fun e => WallEvent.normal e f) (fun e => Prod.snd e) (fun e => WallEvent.offset e c)
        (fun e => WallEvent.support e W) W (fun _ : Unit => singularSupport W) univ q Q →
          q ∈ s) →
      (DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece
        (pathDecoratedEvaluation (Q := SingleObj (WallEvent ι))
          (M := fun _ => (d.shiftedLieFiltration ℒ ℳ p).quotient k) (ι := fun _ => Γ)
          (fun e => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
            (g e)).toLinearMap)
          (fun _ => (d.shiftedQuotientGrading ℳ p k).piece) 0 a s (fun _ => v)
          (fun e => WallEvent.normal e f) (fun e => Prod.snd e)
          (fun e => WallEvent.offset e c) (fun e => WallEvent.support e W) W
          (fun _ : Unit => singularSupport W) univ Q) 0 :
        (d.shiftedLieFiltration ℒ ℳ p).quotient k) = a := by
  -- Choose geometry before the cutoff: coefficient quotients vary with k,
  -- whereas the complete incoming straight realization does not.
  obtain ⟨A, hA⟩ := exists_straightRayRealizationArrangement f c hpoly hdim hker hc {v 0}
  refine ⟨A, fun Q hQ k g a s hs => ?_⟩
  obtain ⟨n, u, r, _⟩ := hA Q hQ (v 0) (Finset.mem_singleton_self _)
  exact decompose_pathDecoratedEvaluation_zero_of_wallEvents (d := d) r hker hc
    (fun e _ hy => d.decompose_truncatedBCHAction_same ℒ ℳ p k (g e) hy)
    (fun e _ _ _ hy hne => d.sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero ℒ ℳ p k (g e)
      hy (by simpa using hne)) s hs

end PositiveDegrees

end Mei
