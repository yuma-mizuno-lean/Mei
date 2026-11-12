/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
public import Mei.Geometry.Convex.Sweep.Admissible.Attach
public import Mei.Algebra.BigOperators.Group.Finset.Subtype
public import Mei.Algebra.PositiveDegrees.Basic

/-!
# Decomposing path ray sums by their final encounter

Fix a final arrow `w : b ⟶ b'` of a path `p.cons w`, a final degree `q` and a degree `p'`
before `w` with the same normal velocity at `w`. Suppose the backward line `X + u • v q`
from the endpoint `X` first meets the walls at a regular point of the support of `w`,
at parameter `t`, with the prescribed crossing sign. Then for every sufficiently short
incoming displacement `η`, the actual decorated rays along `p.cons w` at `X` with final
degree `q` and degree `p'` before `w` carry exactly the selected degree-`q` component of
the transfer of `w` applied to the degree-`p'` decorations of the actual rays along `p`
at the incoming germ `X + t • v q + η • v p'`.

Distinct histories remain distinct, killed components contribute zero, and the
incoming tails, sources and obstacle conditions of the older rays are retained. The
geometric input is `Convex.eventually_mem_admissibleBackwardDomain_cons_iff`. This is
the nearest-encounter step of the backward-ray recursion of Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open TauCeti (PositiveDegrees)

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
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "support" => pathDecoratedHistorySupport T ℳ i₀ x v ν ε
local notation "Ray" p:max X:max => PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X
local notation "D(" p ", " d ")" => admissibleBackwardDomain (Path.reverseArrowLabels ν p)
  (Path.reverseArrowLabels c p) (Path.Degrees.reverseVertexLabels v i₀ p d)
  (Path.reverseArrowLabels P p) W S C

open Classical in
/-- Sum actual rays satisfying a condition on their histories by their surviving
histories, testing the complete endpoint constraints. -/
theorem sum_ite_pathDecoratedRay_eq_sum (p : Path a b) (X : V) (E : p.Degrees ι → Prop)
    [DecidablePred E] {_ : Fintype (Ray p X)} :
    ∑ r : Ray p X, (if E r.1.val then r.decoration else 0) =
      ∑ d ∈ support p, if X ∈ D(p, d) ∧ E d then p.homogeneousHistory T ℳ d x else 0 := by
  rw [Fintype.sum_eq_sum_ite_of_equiv_subtype
    (pathDecoratedRayFiberEquiv T ℳ i₀ x v ν ε c P W S C p X) _
    (fun d => if E d.val then p.homogeneousHistory T ℳ d.val x else 0) fun r => by
      rw [PathDecoratedRay.decoration_def, pathDecoratedRayFiberEquiv_history]]
  rw [← Finset.sum_coe_sort (support p)]
  exact Finset.sum_congr rfl fun d _ => by rw [ite_and]

/-- The weighted evaluation is the sum over the inventory of the sums of the actual
decorated ray fibers along its paths. -/
theorem pathDecoratedEvaluation_eq_sum_fiber (s : Finset (Path a b)) (X : V) :
    pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X =
      ∑ p ∈ s, (let := Fintype.ofFinite (Ray p X)
        ∑ r : Ray p X, r.decoration) := by
  classical
  let : ∀ p : (s : Type _), Fintype (Ray p.val X) := fun _ => Fintype.ofFinite _
  let := Fintype.ofFinite (Σ p : (s : Type _), Ray p.val X)
  rw [pathDecoratedEvaluation_def]
  dsimp only
  trans ∑ p : (s : Type _), ∑ r : Ray p.val X, r.decoration
  · -- The evaluation uses `Fintype.ofFinite`, while the iterated sum uses the
    -- dependent-sum instance. Both enumerate the same finite type.
    convert Fintype.sum_sigma (fun r : Σ p : (s : Type _), Ray p.val X => r.2.decoration)
      using 1
    congr 1
    ext r
    simp
  · exact Finset.sum_coe_sort s fun p =>
      (let := Fintype.ofFinite (Ray p X)
       ∑ r : Ray p X, r.decoration)

variable {b' : Q} (p : Path a b) (w : b ⟶ b') (q : ι b') (p' : ι b) (X : V) {t : ℝ}

open Classical in
/-- Near a regular final encounter `w` at `X + t • v q`, the rays along `p.cons w` with
final degree `q` and degree `p'` before `w` carry exactly the selected degree-`q`
component of the transfer of `w` applied to the degree-`p'` decorations of the rays along
`p` at every sufficiently close incoming germ `X + t • v q + η • v p'`. -/
theorem eventually_sum_pathDecoratedRay_cons_eq [Finite J] [Finite K] (ht : 0 < t)
    (hnormal : ν w (v b' q) = ν w (v b p')) (htrans : ν w (v b' q) ≠ 0)
    (hsign : SignType.sign (ν w (v b' q)) = ε w)
    (hheight : ν w (X + t • v b' q) = c w) (hinc : X + t • v b' q ∈ P w)
    (hP : P w ⊆ ⋃ j, W j) (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, X + t • v b' q ∈ W j → ∀ y ∈ W j, ν w y = c w)
    (hclosedS : ∀ j, IsClosed (S j)) (hregular : ∀ j, X + t • v b' q ∉ S j)
    (hW : ∀ j u, 0 ≤ u → u < t → X + u • v b' q ∉ W j)
    (hS : ∀ j u, 0 ≤ u → u < t → X + u • v b' q ∉ S j) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      (let := Fintype.ofFinite (Ray (p.cons w) X)
       ∑ r : Ray (p.cons w) X,
        if r.1.val.2 = q ∧ Path.Degrees.terminalDegree i₀ p r.1.val.1 = p'
        then r.decoration else 0) =
      (DirectSum.decompose (ℳ b') (T w
        (let := Fintype.ofFinite (Ray p (X + t • v b' q + η • v b p'))
         ∑ r : Ray p (X + t • v b' q + η • v b p'),
          if Path.Degrees.terminalDegree i₀ p r.1.val = p' then r.decoration else 0)) q :
        M b') := by
  classical
  -- For every older history ending in `p'`, the attached endpoint and the incoming
  -- germ are admitted together.
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ dd ∈ support p,
      Path.Degrees.terminalDegree i₀ p dd = p' →
        (X ∈ D(p.cons w, ((dd, q) : (p.cons w).Degrees ι)) ↔
          X + t • v b' q + η • v b p' ∈ D(p, dd)) := by
    refine (Filter.eventually_all_finset _).mpr fun dd _ => ?_
    by_cases hdd : Path.Degrees.terminalDegree i₀ p dd = p'
    · have h0 : Path.Degrees.reverseVertexLabels v i₀ p dd 0 = v b p' := by
        rw [Path.Degrees.reverseVertexLabels_zero, hdd]
      have h := eventually_mem_admissibleBackwardDomain_cons_iff (C := C)
        (f := Path.reverseArrowLabels ν p) (c := Path.reverseArrowLabels c p)
        (v := Path.Degrees.reverseVertexLabels v i₀ p dd) (P := Path.reverseArrowLabels P p)
        (ν w) (c w) (P w) (v b' q) X ht htrans (by rw [h0]; exact hnormal) hheight hinc hP
        hclosedW hplane hclosedS hregular hW hS
      filter_upwards [h] with η hη _
      rw [Path.reverseArrowLabels_cons, Path.reverseArrowLabels_cons,
        Path.Degrees.reverseVertexLabels_cons, Path.reverseArrowLabels_cons]
      rw [h0] at hη
      exact hη
    · exact Eventually.of_forall fun _ h => (hdd h).elim
  filter_upwards [hev] with η hη
  set Y := X + t • v b' q + η • v b p'
  dsimp only
  rw [sum_ite_pathDecoratedRay_eq_sum T ℳ i₀ x v ν ε c P W S C (p.cons w) X
      (fun d => d.2 = q ∧ Path.Degrees.terminalDegree i₀ p d.1 = p'),
    sum_ite_pathDecoratedRay_eq_sum T ℳ i₀ x v ν ε c P W S C p Y
      (fun d => Path.Degrees.terminalDegree i₀ p d = p'), map_sum,
    DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  have hR : ∀ dd ∈ support p,
      (DirectSum.decompose (ℳ b') (T w (if Y ∈ D(p, dd) ∧
        Path.Degrees.terminalDegree i₀ p dd = p' then p.homogeneousHistory T ℳ dd x else 0))
          q : M b') =
        if Y ∈ D(p, dd) ∧ Path.Degrees.terminalDegree i₀ p dd = p' then
          (DirectSum.decompose (ℳ b') (T w (p.homogeneousHistory T ℳ dd x)) q : M b')
        else 0 := by
    intro dd _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hR]
  refine Finset.sum_bij_ne_zero (fun d _ _ => d.1) ?_ ?_ ?_ ?_
  · intro d hd _
    obtain ⟨dd, i⟩ := d
    exact ((mem_pathDecoratedHistorySupport_cons T ℳ i₀ x v ν ε p w dd i).mp hd).1
  · rintro ⟨dd₁, i₁⟩ - h₁ ⟨dd₂, i₂⟩ - h₂ he
    obtain ⟨-, hi₁, -⟩ := (ite_ne_right_iff.mp h₁).1
    obtain ⟨-, hi₂, -⟩ := (ite_ne_right_iff.mp h₂).1
    exact Prod.ext he (hi₁.trans hi₂.symm)
  · intro dd hdd hne
    obtain ⟨⟨hY, hterm⟩, hne⟩ := ite_ne_right_iff.mp hne
    have hhist : (p.cons w).homogeneousHistory T ℳ ((dd, q) : (p.cons w).Degrees ι) x ≠ 0 := by
      rw [Path.homogeneousHistory_cons_apply]
      exact hne
    refine ⟨(dd, q), (mem_pathDecoratedHistorySupport_cons T ℳ i₀ x v ν ε p w dd q).mpr
      ⟨hdd, hhist, by rw [hterm]; exact hnormal, hsign⟩, ?_, rfl⟩
    exact ite_ne_right_iff.mpr ⟨⟨(hη dd hdd hterm).mpr hY, rfl, hterm⟩, hhist⟩
  · rintro ⟨dd, i⟩ hd hne
    obtain ⟨⟨hX, hi, hterm⟩, -⟩ := ite_ne_right_iff.mp hne
    dsimp only at hi hterm ⊢
    subst hi
    have hdd := ((mem_pathDecoratedHistorySupport_cons T ℳ i₀ x v ν ε p w dd _).mp hd).1
    rw [ite_eq_left ⟨hX, rfl, hterm⟩, ite_eq_left ⟨(hη dd hdd hterm).mp hX, hterm⟩,
      Path.homogeneousHistory_cons_apply]

section SingleObj

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P : J → Set V} {W : I → Set V} {S : K → Set V} {C : Set V}

local notation "PRay" => PathDecoratedRay (Q := SingleObj J) (M := fun _ => M)
  (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
  (fun e => ε e) (fun e => c e) (fun e => P e) W S C
local notation "Paths" => Path (SingleObj.star J) (SingleObj.star J)
local notation "evaluation" => fun s X => pathDecoratedEvaluation (Q := SingleObj J)
  (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v)
  (fun e => f e) (fun e => ε e) (fun e => c e) (fun e => P e) W S C X

variable (Q : V) (w : J) (q : Γ) {t : ℝ}

/-- An actual ray of final degree `q` meets its final encounter `e` transversally with
the prescribed crossing sign, at a positive parameter of the backward line from `Q` in
the direction of `q`, and the walls miss that line before it. -/
theorem PathDecoratedRay.exists_finalEncounter_of_final_degree {b : SingleObj J}
    (p : Path (SingleObj.star J) b) (e : b ⟶ SingleObj.star J) (r : PRay (p.cons e) Q)
    (hr : r.1.val.2 = q) :
    f e (v q) ≠ 0 ∧ SignType.sign (f e (v q)) = ε e ∧ ∃ τ : ℝ, 0 < τ ∧
      f e (Q + τ • v q) = c e ∧ Q + τ • v q ∈ P e ∧
      ∀ j u, 0 ≤ u → u < τ → Q + u • v q ∉ W j := by
  obtain ⟨⟨⟨dd, i⟩, hmem⟩, g⟩ := r
  dsimp only at hr
  subst hr
  have hsign := ((mem_pathDecoratedHistorySupport_cons (Q := SingleObj J) (M := fun _ => M)
    (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
    (fun e => ε e) p e dd i).mp hmem).2.2.2
  -- Present the final encounter as the first entry of the backward data.
  have g' := g.congrData (Path.reverseArrowLabels_cons (fun e => f e) p e)
    (Path.reverseArrowLabels_cons (fun e => c e) p e)
    (Path.Degrees.reverseVertexLabels_cons (fun _ => v) 0 p e dd i)
    (Path.reverseArrowLabels_cons (fun e => P e) p e)
  obtain ⟨htrans, τ, hτ, -, hh, hm, hav⟩ := g'.exists_finalEncounter
  simp only [Fin.cons_zero] at htrans hh hm hav
  exact ⟨htrans, hsign, τ, hτ, hh, hm, hav⟩

/-- When the backward line from `Q` in the direction of `q` first meets the walls at
`Q + t • v q`, where `w` is the only incident label with the prescribed crossing sign,
every actual ray of final degree `q` has final encounter `w`. -/
theorem PathDecoratedRay.eq_of_final_degree {b : SingleObj J} (p : Path (SingleObj.star J) b)
    (e : b ⟶ SingleObj.star J) (r : PRay (p.cons e) Q) (hr : r.1.val.2 = q)
    (hP : ∀ j, P j ⊆ ⋃ b, W b) (ht : 0 < t) (hinc : Q + t • v q ∈ P w)
    (hunique : ∀ e, f e (v q) ≠ 0 → SignType.sign (f e (v q)) = ε e →
      f e (Q + t • v q) = c e → Q + t • v q ∈ P e → e = w)
    (hW : ∀ j u, 0 ≤ u → u < t → Q + u • v q ∉ W j) : (e : J) = w := by
  obtain ⟨htrans, hsign, τ, hτ, hh, hm, hav⟩ :=
    r.exists_finalEncounter_of_final_degree Q q p e hr
  have hτt : τ = t := by
    rcases lt_trichotomy τ t with hlt | rfl | hgt
    · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hP _ hm)
      exact (hW b τ hτ.le hlt hb).elim
    · rfl
    · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hP w hinc)
      exact (hav b t ht.le hgt hb).elim
  subst hτt
  exact hunique e htrans hsign hh hm

/-- If the backward line from `Q` in the direction of `q ≠ 0` meets no support at a
signed transverse encounter, no actual ray has final degree `q`, so the degree-`q`
component of the weighted evaluation vanishes, over any inventory. -/
theorem decompose_pathDecoratedEvaluation_eq_zero_of_forall_not_encounter
    (s : Finset Paths) (hq0 : q ≠ 0)
    (hnone : ∀ e (u : ℝ), 0 < u → f e (v q) ≠ 0 → SignType.sign (f e (v q)) = ε e →
      f e (Q + u • v q) = c e → Q + u • v q ∈ P e → False) :
    (DirectSum.decompose ℳ (pathDecoratedEvaluation (Q := SingleObj J)
        (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v)
        (fun e => f e) (fun e => ε e) (fun e => c e) (fun e => P e) W S C Q) q : M) = 0 := by
  rw [pathDecoratedEvaluation_eq_sum_fiber]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : Path.Degrees.terminalDegree (0 : Γ) p r.1.val = q
  · exfalso
    cases p with
    | nil => exact hq0 hr.symm
    | @cons b _ p₀ e =>
      obtain ⟨htrans, hsign, τ, hτ, hh, hm, -⟩ :=
        r.exists_finalEncounter_of_final_degree Q q p₀ e hr
      exact hnone e τ hτ htrans hsign hh hm
  · exact DirectSum.decompose_of_mem_ne ℳ r.decoration_mem hr

open Classical in
/-- Let the backward line from `Q` in the direction of the final degree `q ≠ 0` first
meet the walls at the regular encounter `w`, at ray parameter `t`. For all sufficiently
short incoming displacements, the degree-`q` component of the weighted evaluation at `Q`
is the sum, over the degrees `p'` before `w` that preserve its normal velocity, of the
degree-`q` component of `T w` applied to the degree-`p'` evaluation at the incoming germ
`Q + t • v q + η • v p'`. The inventory exhausts every endpoint fiber, and `D` contains
the degree of every nonzero homogeneous coefficient. The unchanged degree `p' = q` is
included. -/
theorem eventually_decompose_pathDecoratedEvaluation_eq_sum_finalEncounter
    [Finite K] [Finite I] (s : Finset Paths) (hs : ∀ X p, PRay p X → p ∈ s)
    (D : Finset Γ) (hD : ∀ n (y : M), y ∈ ℳ n → y ≠ 0 → n ∈ D)
    (hshift : ∀ j n m (y : M), y ∈ ℳ n →
      (DirectSum.decompose ℳ (T j y) m : M) ≠ 0 → m - n ∈ d.monoid)
    (hq0 : q ≠ 0) (hP : ∀ j, P j ⊆ ⋃ b, W b) (ht : 0 < t)
    (htrans : f w (v q) ≠ 0) (hsign : SignType.sign (f w (v q)) = ε w)
    (hheight : f w (Q + t • v q) = c w) (hinc : Q + t • v q ∈ P w)
    (hunique : ∀ e, f e (v q) ≠ 0 → SignType.sign (f e (v q)) = ε e →
      f e (Q + t • v q) = c e → Q + t • v q ∈ P e → e = w)
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, Q + t • v q ∈ W j → ∀ y ∈ W j, f w y = c w)
    (hclosedS : ∀ j, IsClosed (S j)) (hregular : ∀ j, Q + t • v q ∉ S j)
    (hW : ∀ j u, 0 ≤ u → u < t → Q + u • v q ∉ W j)
    (hS : ∀ j u, 0 ≤ u → u < t → Q + u • v q ∉ S j) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      (DirectSum.decompose ℳ (pathDecoratedEvaluation (Q := SingleObj J)
        (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v)
        (fun e => f e) (fun e => ε e) (fun e => c e) (fun e => P e) W S C Q) q : M) =
        ∑ p' ∈ D with q - p' ∈ d.monoid ∧ f w (v q) = f w (v p'),
          (DirectSum.decompose ℳ (T w (DirectSum.decompose ℳ (pathDecoratedEvaluation
            (Q := SingleObj J) (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e)
            (fun _ => ℳ) 0 a s (fun _ => v) (fun e => f e) (fun e => ε e) (fun e => c e)
            (fun e => P e) W S C (Q + t • v q + η • v p')) p')) q : M) := by
  classical
  let w' : SingleObj.star J ⟶ SingleObj.star J := w
  set D' := D.filter fun p' => q - p' ∈ d.monoid ∧ f w (v q) = f w (v p')
  -- The degree-`n` part of the actual ray fiber along one path.
  let F : Paths → V → Γ → M := fun p X n =>
    let := Fintype.ofFinite (PRay p X)
    ∑ r : PRay p X, if Path.Degrees.terminalDegree (0 : Γ) p r.1.val = n then r.decoration else 0
  have hcomp (s' : Finset Paths) (X : V) (n : Γ) :
      (DirectSum.decompose ℳ (pathDecoratedEvaluation (Q := SingleObj J)
        (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a s' (fun _ => v)
        (fun e => f e) (fun e => ε e) (fun e => c e) (fun e => P e) W S C X) n : M) =
        ∑ p ∈ s', F p X n := by
    rw [pathDecoratedEvaluation_eq_sum_fiber]
    simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    split_ifs with h
    · rw [← h]
      exact DirectSum.decompose_of_mem_same ℳ r.decoration_mem
    · exact DirectSum.decompose_of_mem_ne ℳ r.decoration_mem h
  have hempty (p : Paths) (X : V) (hp : p ∉ s) (n : Γ) : F p X n = 0 := by
    have : IsEmpty (PRay p X) := ⟨fun r => hp (hs X p r)⟩
    simp [F]
  have hinj : Set.InjOn (fun p₀ : Paths => p₀.cons w')
      ((fun p₀ : Paths => p₀.cons w') ⁻¹' (s : Set Paths)) :=
    fun p₁ _ p₂ _ h => eq_of_heq (Path.heq_of_cons_eq_cons h)
  set s₀ := s.preimage (fun p₀ : Paths => p₀.cons w') hinj
  set U := s ∪ s₀
  -- Split the rays along `p₀.cons w` of final degree `q` by their degree before `w`.
  have hsplit (p₀ : Paths) : F (p₀.cons w') Q q = ∑ p' ∈ D',
      (let := Fintype.ofFinite (PRay (p₀.cons w') Q)
       ∑ r : PRay (p₀.cons w') Q,
        if r.1.val.2 = q ∧ Path.Degrees.terminalDegree (0 : Γ) p₀ r.1.val.1 = p'
        then r.decoration else 0) := by
    dsimp only [F]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : r.1.val.2 = q
    · have hm := (mem_pathDecoratedHistorySupport_cons (Q := SingleObj J) (M := fun _ => M)
        (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
        (fun e => ε e) p₀ w' r.1.val.1 r.1.val.2).mp r.1.property
      obtain ⟨-, hne, hnormal, -⟩ := hm
      have hhist := p₀.homogeneousHistory_ne_zero_of_cons _ _ w' r.1.val.1 r.1.val.2 hne
      have hvert := p₀.homogeneousHistory_mem_vertex (T := fun e => T e) (ℳ := fun _ => ℳ)
        r.1.val.1 0 (a : M) a.property
      rw [Path.homogeneousHistory_cons_apply, hr] at hne
      rw [hr] at hnormal
      have hmem : Path.Degrees.terminalDegree (0 : Γ) p₀ r.1.val.1 ∈ D' :=
        Finset.mem_filter.mpr ⟨hD _ _ hvert hhist, hshift w _ _ _ hvert hne, hnormal⟩
      simp only [hr, true_and]
      rw [Finset.sum_ite_eq, ite_eq_left hmem]
      simp
    · rw [ite_eq_right (by rw [Path.Degrees.terminalDegree_cons]; exact hr)]
      exact (Finset.sum_eq_zero fun p' _ => ite_eq_right fun h => hr h.1).symm
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ p₀ ∈ U, ∀ p' ∈ D',
      (let := Fintype.ofFinite (PRay (p₀.cons w') Q)
       ∑ r : PRay (p₀.cons w') Q,
        if r.1.val.2 = q ∧ Path.Degrees.terminalDegree (0 : Γ) p₀ r.1.val.1 = p'
        then r.decoration else 0) =
      (DirectSum.decompose ℳ (T w (F p₀ (Q + t • v q + η • v p') p')) q : M) := by
    refine (Filter.eventually_all_finset U).mpr fun p₀ _ =>
      (Filter.eventually_all_finset D').mpr fun p' hp' => ?_
    exact eventually_sum_pathDecoratedRay_cons_eq (Q := SingleObj J) (M := fun _ => M)
      (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
      (fun e => ε e) (fun e => c e) (fun e => P e) W S C p₀ w' q p' Q ht
      (Finset.mem_filter.mp hp').2.2 htrans hsign hheight hinc (hP w) hclosedW hplane
      hclosedS hregular hW hS
  filter_upwards [hev] with η hη
  rw [hcomp]
  -- Only paths ending with `w` carry rays of final degree `q`.
  have hzero : ∀ p ∈ s, p ∉ Set.range (fun p₀ : Paths => p₀.cons w') → F p Q q = 0 := by
    intro p _ hp
    refine Finset.sum_eq_zero fun r _ => ite_eq_right fun hr => ?_
    cases p with
    | nil => exact hq0 hr.symm
    | @cons b _ p₀ e =>
      cases b
      have he := PathDecoratedRay.eq_of_final_degree Q w q p₀ e r hr hP ht hinc hunique hW
      exact hp ⟨p₀, by rw [he]⟩
  rw [← Finset.sum_preimage _ s hinj (fun p => F p Q q) hzero]
  rw [Finset.sum_subset (Finset.subset_union_right (s₁ := s)) fun p₀ _ hp₀ =>
    hempty _ Q (fun h => hp₀ (Finset.mem_preimage.mpr h)) q]
  rw [Finset.sum_congr rfl fun p₀ hp₀ => (hsplit p₀).trans
    (Finset.sum_congr rfl fun p' hp' => hη p₀ hp₀ p' hp'), Finset.sum_comm]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [hcomp, map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum,
    Finset.sum_subset (Finset.subset_union_left (s₁ := s) (s₂ := s₀)) fun p₀ _ hp₀ => by
      rw [hempty p₀ _ hp₀, map_zero, DirectSum.decompose_zero, DirectSum.zero_apply,
        Submodule.coe_zero]]

end SingleObj

end Mei
