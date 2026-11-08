/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Concatenation of decorated histories across chambers

A signed component history along two consecutive encounter paths splits into
one history on each block. The later block starts with the entire homogeneous
output of the earlier block. The chambers may have different coefficient
semimodules and degree types. The correspondence retains all encounters,
including unchanged degrees and degree changes invisible in space.

Selected finite sums factor through this correspondence. In particular the sum
of actual rays along the joined path can be grouped by its earlier history,
while testing the full joined endpoint domain. This retains the geometric
incidence inequalities, unrecorded-wall and singular avoidance, and admission
of the original incoming tail. It makes no claim that the separated blocks
are independently admissible rays.

We use `Quiver.Path.degreesComp` and `Quiver.Path.homogeneousHistory_comp`.
The local-to-exterior grouping follows Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3.2
(arXiv:1601.07081v4).
-/

public noncomputable section

open Set Quiver Mei.Convex

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

local notation "out(" p ", " d ")" =>
  (Subtype.mk (Path.homogeneousHistory T ℳ p d x)
    (Path.homogeneousHistory_mem_vertex (T := T) (ℳ := ℳ) p d i₀ x x.property) :
      ℳ _ (Path.Degrees.terminalDegree i₀ p d))
local notation "support(" p ")" => pathDecoratedHistorySupport T ℳ i₀ x v ν ε p

/-- A joined signed history survives exactly when both blocks survive, with
the second block acting on the entire intermediate coefficient. -/
theorem mem_pathDecoratedHistorySupport_comp (p : Path a b) :
    ∀ {c : Q} (q : Path b c) (d : p.Degrees ι) (e : q.Degrees ι),
      (Path.degreesComp (ι := ι) p q).symm (d, e) ∈ support(p.comp q) ↔
        d ∈ support(p) ∧ e ∈ pathDecoratedHistorySupport T ℳ
          (Path.Degrees.terminalDegree i₀ p d) out(p, d) v ν ε q
  | _, .nil, d, e => by
    rw [Path.degreesComp_symm_nil (ι := ι) p d]
    -- Expose the empty concatenation in the dependent support index.
    change d ∈ support(p) ↔ _
    rw [mem_pathDecoratedHistorySupport T ℳ (Path.Degrees.terminalDegree i₀ p d)
      out(p, d) v ν ε Path.nil e]
    simp only [mem_pathDecoratedHistorySupport, Path.homogeneousHistory_nil, LinearMap.id_apply,
      Path.length_nil, Fin.forall_fin_zero, and_true]
    tauto
  | _, .cons q f, d, e => by
    obtain ⟨e, i⟩ := e
    rw [Path.degreesComp_symm_cons]
    -- Expose the recursive concatenation in the dependent history type.
    change ((Path.degreesComp (ι := ι) p q).symm (d, e), i) ∈
      support((p.comp q).cons f) ↔ _
    rw [mem_pathDecoratedHistorySupport_cons,
      mem_pathDecoratedHistorySupport_comp p q d e,
      mem_pathDecoratedHistorySupport_cons, Path.Degrees.terminalDegree_comp]
    simp only [Path.homogeneousHistory_cons, LinearMap.comp_apply]
    rw [Path.homogeneousHistory_comp, LinearMap.comp_apply]
    tauto

/-- Split a complete signed history into consecutive surviving blocks. The
intermediate decoration is homogeneous in the retained terminal degree. -/
def pathDecoratedHistoryCompEquiv {c : Q} (p : Path a b) (q : Path b c) :
    (support(p.comp q) : Type _) ≃
      Σ d : (support(p) : Type _),
        (pathDecoratedHistorySupport T ℳ (Path.Degrees.terminalDegree i₀ p d.val)
          out(p, d.val) v ν ε q : Type _) := by
  let e : (Σ _d : p.Degrees ι, q.Degrees ι) ≃ (p.comp q).Degrees ι :=
    (Equiv.sigmaEquivProd _ _).trans (Path.degreesComp (ι := ι) p q).symm
  exact (e.subtypeEquivOfSubtype (p := fun d => d ∈ support(p.comp q))).symm.trans
    ((Equiv.subtypeEquivRight fun de : (Σ _d : p.Degrees ι, q.Degrees ι) =>
      mem_pathDecoratedHistorySupport_comp T ℳ i₀ x v ν ε p q de.1 de.2).trans
        (Equiv.subtypeSigmaEquivSigma
          (p := fun d : p.Degrees ι => d ∈ support(p))
          (q := fun (d : p.Degrees ι) (e : q.Degrees ι) => e ∈
            pathDecoratedHistorySupport T ℳ (Path.Degrees.terminalDegree i₀ p d)
              out(p, d) v ν ε q)))

local notation "split(" p ", " q ")" =>
  pathDecoratedHistoryCompEquiv T ℳ i₀ x v ν ε p q

/-- Splitting retains the first block's complete degree history. -/
@[simp]
theorem pathDecoratedHistoryCompEquiv_fst {c : Q} (p : Path a b) (q : Path b c)
    (d : (support(p.comp q) : Type _)) :
    (split(p, q) d).1.val = (Path.degreesComp (ι := ι) p q d.val).1 := (rfl)

/-- Splitting retains the second block's complete degree history. -/
@[simp]
theorem pathDecoratedHistoryCompEquiv_snd {c : Q} (p : Path a b) (q : Path b c)
    (d : (support(p.comp q) : Type _)) :
    (split(p, q) d).2.val = (Path.degreesComp (ι := ι) p q d.val).2 := (rfl)

/-- Joining restores exactly the original pair of complete histories. -/
@[simp]
theorem pathDecoratedHistoryCompEquiv_symm_val {c : Q} (p : Path a b) (q : Path b c)
    (d : Σ d : (support(p) : Type _),
      (pathDecoratedHistorySupport T ℳ (Path.Degrees.terminalDegree i₀ p d.val)
        out(p, d.val) v ν ε q : Type _)) :
    ((split(p, q)).symm d).val = (Path.degreesComp (ι := ι) p q).symm (d.1.val, d.2.val) := (rfl)

/-- Splitting identifies the second block's decoration of the first block's
output with the joined decoration. -/
theorem pathDecoratedHistoryCompEquiv_decoration {c : Q} (p : Path a b) (q : Path b c)
    (d : (support(p.comp q) : Type _)) :
    q.homogeneousHistory T ℳ (split(p, q) d).2.val out(p, (split(p, q) d).1.val) =
      (p.comp q).homogeneousHistory T ℳ d.val x := by
  simp only [pathDecoratedHistoryCompEquiv_fst, pathDecoratedHistoryCompEquiv_snd]
  have h := Path.homogeneousHistory_comp T ℳ p q
    (Path.degreesComp (ι := ι) p q d.val).1 (Path.degreesComp (ι := ι) p q d.val).2
  rw [Prod.mk.eta, Equiv.symm_apply_apply] at h
  exact (LinearMap.congr_fun h x).symm

open Classical in
/-- Group any selected signed histories by their first block. The selection
may depend on the entire joined history, including geometric admission. -/
theorem sum_ite_pathDecoratedHistory_comp {c : Q} (p : Path a b) (q : Path b c)
    (E : p.Degrees ι → q.Degrees ι → Prop) :
    (∑ d : (support(p.comp q) : Type _),
      if E (Path.degreesComp (ι := ι) p q d.val).1 (Path.degreesComp (ι := ι) p q d.val).2
      then (p.comp q).homogeneousHistory T ℳ d.val x else 0) =
      ∑ d : (support(p) : Type _),
        ∑ e : (pathDecoratedHistorySupport T ℳ (Path.Degrees.terminalDegree i₀ p d.val)
          out(p, d.val) v ν ε q : Type _),
          if E d.val e.val then q.homogeneousHistory T ℳ e.val out(p, d.val) else 0 := by
  let F (d : Σ d : (support(p) : Type _),
      (pathDecoratedHistorySupport T ℳ (Path.Degrees.terminalDegree i₀ p d.val)
        out(p, d.val) v ν ε q : Type _)) : M c :=
    if E d.1.val d.2.val then q.homogeneousHistory T ℳ d.2.val out(p, d.1.val) else 0
  calc
    _ = ∑ d, F d := by
      apply Fintype.sum_equiv (split(p, q))
      intro d
      simp only [F, pathDecoratedHistoryCompEquiv_fst, pathDecoratedHistoryCompEquiv_snd]
      split_ifs
      · exact (pathDecoratedHistoryCompEquiv_decoration T ℳ i₀ x v ν ε p q d).symm
      · rfl
    _ = _ := Fintype.sum_sigma F

variable (offset : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "domain(" p ", " d ")" => admissibleBackwardDomain
  (Path.reverseArrowLabels ν p) (Path.reverseArrowLabels offset p)
  (Path.Degrees.reverseVertexLabels v i₀ p d) (Path.reverseArrowLabels P p) W S C

open Classical in
/-- Regroup the actual joined ray sum by its earlier signed history. The full
joined domain selects both blocks together, retaining original incoming tails
and all geometric incidence and avoidance constraints. Neither block is
assumed to be an independently admissible ray. -/
theorem sum_pathDecoratedRay_comp {c : Q} (p : Path a b) (q : Path b c) (X : V) :
    (let := Fintype.ofFinite
      (PathDecoratedRay T ℳ i₀ x v ν ε offset P W S C (p.comp q) X)
     ∑ r : PathDecoratedRay T ℳ i₀ x v ν ε offset P W S C (p.comp q) X,
       r.decoration) =
      ∑ d : (support(p) : Type _),
        ∑ e : (pathDecoratedHistorySupport T ℳ (Path.Degrees.terminalDegree i₀ p d.val)
          out(p, d.val) v ν ε q : Type _),
          if X ∈ domain(p.comp q, (Path.degreesComp (ι := ι) p q).symm (d.val, e.val))
          then q.homogeneousHistory T ℳ e.val out(p, d.val) else 0 := by
  rw [sum_pathDecoratedRay_eq_sum_histories]
  convert sum_ite_pathDecoratedHistory_comp T ℳ i₀ x v ν ε p q
    (fun d e => X ∈ domain(p.comp q, (Path.degreesComp (ι := ι) p q).symm (d, e))) using 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [Prod.mk.eta, Equiv.symm_apply_apply]

end Mei
