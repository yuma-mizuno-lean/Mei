/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Basic
public import Mei.LinearAlgebra.GradedModule.History.Path.Insertion
public import Mei.Geometry.Convex.Sweep.Admissible.Insertion

/-!
# Identity encounters between varying-chamber propagation blocks

Restore an identity encounter between two arbitrary chamber itineraries. The
shared history construction repeats the intermediate degree, and geometric
insertion retains the entire ray and its incoming tail. The added support joins
the obstacle family: every unrecorded hit must be excluded, including on the
unbounded incoming half-line. All previous encounters remain recorded even when
their degrees or spatial directions agree.

The construction combines `Quiver.Path.degreesRepeat` with
`AdmissibleRayRealization.insertEncounter`. Identity propagation is required on
the intermediate chamber only; the remaining chamber modules, degree types and
transfer maps may differ. The broken-line conventions follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei.PathDecoratedRay

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  {T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c}
  {ℳ : ∀ q, ι q → Submodule R (M q)} [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b z : Q} {i₀ : ι a} {x : ℳ a i₀}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {v : ∀ q, ι q → V}
  {ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ}
  {ε : ∀ {b c : Q}, (b ⟶ c) → SignType}
  {c : ∀ {b c : Q}, (b ⟶ c) → ℝ}
  {P : ∀ {b c : Q}, (b ⟶ c) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {X : V}
  {p : Path a b} {q : Path b z}
  (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C (p.comp q) X)
  (e : b ⟶ b) (he : T e = LinearMap.id)

local notation "pos" => Path.insertionIndex p q
local notation "dirs" => Path.Degrees.reverseVertexLabels v i₀ (p.comp q)
  (Subtype.val (Sigma.fst r))
local notation "newPath" => Path.comp (Path.cons p e) q
local notation "newD" => Path.degreesRepeat p q e i₀ (Subtype.val (Sigma.fst r))
local notation "newDirs" => Path.Degrees.reverseVertexLabels v i₀ newPath newD

include he in
/-- Repeating the degree at an identity encounter preserves the normal rules
when the new coorientation records its actual crossing sign. -/
private theorem degreesRepeat_mem_pathDecoratedHistorySupport
    (hε : ε e = SignType.sign (ν e (dirs pos))) :
    newD ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε newPath := by
  have hν := Path.reverseArrowLabels_insertLoop ν p e q
  have hv := Path.Degrees.reverseVertexLabels_degreesRepeat v p e i₀ q r.1.val
  have hsign := Path.reverseArrowLabels_insertLoop ε p e q
  have hold := (mem_pathDecoratedHistorySupport T ℳ i₀ x v ν ε (p.comp q) r.1.val).mp
    r.1.property
  have hraw : ∀ j,
      ((pos).insertNth (α := fun _ => V →L[ℝ] ℝ) (ν e) ((p.comp q).reverseArrowLabels ν)) j
          (((pos).succ.insertNth (α := fun _ => V) (dirs pos) dirs) j.castSucc) =
        ((pos).insertNth (α := fun _ => V →L[ℝ] ℝ) (ν e) ((p.comp q).reverseArrowLabels ν)) j
          (((pos).succ.insertNth (α := fun _ => V) (dirs pos) dirs) j.succ) ∧
      SignType.sign (((pos).insertNth (α := fun _ => V →L[ℝ] ℝ) (ν e)
          ((p.comp q).reverseArrowLabels ν)) j
          (((pos).succ.insertNth (α := fun _ => V) (dirs pos) dirs) j.castSucc)) =
        ((pos).insertNth (α := fun _ => SignType) (ε e) ((p.comp q).reverseArrowLabels ε)) j := by
    intro j
    rw [Fin.insertNth_succ_castSucc]
    cases j using Fin.succAboveCases pos with
    | x => simp [hε]
    | p j =>
      simpa only [Fin.insertNth_apply_succAbove, ← Fin.succ_succAbove_succ] using hold.2 j
  apply (mem_pathDecoratedHistorySupport T ℳ i₀ x v ν ε newPath newD).mpr
  refine ⟨?_, ?_⟩
  · rw [Path.homogeneousHistory_degreesRepeat T ℳ p q e he i₀ _ x.property]
    exact hold.1
  · intro j
    obtain ⟨j, rfl⟩ := (finCongr (Path.length_insertLoop p q e).symm).surjective j
    have hv₀ := congrFun hv j.castSucc
    have hv₁ := congrFun hv j.succ
    have hn := congrFun hν j
    have hs := congrFun hsign j
    simpa only [← hv₀, ← hv₁, ← hn, ← hs, finCongr_apply, Fin.cast_castSucc,
      Fin.cast_succ_eq] using hraw j

variable (t : ℝ) (hbefore : t < r.2.parameter (Path.insertionIndex p q))
  (hafter : ∀ j, Path.insertionIndex p q < j → r.2.parameter j < t)
  (htrans : ν e (Path.Degrees.reverseVertexLabels v i₀ (p.comp q) r.1.val
    (Path.insertionIndex p q)) ≠ 0) (hheight : ν e (r.2.ray t) = c e)
  (hinc : r.2.ray t ∈ P e)
  (havoid : ∀ s, s < 0 → s ≠ t →
    (∀ j : Fin (p.comp q).length, s ≠ r.2.parameter j.succ) → r.2.ray s ∉ P e)
  (hoff : X ∉ P e) (hε : ε e = SignType.sign (ν e
    (Path.Degrees.reverseVertexLabels v i₀ (p.comp q) r.1.val (Path.insertionIndex p q))))

include hbefore hafter htrans hε in
/-- Restore an identity encounter between arbitrary varying-chamber blocks.
The support joins the obstacles, while the path and original incoming source
are retained. No invertibility of the other transfers is required. -/
def insertIdentityEncounter :
    PathDecoratedRay T ℳ i₀ x v ν ε c P (Sum.elim W (fun _ : Unit => P e)) S C newPath X := by
  let g := r.2.insertEncounter pos t hbefore hafter (ν e) (c e) (P e)
    htrans hheight hinc havoid hoff
  refine ⟨⟨newD, degreesRepeat_mem_pathDecoratedHistorySupport r e he hε⟩, ?_⟩
  exact g.congrLength (Path.length_insertLoop p q e).symm
    ((newPath).reverseArrowLabels ν) ((newPath).reverseArrowLabels c) newDirs
    ((newPath).reverseArrowLabels P)
    (fun j => (congrFun (Path.reverseArrowLabels_insertLoop ν p e q) j).symm)
    (fun j => (congrFun (Path.reverseArrowLabels_insertLoop c p e q) j).symm)
    (fun j => (congrFun
      (Path.Degrees.reverseVertexLabels_degreesRepeat v p e i₀ q r.1.val) j).symm)
    (fun j => (congrFun (Path.reverseArrowLabels_insertLoop P p e q) j).symm)

/-- The restored encounter repeats only the intermediate degree. -/
@[simp]
theorem history_insertIdentityEncounter :
    (r.insertIdentityEncounter e he t hbefore hafter htrans hheight hinc havoid hoff hε).1.val =
      newD := (rfl)

/-- The entire path, including the original incoming tail, remains unchanged. -/
@[simp]
theorem ray_insertIdentityEncounter :
    (r.insertIdentityEncounter e he t hbefore hafter htrans hheight hinc havoid hoff hε).2.ray =
      r.2.ray := by
  simp only [insertIdentityEncounter, AdmissibleRayRealization.ray_congrLength,
    AdmissibleRayRealization.ray_insertEncounter]

/-- All old times are retained, and the new time occupies the block boundary.
The cast accounts for the equality of the two encounter counts. -/
@[simp]
theorem parameter_insertIdentityEncounter (j : Fin ((p.comp q).length + 2)) :
    (r.insertIdentityEncounter e he t hbefore hafter htrans hheight hinc havoid hoff hε).2.parameter
        (Fin.cast (congrArg (fun n => n + 1) (Path.length_insertLoop p q e)).symm j) =
      (pos).succ.insertNth (α := fun _ => ℝ) t r.2.parameter j := by
  simp only [insertIdentityEncounter, AdmissibleRayRealization.parameter_congrLength,
    AdmissibleRayRealization.parameter_insertEncounter, Fin.cast_cast, Fin.cast_eq_self]

/-- Identity insertion preserves the whole final decoration in the last
chamber, even if propagation through intermediate chambers kills other histories. -/
@[simp↓]
theorem decoration_insertIdentityEncounter :
    (r.insertIdentityEncounter e he t hbefore hafter htrans hheight hinc havoid
      hoff hε).decoration = r.decoration := by
  rw [decoration_def, history_insertIdentityEncounter, decoration_def,
    Path.homogeneousHistory_degreesRepeat T ℳ p q e he i₀ _ x.property]

include he hbefore hafter hε in
omit htrans hheight hinc havoid hoff in
/-- The geometric admission conditions are necessary and sufficient to restore
an identity encounter with its repeated history, original path and new time.
The prescribed coorientation must have the actual crossing sign. No further
condition on the intermediate coefficient modules is needed. -/
theorem exists_insertIdentityEncounter_iff :
    (∃ s : PathDecoratedRay T ℳ i₀ x v ν ε c P
        (Sum.elim W (fun _ : Unit => P e)) S C newPath X,
      s.1.val = newD ∧ s.2.ray = r.2.ray ∧
        ∀ j : Fin ((p.comp q).length + 2), s.2.parameter
          (Fin.cast (congrArg (fun n => n + 1) (Path.length_insertLoop p q e)).symm j) =
            (pos).succ.insertNth (α := fun _ => ℝ) t r.2.parameter j) ↔
      ν e (dirs pos) ≠ 0 ∧ ν e (r.2.ray t) = c e ∧ r.2.ray t ∈ P e ∧
        (∀ s, s < 0 → s ≠ t →
          (∀ j : Fin (p.comp q).length, s ≠ r.2.parameter j.succ) → r.2.ray s ∉ P e) ∧
        X ∉ P e := by
  constructor
  · rintro ⟨s, hh, hr, hp⟩
    have hv := Path.Degrees.reverseVertexLabels_degreesRepeat v p e i₀ q r.1.val
    -- Reindex the candidate by the inserted tuple before applying the geometric converse.
    let g₀ := s.2.congrVelocity
      (congrArg (Path.Degrees.reverseVertexLabels v i₀ newPath) hh)
    let g := g₀.congrLength (Path.length_insertLoop p q e)
      ((pos).insertNth (α := fun _ => V →L[ℝ] ℝ) (ν e) ((p.comp q).reverseArrowLabels ν))
      ((pos).insertNth (α := fun _ => ℝ) (c e) ((p.comp q).reverseArrowLabels c))
      ((pos).succ.insertNth (α := fun _ => V) (dirs pos) dirs)
      ((pos).insertNth (α := fun _ => Set V) (P e) ((p.comp q).reverseArrowLabels P))
      (fun j => by
        simpa only [Fin.cast_cast, Fin.cast_eq_self] using
          congrFun (Path.reverseArrowLabels_insertLoop ν p e q)
            (Fin.cast (Path.length_insertLoop p q e) j))
      (fun j => by
        simpa only [Fin.cast_cast, Fin.cast_eq_self] using
          congrFun (Path.reverseArrowLabels_insertLoop c p e q)
            (Fin.cast (Path.length_insertLoop p q e) j))
      (fun j => by
        simpa only [Fin.cast_cast, Fin.cast_eq_self] using congrFun hv
          (Fin.cast (congrArg (fun n => n + 1) (Path.length_insertLoop p q e)) j))
      (fun j => by
        simpa only [Fin.cast_cast, Fin.cast_eq_self] using
          congrFun (Path.reverseArrowLabels_insertLoop P p e q)
            (Fin.cast (Path.length_insertLoop p q e) j))
    apply (r.2.exists_insertEncounter_iff pos t hbefore hafter (ν e) (c e) (P e)).mp
    refine ⟨g, ?_, ?_⟩
    · simpa only [g, g₀, AdmissibleRayRealization.ray_congrLength,
        AdmissibleRayRealization.ray_congrVelocity] using hr
    · funext j
      simpa only [g, g₀, AdmissibleRayRealization.parameter_congrLength,
        AdmissibleRayRealization.parameter_congrVelocity] using hp j
  · rintro ⟨htrans, hheight, hinc, havoid, hoff⟩
    exact ⟨r.insertIdentityEncounter e he t hbefore hafter htrans hheight hinc havoid hoff hε,
      history_insertIdentityEncounter .., ray_insertIdentityEncounter ..,
      fun j => parameter_insertIdentityEncounter r e he t hbefore hafter htrans
        hheight hinc havoid hoff hε j⟩

end Mei.PathDecoratedRay
