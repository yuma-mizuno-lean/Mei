/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mei.Algebra.DirectSum.Degree.Basic
public import Mei.Combinatorics.Quiver.Path.ZeroRuns
public import Mei.LinearAlgebra.GradedModule.History.Path
public import Mei.LinearAlgebra.ModuleFiltration.Basic

/-!
# Encounter bounds with degree-dependent marks

An arrow may have both filtration-preserving and filtration-raising homogeneous
components. Thus marking its entire linear map is too coarse for encounter bounds.
We lift a path and its complete degree history to the quiver of chamber-degree
pairs. Every original encounter remains an arrow of this lift, including encounters
whose input and output degrees agree. A mark depends on the two degrees, without
reference to their spatial velocities.

The lifted path has exactly the original length. Component transfers raising a
nilpotent filtration bound its total weight; a bound on zero-weight runs then
bounds all encounters. The input is homogeneous in its prescribed incoming degree,
and the entire original path and degree history are retained. No truncation of an
incoming history, ring structure, cancellation or freeness assumption is used.
-/

public noncomputable section

namespace Mei

/-- A chamber together with one of its homogeneous degrees. -/
@[ext]
structure GradedVertex {Q : Type*} (ι : Q → Type*) where
  /-- The chamber. -/
  chamber : Q
  /-- The degree in that chamber. -/
  degree : ι chamber

namespace GradedVertex

variable {Q : Type*} [Quiver Q] {ι : Q → Type*}

/-- Each encounter is retained between any chosen source and target degrees. -/
instance : Quiver (GradedVertex ι) where
  Hom b c := b.chamber ⟶ c.chamber

/-- An encounter weight that can distinguish components of the same arrow. -/
def componentWeight (w : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ)
    {b c : GradedVertex ι} (e : b ⟶ c) : ℕ := w e b.degree c.degree

/-- Forget degree labels while retaining every original encounter.
The object map is reducible so equalities of typed paths need no endpoint casts. -/
@[expose, reducible]
def forget : GradedVertex ι ⥤q Q where
  obj b := b.chamber
  map e := e

/-- The weight of an encounter uses its two recorded degrees. -/
@[simp]
theorem componentWeight_apply (w : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ)
    {b c : GradedVertex ι} (e : b ⟶ c) : componentWeight w e = w e b.degree c.degree := (rfl)

/-- Forgetting a graded vertex keeps its chamber. -/
@[simp]
theorem forget_obj (b : GradedVertex ι) : (forget (ι := ι)).obj b = b.chamber := (rfl)

/-- Forgetting a component encounter keeps its arrow label. -/
@[simp]
theorem forget_map {b c : GradedVertex ι} (e : b ⟶ c) :
    (forget (ι := ι)).map e = e := (rfl)

end GradedVertex

section DegreeFiltration

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (rank : ι → ℕ)

/-- The filtration by a natural-valued order of homogeneous pieces. -/
def componentDegreeFiltration : ModuleFiltration R M where
  submodule := DirectSum.degreeTail ℳ (fun i => (rank i : ℤ))
  antitone := DirectSum.degreeTail_antitone ℳ _
  zero_eq_top := DirectSum.degreeTail_zero ℳ _ (fun i hi => by omega)

/-- Each filtration submodule is the corresponding homogeneous degree tail. -/
@[simp]
theorem componentDegreeFiltration_submodule (k : ℕ) :
    (componentDegreeFiltration ℳ rank).submodule k =
      DirectSum.degreeTail ℳ (fun i => (rank i : ℤ)) k := (rfl)

/-- Membership means that all lower-rank homogeneous components vanish. -/
theorem mem_componentDegreeFiltration_iff {k : ℕ} {x : M} :
    x ∈ (componentDegreeFiltration ℳ rank).submodule k ↔
      ∀ i, rank i < k → (_root_.DirectSum.decompose ℳ x i : M) = 0 := by
  rw [componentDegreeFiltration_submodule, DirectSum.mem_degreeTail_iff]
  simp only [Nat.cast_lt]

/-- Vanishing of pieces in order at least `r` makes the degree filtration nilpotent. -/
theorem componentDegreeFiltration_eq_bot {r : ℕ}
    (hr : ∀ i, r ≤ rank i → ℳ i = ⊥) :
    (componentDegreeFiltration ℳ rank).submodule r = ⊥ := by
  apply bot_unique
  rw [componentDegreeFiltration_submodule, DirectSum.degreeTail_def]
  refine iSup_le fun i => iSup_le fun hi => ?_
  rw [hr i (by exact_mod_cast hi)]

end DegreeFiltration

section ComponentTransfers

variable {Q : Type*} [Quiver Q] {ι : Q → Type*}
  {R : Type*} [Semiring R] {M : Q → Type*}
  [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [∀ q, DecidableEq (ι q)]
  {T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c}
  {ℳ : ∀ q, ι q → Submodule R (M q)} [∀ q, DirectSum.Decomposition (ℳ q)]
  {F : ∀ q, ModuleFiltration R (M q)}
  {w : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ}

/-- A degree-dependent component transfer preserves its prescribed weighted
filtration shift on homogeneous inputs. -/
def ComponentTransfersRaise : Prop :=
  ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c) (k : ℕ) (x : M b),
    x ∈ ℳ b i → x ∈ (F b).submodule k →
      homogeneousComponent (ℳ c) j (T e x) ∈ (F c).submodule (k + w e i j)

/-- The component filtration condition on homogeneous inputs. -/
theorem componentTransfersRaise_iff :
    ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := w) ↔
      ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c) (k : ℕ) (x : M b),
        x ∈ ℳ b i → x ∈ (F b).submodule k →
          homogeneousComponent (ℳ c) j (T e x) ∈ (F c).submodule (k + w e i j) := Iff.rfl

/-- Inequalities on surviving component degrees supply the filtration-raising
hypothesis. Zero components need satisfy no inequality. -/
theorem componentTransfersRaise_of_rank (rank : ∀ q, ι q → ℕ)
    (hT : ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c) (x : M b),
      x ∈ ℳ b i → homogeneousComponent (ℳ c) j (T e x) ≠ 0 →
        rank b i + w e i j ≤ rank c j) :
    ComponentTransfersRaise (T := T) (ℳ := ℳ)
      (F := fun q => componentDegreeFiltration (ℳ q) (rank q)) (w := w) := by
  rw [componentTransfersRaise_iff]
  intro b c e i j k x hxi hxF
  by_cases hz : homogeneousComponent (ℳ c) j (T e x) = 0
  · rw [hz]
    exact Submodule.zero_mem _
  have hx : x ≠ 0 := by
    intro hx
    apply hz
    simp only [hx, map_zero]
  have hki : k ≤ rank b i := by
    by_contra hki
    have hzero := (mem_componentDegreeFiltration_iff (ℳ b) (rank b)).mp hxF i
      (Nat.lt_of_not_ge hki)
    rw [DirectSum.decompose_of_mem_same (ℳ b) hxi] at hzero
    exact hx hzero
  rw [componentDegreeFiltration_submodule]
  exact DirectSum.le_degreeTail (ℳ c) (fun j => (rank c j : ℤ))
    (by exact_mod_cast (Nat.add_le_add_right hki (w e i j)).trans (hT e i j x hxi hz))
    (homogeneousComponent_mem (ℳ c) j _)

end ComponentTransfers

end Mei

namespace Quiver.Path

open Mei

variable {Q : Type*} [Quiver Q] {ι : Q → Type*} {a : Q}

/-- The last selected degree, or the prescribed incoming degree for an empty path.
This index is reducible so the degree of a lifted path endpoint reduces without casts. -/
@[expose, reducible]
def Degrees.terminalDegree (i₀ : ι a) : {b : Q} → (p : Path a b) → p.Degrees ι → ι b
  | _, nil, _ => i₀
  | _, cons _ _, d => d.2

/-- The terminal chamber-degree pair of a history with specified incoming degree.
Reducibility keeps the source and target types of encounter arrows definitionally equal. -/
@[expose, reducible]
def Degrees.vertex (i₀ : ι a) {b : Q} (p : Path a b) (d : p.Degrees ι) : GradedVertex ι :=
  ⟨b, Degrees.terminalDegree i₀ p d⟩

/-- The lifted history retains every original encounter and all selected degrees. -/
def Degrees.liftPath (i₀ : ι a) : {b : Q} → (p : Path a b) → (d : p.Degrees ι) →
    Path (⟨a, i₀⟩ : GradedVertex ι) (Degrees.vertex i₀ p d)
  | _, nil, _ => nil
  | _, cons p e, d => (Degrees.liftPath i₀ p d.1).cons e

/-- Empty histories retain the incoming degree. -/
theorem Degrees.terminalDegree_nil (i₀ : ι a) (d : (nil : Path a a).Degrees ι) :
    Degrees.terminalDegree i₀ nil d = i₀ := (rfl)

/-- A nonempty history ends in its last selected degree. -/
theorem Degrees.terminalDegree_cons (i₀ : ι a) {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) :
    Degrees.terminalDegree i₀ (p.cons e) (d, i) = i := (rfl)

/-- The empty lifted history has the prescribed incoming vertex. -/
theorem Degrees.vertex_nil (i₀ : ι a) (d : (nil : Path a a).Degrees ι) :
    Degrees.vertex i₀ nil d = ⟨a, i₀⟩ := (rfl)

/-- Appending a degree gives the corresponding terminal vertex. -/
theorem Degrees.vertex_cons (i₀ : ι a) {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) :
    Degrees.vertex i₀ (p.cons e) (d, i) = ⟨c, i⟩ := (rfl)

/-- An empty degree history lifts to an empty path. -/
@[simp]
theorem Degrees.liftPath_nil (i₀ : ι a) (d : (nil : Path a a).Degrees ι) :
    Degrees.liftPath i₀ nil d = nil := (rfl)

/-- Every selected component appends exactly its original encounter. -/
@[simp]
theorem Degrees.liftPath_cons (i₀ : ι a) {b c : Q} (p : Path a b) (e : b ⟶ c)
    (d : p.Degrees ι) (i : ι c) :
    Degrees.liftPath i₀ (p.cons e) (d, i) = (Degrees.liftPath i₀ p d).cons e := (rfl)

/-- A component encounter adds its degree-dependent weight to the lifted history. -/
theorem Degrees.addWeight_componentWeight_liftPath_cons
    (w : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ) (i₀ : ι a)
    {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι) (i : ι c) :
    addWeight (GradedVertex.componentWeight w) (Degrees.liftPath i₀ (p.cons e) (d, i)) =
      addWeight (GradedVertex.componentWeight w) (Degrees.liftPath i₀ p d) +
        w e (Degrees.terminalDegree i₀ p d) i := by
  rw [Degrees.liftPath_cons, addWeight_cons, GradedVertex.componentWeight_apply]

/-- Lifting a history neither inserts nor removes encounters. -/
@[simp]
theorem Degrees.length_liftPath (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι), (Degrees.liftPath i₀ p d).length = p.length
  | _, nil, _ => (rfl)
  | _, cons p e, d => by
    rw [Degrees.liftPath_cons, length_cons, Degrees.length_liftPath, length_cons]

/-- Forgetting the lift gives exactly the original path, including repeated arrows. -/
@[simp]
theorem Degrees.mapPath_liftPath (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      (GradedVertex.forget (ι := ι)).mapPath (Degrees.liftPath i₀ p d) = p
  | _, nil, _ => (rfl)
  | _, cons p e, d => by
    rw [Degrees.liftPath_cons, Prefunctor.mapPath_cons, Degrees.mapPath_liftPath,
      GradedVertex.forget_map]

/-- Weights independent of the selected degrees have the same sum on a history
lift as on the original encounter path. -/
@[simp]
theorem Degrees.addWeight_componentWeight_liftPath
    (w : ∀ {b c : Q}, (b ⟶ c) → ℕ) (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      addWeight (GradedVertex.componentWeight (fun e _ _ => w e))
        (Degrees.liftPath i₀ p d) = addWeight w p
  | _, nil, _ => by simp only [Degrees.liftPath_nil, addWeight_nil]
  | _, cons p e, d => by
    rw [Degrees.liftPath_cons, addWeight_cons, GradedVertex.componentWeight_apply,
      Degrees.addWeight_componentWeight_liftPath, addWeight_cons]

section Filtration

variable {R : Type*} [Semiring R] {M : Q → Type*}
  [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [∀ q, DecidableEq (ι q)]
  {T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c}
  {ℳ : ∀ q, ι q → Submodule R (M q)} [∀ q, DirectSum.Decomposition (ℳ q)]
  {F : ∀ q, ModuleFiltration R (M q)}
  {w : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ}

/-- The selected output remains homogeneous, including the unchanged incoming
piece when the path is empty. -/
theorem homogeneousHistory_mem_vertex {b : Q} (p : Path a b)
    (d : p.Degrees ι) (i₀ : ι a) (x : M a) (hx : x ∈ ℳ a i₀) :
    p.homogeneousHistory T ℳ d x ∈ ℳ b (Degrees.terminalDegree i₀ p d) := by
  cases p with
  | nil =>
    simpa only [homogeneousHistory_nil, LinearMap.id_apply, Degrees.terminalDegree_nil] using hx
  | cons p e => exact homogeneousHistory_cons_mem T ℳ p e d.1 d.2 x

/-- Every complete homogeneous history lies in the filtration step counted by
its lifted component weights. No intermediate encounter is deleted. -/
theorem homogeneousHistory_apply_mem_submodule_addWeight :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι)
      (_hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := w))
      (i₀ : ι a) (x : M a),
      x ∈ ℳ a i₀ → p.homogeneousHistory T ℳ d x ∈
        (F b).submodule (addWeight (GradedVertex.componentWeight w) (Degrees.liftPath i₀ p d))
  | _, nil, _, _, _, x, _ => by
    rw [Degrees.liftPath_nil, addWeight_nil, ModuleFiltration.zero_eq_top]
    exact Submodule.mem_top
  | _, cons p e, d, hT, i₀, x, hx => by
    obtain ⟨d, j⟩ := d
    rw [homogeneousHistory_cons, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [Degrees.addWeight_componentWeight_liftPath_cons]
    exact (componentTransfersRaise_iff.mp hT) e _ j _ _ (homogeneousHistory_mem_vertex p d i₀ x hx)
      (homogeneousHistory_apply_mem_submodule_addWeight p d hT i₀ x hx)

/-- A surviving history has fewer marked components than the vanishing order.
Weights may depend on both degrees of each encounter. -/
theorem componentWeight_lt_of_homogeneousHistory_ne_zero {b : Q} (p : Path a b)
    (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := w))
    (i₀ : ι a) {d : p.Degrees ι} {x : M a} {r : ℕ}
    (hx : x ∈ ℳ a i₀) (hr : (F b).submodule r = ⊥)
    (hne : p.homogeneousHistory T ℳ d x ≠ 0) :
    addWeight (GradedVertex.componentWeight w) (Degrees.liftPath i₀ p d) < r := by
  by_contra hlt
  have hmem := (F b).antitone (not_lt.mp hlt)
    (homogeneousHistory_apply_mem_submodule_addWeight p d hT i₀ x hx)
  rw [hr] at hmem
  exact hne ((Submodule.mem_bot R).mp hmem)

/-- Degree-dependent marks and a bound on intervening unmarked encounters give
the same encounter bound as arrow-dependent marks. Complete histories and the
incoming homogeneous degree are retained. -/
theorem length_add_one_le_of_homogeneousHistory_ne_zero {b : Q} (p : Path a b)
    (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := w))
    (i₀ : ι a) {d : p.Degrees ι} {x : M a} {r h : ℕ}
    (hx : x ∈ ℳ a i₀) (hr : (F b).submodule r = ⊥)
    (hne : p.homogeneousHistory T ℳ d x ≠ 0)
    (hp : IsZeroRunBounded (GradedVertex.componentWeight w) h (Degrees.liftPath i₀ p d)) :
    p.length + 1 ≤ r * (h + 1) := by
  rw [← Degrees.length_liftPath i₀ p d]
  exact (length_add_one_le_of_isZeroRunBounded hp).trans
    (Nat.mul_le_mul_right _ (componentWeight_lt_of_homogeneousHistory_ne_zero p hT i₀ hx hr hne))

end Filtration

end Quiver.Path
