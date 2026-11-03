/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Chain
import Mathlib.Data.List.OfFn

/-!
# Finite homogeneous propagation histories

Insert a homogeneous projection after each map in a finite sequence of linear
endomorphisms. Each choice of intermediate degrees gives a linear map retaining
whole homogeneous decorations. The maps are indexed backwards: index zero is the
final operation, so the first operation is the rightmost factor. A nonzero final
decoration forces every intermediate decoration to be nonzero.
`homogeneousHistoryStage` records all segment decorations and their component
propagation equations, for attachment to geometric realizations.

A history on one module is the chain history `chainHistory` of the constant
chain (`Mei.LinearAlgebra.GradedModule.History.Chain`). Its finite-support
expansion and regrading comparison specialize to the forms in
`Mei.LinearAlgebra.GradedModule.History.Finite` and `History/Uniform.lean`.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Propagation along a chosen homogeneous degree history. Index zero records
its final component; the empty history leaves the input unchanged. It is the
chain history of the constant chain on `M`. -/
def homogeneousHistory {n : ℕ} (T : Fin n → Module.End R M) (p : Fin n → ι) :
    Module.End R M :=
  chainHistory (M := fun _ => M) (ι := fun _ => ι) (fun _ => ℳ) T p

/-- A single-module history is the history of the constant chain. -/
theorem homogeneousHistory_eq_chainHistory {n : ℕ} (T : Fin n → Module.End R M)
    (p : Fin n → ι) :
    homogeneousHistory ℳ T p =
      chainHistory (M := fun _ => M) (ι := fun _ => ι) (fun _ => ℳ) T p :=
  (rfl)

/-- No propagation steps give the identity map. -/
@[simp]
theorem homogeneousHistory_zero (T : Fin 0 → Module.End R M) (p : Fin 0 → ι) :
    homogeneousHistory ℳ T p = LinearMap.id :=
  chainHistory_zero (fun _ => ℳ) T p

/-- One more history entry applies its map and selects the entire output component. -/
@[simp]
theorem homogeneousHistory_succ_apply {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) (a : M) :
    homogeneousHistory ℳ T p a =
      (DirectSum.decompose ℳ (T 0
        (homogeneousHistory ℳ (fun j : Fin n => T j.succ) (fun j => p j.succ) a)) (p 0) : M) :=
  chainHistory_succ_apply (fun _ => ℳ) T p a

/-- The output of a nonempty history lies in its last selected homogeneous piece. -/
theorem homogeneousHistory_mem {n : ℕ} (T : Fin (n + 1) → Module.End R M)
    (p : Fin (n + 1) → ι) (a : M) :
    homogeneousHistory ℳ T p a ∈ ℳ (p 0) := by
  rw [homogeneousHistory_succ_apply]
  exact Subtype.property _

/-- A nonempty history has no component in a degree different from its terminal
degree. -/
@[simp]
theorem homogeneousComponent_comp_homogeneousHistory_of_ne {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) (η : ι)
    (hη : p 0 ≠ η) :
    (homogeneousComponent ℳ η).comp (homogeneousHistory ℳ T p) = 0 := by
  rw [homogeneousHistory_eq_chainHistory]
  exact homogeneousComponent_comp_chainHistory_of_ne (fun _ => ℳ) T p η hη

/-- Selecting the terminal degree of a nonempty history returns that history:
the history already ends in the `p 0` selection, which fixes its output. -/
@[simp]
theorem homogeneousComponent_comp_homogeneousHistory {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) :
    (homogeneousComponent ℳ (p 0)).comp (homogeneousHistory ℳ T p) =
      homogeneousHistory ℳ T p := by
  rw [homogeneousHistory_eq_chainHistory]
  exact homogeneousComponent_comp_chainHistory (fun _ => ℳ) T p

/-- The final `η`-selection of a nonempty history keeps it when `η` is the
terminal degree and kills it otherwise. -/
theorem homogeneousComponent_homogeneousHistory_apply {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) (η : ι) (a : M) :
    homogeneousComponent ℳ η (homogeneousHistory ℳ T p a) =
      if p 0 = η then homogeneousHistory ℳ T p a else 0 := by
  rw [homogeneousHistory_eq_chainHistory]
  exact homogeneousComponent_chainHistory_apply (fun _ => ℳ) T p η a

/-- A vanished intermediate decoration cannot yield a nonzero final history. -/
theorem homogeneousHistory_tail_ne_zero {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) {a : M}
    (ha : homogeneousHistory ℳ T p a ≠ 0) :
    homogeneousHistory ℳ (fun j : Fin n => T j.succ) (fun j => p j.succ) a ≠ 0 := by
  intro hz
  apply ha
  simp [hz]

/-- A homogeneous history is the ordered product of its one-step component maps.
The step with index zero acts last. -/
theorem homogeneousHistory_eq_prod {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) :
    homogeneousHistory ℳ T p =
      (List.ofFn fun j => homogeneousHistory ℳ (fun _ : Fin 1 => T j)
        (fun _ => p j)).prod := by
  induction n with
  | zero => ext a; simp
  | succ n ih =>
    ext a
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, ← ih]
    simp only [homogeneousHistory_succ_apply, homogeneousHistory_zero,
      LinearMap.id_apply]

/-- Concatenating degree histories composes their component propagation maps.
The right block acts first, in accordance with the backward indexing. -/
@[simp]
theorem homogeneousHistory_append {n m : ℕ}
    (T : Fin n → Module.End R M) (U : Fin m → Module.End R M)
    (p : Fin n → ι) (q : Fin m → ι) :
    homogeneousHistory ℳ (Fin.append T U) (Fin.append p q) =
      (homogeneousHistory ℳ T p).comp (homogeneousHistory ℳ U q) := by
  rw [homogeneousHistory_eq_prod, homogeneousHistory_eq_prod ℳ T p,
    homogeneousHistory_eq_prod ℳ U q]
  have he : (fun j => homogeneousHistory ℳ (fun _ : Fin 1 => Fin.append T U j)
      (fun _ => Fin.append p q j)) =
      Fin.append (fun j => homogeneousHistory ℳ (fun _ : Fin 1 => T j) (fun _ => p j))
        (fun j => homogeneousHistory ℳ (fun _ : Fin 1 => U j) (fun _ => q j)) := by
    funext j
    exact Fin.addCases (by intro i; simp) (by intro i; simp) j
  rw [he, List.ofFn_fin_append, List.prod_append]
  rfl

/-- A nonzero concatenated history forces the entire first block to survive,
even when the later block kills other intermediate decorations. -/
theorem homogeneousHistory_right_ne_zero {n m : ℕ}
    (T : Fin n → Module.End R M) (U : Fin m → Module.End R M)
    (p : Fin n → ι) (q : Fin m → ι) {a : M}
    (ha : homogeneousHistory ℳ (Fin.append T U) (Fin.append p q) a ≠ 0) :
    homogeneousHistory ℳ U q a ≠ 0 := by
  rw [homogeneousHistory_append, LinearMap.comp_apply] at ha
  exact fun hz => ha (by rw [hz, map_zero])

/-- The whole decoration on every segment of a homogeneous history, in backward
order. The last segment carries the input, and segment zero carries the output. -/
def homogeneousHistoryStage : {n : ℕ} → (Fin n → Module.End R M) →
    (Fin n → ι) → Fin (n + 1) → Module.End R M
  | 0, _, _ => fun _ => LinearMap.id
  | n + 1, T, p => Fin.cons (homogeneousHistory ℳ T p)
      (homogeneousHistoryStage (fun j : Fin n => T j.succ) (fun j => p j.succ))

/-- The terminal segment carries the final whole component. -/
@[simp]
theorem homogeneousHistoryStage_zero {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) :
    homogeneousHistoryStage ℳ T p 0 = homogeneousHistory ℳ T p := by
  cases n with
  | zero => exact (homogeneousHistory_zero ℳ T p).symm
  | succ => rfl

/-- Removing the terminal segment removes the last propagation step. -/
@[simp]
theorem homogeneousHistoryStage_succ {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T p j.succ =
      homogeneousHistoryStage ℳ (fun j => T j.succ) (fun j => p j.succ) j := (rfl)

/-- Discarding the final `m` propagation steps preserves every earlier segment
map. The retained maps keep their backward order. -/
@[simp]
theorem homogeneousHistoryStage_natAdd {m n : ℕ}
    (T : Fin (m + n) → Module.End R M) (p : Fin (m + n) → ι)
    (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T p (Fin.natAdd m j) =
      homogeneousHistoryStage ℳ (fun i => T (Fin.natAdd m i))
        (fun i => p (Fin.natAdd m i)) j := by
  have transport {s t : ℕ} (h : s = t)
      (T : Fin s → Module.End R M) (p : Fin s → ι) (i : Fin (s + 1)) :
      homogeneousHistoryStage ℳ T p i =
        homogeneousHistoryStage ℳ (fun j => T (j.cast h.symm))
          (fun j => p (j.cast h.symm)) (i.cast (congrArg (· + 1) h)) := by
    subst t
    rfl
  induction m with
  | zero =>
    rw [transport (Nat.zero_add n)]
    congr 1
    · funext i; congr 1; apply Fin.ext; simp
    · funext i; congr 1; apply Fin.ext; simp
    · apply Fin.ext; simp
  | succ m ih =>
    rw [transport (Nat.succ_add m n)]
    have hi : (Fin.natAdd (m + 1) j).cast
        (congrArg (· + 1) (Nat.succ_add m n)) = (Fin.natAdd m j).succ := by
      ext
      simp [Nat.succ_add]
    rw [hi, homogeneousHistoryStage_succ, ih]
    congr 1 <;> funext i <;> congr 1 <;> apply Fin.ext <;> simp [Nat.succ_add]

/-- The incoming segment carries the original input. -/
@[simp]
theorem homogeneousHistoryStage_last {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) :
    homogeneousHistoryStage ℳ T p (Fin.last n) = LinearMap.id := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun j => T j.succ) (fun j => p j.succ)

/-- At an encounter the entire output component of its propagation map is
retained. Adjacent segments may have the same degree. -/
theorem homogeneousHistoryStage_castSucc_apply {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) (j : Fin n) (a : M) :
    homogeneousHistoryStage ℳ T p j.castSucc a =
      (DirectSum.decompose ℳ (T j (homogeneousHistoryStage ℳ T p j.succ a)) (p j) : M) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.castSucc_zero, homogeneousHistoryStage_zero,
        homogeneousHistoryStage_succ] using homogeneousHistory_succ_apply ℳ T p a
    · exact ih (fun j => T j.succ) (fun j => p j.succ) j

/-- A surviving final decoration forces every segment decoration to survive. -/
theorem homogeneousHistoryStage_ne_zero {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) {a : M}
    (ha : homogeneousHistory ℳ T p a ≠ 0) (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T p j a ≠ 0 := by
  induction n with
  | zero =>
    rw [homogeneousHistory_zero] at ha
    exact ha
  | succ n ih =>
    refine Fin.cases ha (fun j => ?_) j
    exact ih (fun j => T j.succ) (fun j => p j.succ)
      (homogeneousHistory_tail_ne_zero ℳ T p ha) j

/-- Every selected segment decoration lies in its recorded homogeneous piece. -/
theorem homogeneousHistoryStage_mem {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) (a : M) (j : Fin n) :
    homogeneousHistoryStage ℳ T p j.castSucc a ∈ ℳ (p j) := by
  rw [homogeneousHistoryStage_castSucc_apply]
  exact Subtype.property _

/-- All segment decorations are homogeneous in the recorded degrees, including
the incoming degree appended after the selected output degrees. -/
theorem homogeneousHistoryStage_mem_snoc {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) (p₀ : ι) (a : ℳ p₀)
    (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T p j a ∈ ℳ (Fin.snoc (α := fun _ => ι) p p₀ j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [Fin.snoc_last, homogeneousHistoryStage_last, LinearMap.id_apply] using a.property
  · simpa only [Fin.snoc_castSucc] using homogeneousHistoryStage_mem ℳ T p a i

/-- The whole output of a history, bundled in its homogeneous piece. For the
empty history the piece is the incoming one. -/
def homogeneousHistoryResult {n : ℕ} (T : Fin n → Module.End R M)
    (p : Fin n → ι) {p₀ : ι} (a : ℳ p₀) :
    ℳ (Fin.snoc (α := fun _ => ι) p p₀ 0) :=
  ⟨homogeneousHistory ℳ T p a, by
    simpa only [homogeneousHistoryStage_zero] using
      homogeneousHistoryStage_mem_snoc ℳ T p p₀ a 0⟩

/-- Forgetting the output piece gives the original whole history decoration. -/
@[simp]
theorem coe_homogeneousHistoryResult {n : ℕ} (T : Fin n → Module.End R M)
    (p : Fin n → ι) {p₀ : ι} (a : ℳ p₀) :
    (homogeneousHistoryResult ℳ T p a : M) = homogeneousHistory ℳ T p a := (rfl)

/-- Any relation satisfied by the input and nonzero output degrees of each
propagation map holds at every step of a surviving homogeneous history,
including the step adjacent to the incoming coefficient. -/
theorem homogeneousHistory_rel_of_ne_zero {n : ℕ}
    (T : Fin n → Module.End R M) {P : Fin n → ι → ι → Prop}
    (hP : ∀ j p q (x : M), x ∈ ℳ p →
      DirectSum.decompose ℳ (T j x) q ≠ 0 → P j q p)
    (r : Fin n → ι) (r₀ : ι) (a : ℳ r₀)
    (hne : homogeneousHistory ℳ T r a ≠ 0) (j : Fin n) :
    P j (r j) (Fin.snoc (α := fun _ => ι) r r₀ j.succ) := by
  apply hP j _ _ _ (homogeneousHistoryStage_mem_snoc ℳ T r r₀ a j.succ)
  intro hz
  apply homogeneousHistoryStage_ne_zero ℳ T r hne j.castSucc
  rw [homogeneousHistoryStage_castSucc_apply]
  exact congrArg Subtype.val hz

section Regrading

variable {N κ : Type*} [AddCommMonoid N] [Module R N] [DecidableEq κ]
  (𝓝 : κ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : ι → κ)
  (hr : ∀ i x, x ∈ ℳ i → r x ∈ 𝓝 (σ i))

include hr

/-- Along an injective map of degrees, an intertwining coefficient map sends
each whole homogeneous history to the history with the reindexed degrees. -/
theorem map_homogeneousHistory_of_injective (hσ : Function.Injective σ) {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r) (p : Fin n → ι) (a : M) :
    r (homogeneousHistory ℳ T p a) = homogeneousHistory 𝓝 U (σ ∘ p) (r a) :=
  map_chainHistory_of_injective (fun _ => ℳ) (fun _ => 𝓝) (fun _ => r) (fun _ => σ)
    (fun _ => hr) (fun _ => hσ) T U hT p a

end Regrading

end Mei
