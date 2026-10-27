/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Completions of filtered modules

The completion of a decreasing module filtration is the module of compatible
families in its quotient tower. It has linear projections and a universal lift
of compatible linear maps, giving a limit cone in `ModuleCat`. The induced
filtration is separated, and the canonical map preserves and reflects each
filtration term; its kernel is the intersection of the original terms.

The carrier uses Mathlib's `ModuleCat.sectionsSubmodule`; tower transitions use
`Submodule.factor`. No finiteness or separatedness of the original module is
required. These completions support formal coefficient modules with arbitrary
submodule filtrations, rather than only filtrations by powers of one ideal.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace Mei.ModuleFiltration

universe u v
variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M)

/-- The order-`k` quotient retains terms through order `k`. -/
abbrev quotient (k : ℕ) := M ⧸ F.submodule (k + 1)

/-- The transition from a finer quotient to a coarser quotient. -/
def transition {k l : ℕ} (h : k ≤ l) : F.quotient l →ₗ[R] F.quotient k :=
  Submodule.factor (F.antitone (Nat.add_le_add_right h 1))

@[simp]
lemma transition_mk {k l : ℕ} (h : k ≤ l) (x : M) :
    F.transition h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  (rfl)

@[simp]
lemma transition_refl (k : ℕ) : F.transition (le_refl k) = LinearMap.id := by
  ext x
  simp [transition, Submodule.factor]

@[simp]
lemma transition_comp {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m) :
    (F.transition h).comp (F.transition h') = F.transition (h.trans h') :=
  Submodule.factor_comp (F.antitone (Nat.add_le_add_right h' 1))
    (F.antitone (Nat.add_le_add_right h 1))

/-- The quotient tower as a functor on opposite natural numbers. -/
@[expose]
def quotientTower : ℕᵒᵖ ⥤ ModuleCat.{v} R where
  obj k := ModuleCat.of R (F.quotient k.unop)
  map f := ModuleCat.ofHom (F.transition (leOfHom f.unop))
  map_id k := by
    apply ModuleCat.hom_ext
    exact F.transition_refl k.unop
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (F.transition_comp (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The compatible-family submodule of the product of the quotient tower. -/
def completionSubmodule : Submodule R (∀ k : ℕᵒᵖ, F.quotient k.unop) :=
  ModuleCat.sectionsSubmodule F.quotientTower

/-- A family belongs to the completion exactly when all its transitions agree. -/
@[simp]
lemma mem_completionSubmodule_iff (x : ∀ k : ℕᵒᵖ, F.quotient k.unop) :
    x ∈ F.completionSubmodule ↔
      ∀ k l (h : k ≤ l), F.transition h (x (Opposite.op l)) = x (Opposite.op k) := by
  constructor
  · intro hx k l h
    exact hx (homOfLE h).op
  · intro hx k l g
    exact hx l.unop k.unop (leOfHom g.unop)

/-- The module completion, as compatible quotient families. -/
abbrev completion := F.completionSubmodule

/-- Projection from the completion to its order-`k` quotient. -/
def projection (k : ℕ) : F.completion →ₗ[R] F.quotient k :=
  (LinearMap.proj (Opposite.op k)).comp F.completionSubmodule.subtype

@[simp]
lemma projection_mk (x : ∀ k : ℕᵒᵖ, F.quotient k.unop)
    (hx : x ∈ F.completionSubmodule) (k : ℕ) :
    F.projection k ⟨x, hx⟩ = x (Opposite.op k) :=
  (rfl)

/-- Projections of a completed element form a compatible family. -/
@[simp]
lemma transition_projection {k l : ℕ} (h : k ≤ l) (x : F.completion) :
    F.transition h (F.projection l x) = F.projection k x :=
  x.property (homOfLE h).op

@[ext]
lemma completion_ext {x y : F.completion}
    (h : ∀ k, F.projection k x = F.projection k y) : x = y := by
  apply Subtype.ext
  funext k
  exact h k.unop

variable {X : Type*} [AddCommGroup X] [Module R X]

/-- Lift a compatible family of linear maps to the completion. -/
def lift (f : ∀ k, X →ₗ[R] F.quotient k)
    (hf : ∀ k l (h : k ≤ l), (F.transition h).comp (f l) = f k) :
    X →ₗ[R] F.completion :=
  (LinearMap.pi fun k : ℕᵒᵖ => f k.unop).codRestrict F.completionSubmodule
    (fun x _ _ g => LinearMap.congr_fun (hf _ _ (leOfHom g.unop)) x)

@[simp]
lemma projection_lift (f : ∀ k, X →ₗ[R] F.quotient k)
    (hf : ∀ k l (h : k ≤ l), (F.transition h).comp (f l) = f k) (k : ℕ) (x : X) :
    F.projection k (F.lift f hf x) = f k x :=
  (rfl)

/-- The universal lift is the unique map with the specified projections. -/
lemma lift_unique (f : ∀ k, X →ₗ[R] F.quotient k)
    (hf : ∀ k l (h : k ≤ l), (F.transition h).comp (f l) = f k)
    (g : X →ₗ[R] F.completion) (hg : ∀ k, (F.projection k).comp g = f k) :
    g = F.lift f hf := by
  ext x k
  exact LinearMap.congr_fun (hg k) x

/-- The canonical linear map into the completion. -/
def of : M →ₗ[R] F.completion :=
  F.lift (fun k => (F.submodule (k + 1)).mkQ) (by
    intro k l h
    ext x
    exact F.transition_mk h x)

@[simp]
lemma projection_of (k : ℕ) (x : M) :
    F.projection k (F.of x) = Submodule.Quotient.mk x :=
  (rfl)

/-- The cone of completion projections over the quotient tower. -/
def completionCone : Cone F.quotientTower where
  pt := ModuleCat.of R F.completion
  π :=
    { app := fun k => ModuleCat.ofHom (F.projection k.unop)
      naturality := fun _ _ g => by
        ext x
        exact (F.transition_projection (leOfHom g.unop) x).symm }

/-- The vertex of the completion cone is the completed module. -/
@[simp]
lemma completionCone_pt : F.completionCone.pt = ModuleCat.of R F.completion :=
  (rfl)

/-- The components of the completion cone are the quotient projections. -/
@[simp]
lemma completionCone_π_app (k : ℕᵒᵖ) :
    F.completionCone.π.app k =
      eqToHom F.completionCone_pt ≫ ModuleCat.ofHom (F.projection k.unop) :=
  (rfl)

/-- The compatible-family completion is the inverse limit of its quotient tower. -/
def completionIsLimit : IsLimit F.completionCone where
  lift s := ModuleCat.ofHom (F.lift (fun k => (s.π.app (Opposite.op k)).hom)
    (fun k l h => by
      ext x
      exact congrArg (fun f => f x) (s.w (homOfLE h).op)))
  fac s k := by ext x; rfl
  uniq s m hm := by
    apply ModuleCat.hom_ext
    ext x
    apply F.completion_ext
    intro k
    exact congrArg (fun f => f x) (hm (Opposite.op k))

/-- The compatible-family completion is canonically isomorphic to the chosen categorical limit. -/
noncomputable def completionIsoLimit : ModuleCat.of R F.completion ≅ limit F.quotientTower :=
  F.completionIsLimit.conePointUniqueUpToIso (limit.isLimit F.quotientTower)

/-- The canonical limit comparison identifies its projections with quotient projections. -/
@[reassoc (attr := simp)]
lemma completionIsoLimit_hom_π (k : ℕᵒᵖ) :
    F.completionIsoLimit.hom ≫ limit.π F.quotientTower k =
      ModuleCat.ofHom (F.projection k.unop) := by
  exact F.completionIsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit F.quotientTower) k

/-- The inverse comparison recovers the quotient components of a categorical limit element. -/
@[reassoc (attr := simp)]
lemma completionIsoLimit_inv_projection (k : ℕᵒᵖ) :
    F.completionIsoLimit.inv ≫ ModuleCat.ofHom (F.projection k.unop) =
      limit.π F.quotientTower k := by
  -- Identify the tower object with the concrete quotient module during reassociation.
  erw [← completionIsoLimit_hom_π, Iso.inv_hom_id_assoc]

/-- The induced filtration: positive orders are kernels of quotient projections. -/
def completedFiltration : ModuleFiltration R F.completion where
  submodule
    | 0 => ⊤
    | k + 1 => LinearMap.ker (F.projection k)
  zero_eq_top := rfl
  antitone := by
    intro a b hab
    cases a with
    | zero => exact le_top
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        intro x hx
        have he := F.transition_projection (Nat.le_of_succ_le_succ hab) x
        rw [LinearMap.mem_ker] at hx ⊢
        rw [← he, hx, map_zero]

@[simp]
lemma completedFiltration_succ (k : ℕ) :
    F.completedFiltration.submodule (k + 1) = LinearMap.ker (F.projection k) :=
  (rfl)

/-- The induced filtration on the completion is separated. -/
@[simp]
lemma iInf_completedFiltration : (⨅ k, F.completedFiltration.submodule k) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply (Submodule.mem_bot R).mpr
  apply F.completion_ext
  intro k
  exact ((Submodule.mem_iInf _).mp hx (k + 1) : F.projection k x = 0)

/-- Representatives of a completed element in a filtration term can be chosen
in that same term at every finer cutoff. -/
theorem exists_projection_eq_of_mem_completedFiltration {a k : ℕ} (hak : a ≤ k + 1)
    {x : F.completion} (hx : x ∈ F.completedFiltration.submodule a) :
    ∃ m ∈ F.submodule a, Submodule.Quotient.mk m = F.projection k x := by
  obtain ⟨m, hm⟩ := (F.submodule (k + 1)).mkQ_surjective (F.projection k x)
  refine ⟨m, ?_, hm⟩
  cases a with
  | zero => simp
  | succ a =>
    rw [completedFiltration_succ, LinearMap.mem_ker] at hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have he := congrArg (F.transition (by omega : a ≤ k)) hm
    rw [Submodule.mkQ_apply, transition_mk, transition_projection] at he
    exact he.trans hx

/-- The canonical map preserves and reflects every filtration order. -/
@[simp]
lemma comap_completedFiltration (k : ℕ) :
    (F.completedFiltration.submodule k).comap F.of = F.submodule k := by
  cases k with
  | zero => simp [F.zero_eq_top]
  | succ k =>
    ext x
    simp [LinearMap.mem_ker]

/-- The kernel of the canonical map consists of elements in every filtration term. -/
lemma ker_of : LinearMap.ker F.of = ⨅ k, F.submodule k := by
  calc
    LinearMap.ker F.of = (⨅ k, F.completedFiltration.submodule k).comap F.of := by
      rw [F.iInf_completedFiltration, Submodule.comap_bot]
    _ = ⨅ k, F.submodule k := by
      simp only [Submodule.comap_iInf, F.comap_completedFiltration]

/-- The canonical map is injective exactly when the original filtration is separated. -/
lemma of_injective_iff : Function.Injective F.of ↔ (⨅ k, F.submodule k) = ⊥ := by
  rw [← LinearMap.ker_eq_bot, F.ker_of]

end Mei.ModuleFiltration
