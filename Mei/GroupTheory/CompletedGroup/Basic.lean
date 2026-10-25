/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Completed groups of towers

The completed group of a tower of groups consists of compatible families, indexed by natural
numbers. Its projections exhibit it as the inverse limit. Their kernels give a decreasing,
separated filtration, with the whole group at degree zero.

The carrier is the preimage of Mathlib's `GrpCat.sectionsSubgroup` under reindexing from
natural numbers to their opposite category. The categorical comparison uses
`GrpCat.limitConeIsLimit`. The proof of surjectivity at every order extends the recursive
preimage construction of `CategoryTheory.Limits.Types.surjective_π_app_zero_of_surjective_map`
to a tail starting at the specified order.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Mei

/-- The compatible-family subgroup of a tower, indexed by natural numbers. -/
def completedGroup (F : ℕᵒᵖ ⥤ GrpCat.{u}) : Subgroup (∀ k : ℕ, F.obj (op k)) :=
  (GrpCat.sectionsSubgroup F).comap
    { toFun := fun x (j : ℕᵒᵖ) => x j.unop
      map_one' := rfl
      map_mul' _ _ := rfl }

/-- Membership in the completed group is compatibility with every transition. -/
@[simp]
theorem mem_completedGroup_iff (F : ℕᵒᵖ ⥤ GrpCat.{u})
    (x : ∀ k : ℕ, F.obj (op k)) :
    x ∈ completedGroup F ↔
      ∀ (k l : ℕ) (h : k ≤ l), F.map (homOfLE h).op (x l) = x k := by
  constructor
  · intro hx k l h
    rw [completedGroup, Subgroup.mem_comap] at hx
    exact hx (homOfLE h).op
  · intro hx
    rw [completedGroup, Subgroup.mem_comap]
    intro ⟨l⟩ ⟨k⟩ f
    exact hx k l (leOfHom f.unop)

namespace CompletedGroup

variable {F : ℕᵒᵖ ⥤ GrpCat.{u}}

/-- Projection of a completed group to one order of the tower. -/
def projection (k : ℕ) : completedGroup F →* F.obj (op k) where
  toFun x := x.val k
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_apply (k : ℕ) (x : completedGroup F) : projection k x = x.val k :=
  (rfl)

/-- Every transition sends the higher projection to the lower projection. -/
@[simp]
theorem map_projection (k l : ℕ) (h : k ≤ l) (x : completedGroup F) :
    F.map (homOfLE h).op (projection l x) = projection k x :=
  (mem_completedGroup_iff F x.val).mp x.property k l h

/-- Completed elements are determined by their projections. -/
@[ext]
theorem ext {x y : completedGroup F}
    (h : ∀ k, projection k x = projection k y) : x = y :=
  Subtype.ext (funext h)

variable {H : Type*} [Group H]

/-- The unique homomorphism with a prescribed compatible family of projections. -/
def lift (f : ∀ k : ℕ, H →* F.obj (op k))
    (hf : ∀ (k l : ℕ) (h : k ≤ l), (F.map (homOfLE h).op).hom.comp (f l) = f k) :
    H →* completedGroup F where
  toFun x := ⟨fun k => f k x, (mem_completedGroup_iff F _).mpr
    (fun k l h => DFunLike.congr_fun (hf k l h) x)⟩
  map_one' := Subtype.ext (funext fun k => (f k).map_one)
  map_mul' x y := Subtype.ext (funext fun k => (f k).map_mul x y)

@[simp]
theorem projection_lift (f : ∀ k : ℕ, H →* F.obj (op k))
    (hf : ∀ (k l : ℕ) (h : k ≤ l), (F.map (homOfLE h).op).hom.comp (f l) = f k)
    (k : ℕ) (x : H) : projection k (lift f hf x) = f k x :=
  (rfl)

/-- Uniqueness of a lift from its projections. -/
theorem lift_unique (f : ∀ k : ℕ, H →* F.obj (op k))
    (hf : ∀ (k l : ℕ) (h : k ≤ l), (F.map (homOfLE h).op).hom.comp (f l) = f k)
    (g : H →* completedGroup F) (hg : ∀ k, (projection k).comp g = f k) :
    g = lift f hf := by
  ext x k
  exact DFunLike.congr_fun (hg k) x

variable (F)

/-- The cone of all projections of the completed group. -/
def cone : Cone F where
  pt := GrpCat.of (completedGroup F)
  π :=
    { app := fun j => GrpCat.ofHom (projection j.unop)
      naturality := fun ⟨l⟩ ⟨k⟩ f => by
        ext x
        exact (map_projection k l (leOfHom f.unop) x).symm }

/-- The compatible-family completed group is an inverse limit in the category of groups. -/
def coneIsLimit : IsLimit (cone F) where
  lift s := GrpCat.ofHom (lift (fun k => (s.π.app (op k)).hom)
    (fun k l h => by
      ext x
      exact ConcreteCategory.congr_hom (s.w (homOfLE h).op) x))
  fac s j := by ext x; rfl
  uniq s m hm := by
    apply GrpCat.hom_ext
    apply DFunLike.ext
    intro x
    apply ext
    intro k
    exact ConcreteCategory.congr_hom (hm (op k)) x

/-- The completed group agrees with Mathlib's chosen categorical inverse limit. -/
noncomputable def limitConeIso : GrpCat.of (completedGroup F) ≅ (GrpCat.limitCone F).pt :=
  (coneIsLimit F).conePointUniqueUpToIso (GrpCat.limitConeIsLimit F)

@[simp, reassoc]
theorem limitConeIso_hom_π (k : ℕ) :
    (limitConeIso F).hom ≫ (GrpCat.limitCone F).π.app (op k) =
      GrpCat.ofHom (projection (F := F) k) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- The degree filtration: degree zero is the whole group; degree `k+1` is the kernel of
projection to order `k`. -/
def degreeFiltration : ℕ → Subgroup (completedGroup F)
  | 0 => ⊤
  | k + 1 => (projection k).ker

@[simp]
theorem degreeFiltration_zero : degreeFiltration F 0 = ⊤ := (rfl)

@[simp]
theorem degreeFiltration_succ (k : ℕ) :
    degreeFiltration F (k + 1) = (projection k).ker := (rfl)

/-- Every term of the degree filtration is normal. -/
instance degreeFiltration_normal (k : ℕ) : (degreeFiltration F k).Normal := by
  cases k with
  | zero => exact (inferInstance : (⊤ : Subgroup (completedGroup F)).Normal)
  | succ k => exact MonoidHom.normal_ker _

/-- Higher filtration orders impose stronger vanishing conditions. -/
theorem degreeFiltration_antitone : Antitone (degreeFiltration F) := by
  intro k l h x hx
  cases k with
  | zero => trivial
  | succ k =>
    cases l with
    | zero => omega
    | succ l =>
      simp only [degreeFiltration_succ, MonoidHom.mem_ker] at hx ⊢
      rw [← map_projection k l (by omega), hx, map_one]

/-- The degree filtration is separated. -/
@[simp]
theorem iInf_degreeFiltration : ⨅ k, degreeFiltration F k = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply ext
  intro k
  simpa only [degreeFiltration_succ, MonoidHom.mem_ker, map_one] using
    (Subgroup.mem_iInf.mp hx) (k + 1)

/-- If every successive transition is onto, every finite-order projection is onto. -/
theorem projection_surjective
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) (k : ℕ) :
    Function.Surjective (projection (F := F) k) := by
  classical
  intro a
  -- First lift the given value along the tail starting at order `k`.
  let x : (n : ℕ) → F.obj (op (k + n)) :=
    Nat.rec a (fun n b => (hF (k + n) b).choose)
  have step (n : ℕ) :
      F.map (homOfLE (Nat.le_succ (k + n))).op (x (n + 1)) = x n :=
    (hF (k + n) (x n)).choose_spec
  have hx (m n : ℕ) (h : m ≤ n) :
      F.map (homOfLE (Nat.add_le_add_left h k)).op (x n) = x m := by
    induction h with
    | refl => simp
    | @step n h ih =>
      calc
        _ = F.map (homOfLE (Nat.add_le_add_left h k)).op
            (F.map (homOfLE (Nat.le_succ (k + n))).op (x (n + 1))) := by
          rw [← GrpCat.comp_apply, ← F.map_comp]
          rfl
        _ = x m := by rw [step, ih]
  -- Project the tail to all orders; the two routes through each triangle agree.
  let y : ∀ n : ℕ, F.obj (op n) :=
    fun n => F.map (homOfLE (Nat.le_add_left n k)).op (x n)
  have hy : y ∈ completedGroup F := by
    apply (mem_completedGroup_iff F y).mpr
    intro m n h
    dsimp only [y]
    calc
      _ = F.map (homOfLE (Nat.le_add_left m k)).op
          (F.map (homOfLE (Nat.add_le_add_left h k)).op (x n)) := by
        rw [← GrpCat.comp_apply, ← F.map_comp, ← GrpCat.comp_apply, ← F.map_comp]
        rfl
      _ = _ := by rw [hx m n h]
  exact ⟨⟨y, hy⟩, hx 0 k (Nat.zero_le k)⟩

/-- For an onto tower, quotienting by the order-`k` projection kernel recovers that order. -/
noncomputable def quotientEquiv
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) (k : ℕ) :
    completedGroup F ⧸ degreeFiltration F (k + 1) ≃* F.obj (op k) :=
  QuotientGroup.quotientKerEquivOfSurjective (projection k) (projection_surjective F hF k)

@[simp]
theorem quotientEquiv_mk
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (k : ℕ) (x : completedGroup F) :
    quotientEquiv F hF k (QuotientGroup.mk x) = projection k x :=
  (rfl)

end CompletedGroup
end Mei
