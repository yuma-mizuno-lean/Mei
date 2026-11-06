/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.History
public import Mei.LinearAlgebra.GradedCorrespondence.Path
public import Mei.LinearAlgebra.GradedModule.History.Path.Regrouping

/-!
# Selected transfers and uniform regrouping

The selected-transfer functor and the shared histories of zero-extended total
transfers describe the same homogeneous propagation. Their comparison retains
the entire coefficient and holds at every prefix, including the empty path.
The source degree must be admissible at each crossing; terminal degrees need
no lift. An inadmissible intermediate decoration vanishes in the total-transfer
expansion, as in `homogeneousHistory_totalTransfer_cons_eq_zero_of_notMem`.

For two transfer itineraries between possibly different chamber modules, a
finitely generated incoming range supplies one finite rectangle of histories
for all input parameters. Arbitrary predicates on the paired histories may
select geometric incidence conditions. The resulting nested sums compute the
selected concatenated histories, also after a final linear map. In particular,
retaining every pair recovers the composite of the two total transfers.
No geometric realization of an unrestricted operator history is asserted.

The proofs reuse the path expansion and rectangular support construction in
`Mei.LinearAlgebra.GradedModule.History.Path.Regrouping`, and the single-step
formula `decompose_right_liftLeftTotal_of_mem`. The interpretation of whole
component transfers follows Gross–Hacking–Siebert, *Theta functions on varieties
with effective anti-canonical class*, Definitions 3.1–3.3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.GradedCorrespondence

variable {R Q : Type*} [Semiring R] [Quiver Q]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {B : ∀ {b c : Q}, (b ⟶ c) → Type*}
  [∀ (b c : Q) (e : b ⟶ c), AddCommMonoid (B e)]
  [∀ (b c : Q) (e : b ⟶ c), Module R (B e)]
  {I : ∀ {b c : Q}, (b ⟶ c) → Set (ι b)}
  {J : ∀ {b c : Q}, (b ⟶ c) → Set (ι c)}
  (C : ∀ {b c : Q} (e : b ⟶ c),
    GradedCorrespondence (B := B e) (ℳ b) (ℳ c) (I e) (J e))

local notation "T" => fun e => totalTransfer (C e)

/-- Selected homogeneous path propagation is precisely the corresponding
zero-extended transfer history on its incoming homogeneous piece. This compares
the two existing constructions without an assumption that any decoration survives. -/
theorem transferFunctor_map_hom_eq_homogeneousHistory
    (s : ∀ q, ι q) (hs : ∀ {b c : Q} (e : b ⟶ c), s b ∈ I e)
    {a b : Q} (p : Quiver.Path a b) :
    (ℳ b (s b)).subtype.comp (((transferFunctor ℳ C s hs).map p).hom) =
      (p.homogeneousHistory T ℳ (p.degreesOfVertices s)).comp (ℳ a (s a)).subtype := by
  classical
  -- Expand the free extension to use Mathlib's path recursion. The component
  -- transfers are evaluated only through their public single-step formula.
  unfold transferFunctor transferPrefunctor
  induction p with
  | nil =>
    -- The objects of `Paths Q` use a type synonym for the original vertices.
    erw [CategoryTheory.Paths.lift_nil, SemimoduleCat.hom_id,
      LinearMap.comp_id, Quiver.Path.homogeneousHistory_nil, LinearMap.id_comp]
  | @cons b c p e ih =>
    refine LinearMap.ext fun (x : ℳ a (s a)) => ?_
    have hx := LinearMap.congr_fun ih x
    erw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.subtype_apply] at hx
    have hmem : p.homogeneousHistory T ℳ (p.degreesOfVertices s) x ∈ ℳ b (s b) :=
      hx ▸ Subtype.property _
    calc
      _ = ((C e).transfer ⟨s b, hs e⟩ (s c)
          (((transferFunctor ℳ C s hs).map p).hom x) : M c) := rfl
      _ = ((C e).transfer ⟨s b, hs e⟩ (s c) ⟨_, hmem⟩ : M c) := by
        exact congrArg (fun y : ℳ b (s b) =>
          ((C e).transfer ⟨s b, hs e⟩ (s c) y : M c)) (Subtype.ext hx)
      _ = (p.cons e).homogeneousHistory T ℳ
          ((p.cons e).degreesOfVertices s) (x : M a) := by
        simpa only [Quiver.Path.degreesOfVertices_cons, dite_eq_left (hs e),
          LinearMap.comp_apply, Submodule.subtype_apply] using
          (homogeneousHistory_totalTransfer_cons_apply ℳ C p e
            (p.degreesOfVertices s) (s c) (x : M a) hmem).symm
      _ = _ := (LinearMap.comp_apply
        ((p.cons e).homogeneousHistory T ℳ ((p.cons e).degreesOfVertices s))
        (ℳ a (s a)).subtype x).symm

open Classical in
/-- A finitely generated incoming range supports every selected two-block transfer sum
uniformly. The predicate may couple both histories, for instance by geometric
incidence inequalities; zero terms are retained. The right-hand side is the
pointwise selected expansion of the concatenated transfer path. -/
theorem exists_uniform_totalTransfer_regrouping
    {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c)
    {E : Type*} [AddCommMonoid E] [Module R E]
    (f : E →ₗ[R] M a) (hf : (LinearMap.range f).FG) :
    ∃ (S : Finset (p.Degrees ι)) (U : Finset (q.Degrees ι)),
      (∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) ∧
      (∀ d ∈ S, ∀ e ∉ U,
        (q.homogeneousHistory T ℳ e).comp ((p.homogeneousHistory T ℳ d).comp f) = 0) ∧
      ∀ (P : p.Degrees ι → q.Degrees ι → Prop),
        ∀ {O : Type*} [AddCommMonoid O] [Module R O] (g : M c →ₗ[R] O) (x : E),
          (∑ d ∈ S, ∑ e ∈ U, if P d e then
            g.comp ((q.homogeneousHistory T ℳ e).comp
              ((p.homogeneousHistory T ℳ d).comp f)) else 0) x =
            ∑ h ∈ (p.comp q).historySupport T ℳ (f x),
              if P ((p.degreesComp (ι := ι) q) h).1 ((p.degreesComp (ι := ι) q) h).2 then
                g ((p.comp q).homogeneousHistory T ℳ h (f x)) else 0 := by
  classical
  obtain ⟨S, U, hS, hU⟩ := p.exists_uniform_historySupport_rectangle T ℳ q f hf
  refine ⟨S, U, hS, hU, fun P O _ _ g x => ?_⟩
  rw [p.sum_ite_comp_homogeneousHistory_comp T ℳ q f g S U P]
  have hrect := p.homogeneousHistory_comp_eq_zero_of_notMem_rectangle T ℳ q f S U hS hU
  have hexp := (p.comp q).sum_ite_homogeneousHistory_comp_apply T ℳ f
    ((S ×ˢ U).map (p.degreesComp (ι := ι) q).symm.toEmbedding) hrect
    (fun h => P ((p.degreesComp (ι := ι) q) h).1 ((p.degreesComp (ι := ι) q) h).2) x
  have hmap := congrArg g hexp
  convert hmap using 1
  all_goals
    simp only [LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> simp

end Mei.GradedCorrespondence
