/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.DenseBasisTransport
public import Mei.Algebra.Category.SemimoduleCat.Limits
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Group.TransferInstance

/-!
# Linear sections of dense-domain transport sheaves

If the chart transports preserve addition and scalar multiplication, the existing
sheaf of locally parallel coefficients is a sheaf of semimodules. Addition and
scalar multiplication are pointwise on the dense coefficient domain. Restriction
and evaluation are linear; on a preconnected subopen of a transport chart,
evaluation is a linear equivalence.

Finite linear combinations of locally parallel sections remain locally parallel.
Restriction and evaluation preserve these combinations, so coefficient identities
can be checked in a chart and carried to smaller opens.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Set TopCat

universe u v r

namespace Mei.DenseBasisTransport

variable {X : TopCat.{u}} {S : Set X} {M : Type v} (T : DenseBasisTransport S M)
  [AddCommMonoid M]

/-- Chart transports preserve the additive coefficient structure. -/
class IsAdditive : Prop where
  /-- Transport preserves zero. -/
  map_zero : ∀ U hU x y hx hy, T.transport U hU x y hx hy 0 = 0
  /-- Transport preserves addition. -/
  map_add : ∀ U hU x y hx hy a b,
    T.transport U hU x y hx hy (a + b) =
      T.transport U hU x y hx hy a + T.transport U hU x y hx hy b

attribute [simp] IsAdditive.map_zero IsAdditive.map_add

variable [T.IsAdditive]

-- Mathlib's operation induction for sheafification gives closure on the
-- existing section predicate; the coefficient functions below use a Type-valued
-- index so their pointwise algebra is supplied by Mathlib's Pi instances.
private def coefficientFunctions (U : Opens X) :
    AddSubmonoid ({x : S // x.val ∈ U} → M) where
  carrier := {f | T.prelocal.sheafify.pred (U := U)
    (fun x hx => f ⟨⟨x.val, hx⟩, x.property⟩)}
  zero_mem' := PrelocalPredicate.sheafifyOf (P := T.prelocal)
    (f := fun (_ : U) _ => (0 : M)) (by
    rw [prelocal_pred_iff]
    intro V hV hVU x y hx hy
    exact IsAdditive.map_zero (T := T) V hV x y hx hy)
  add_mem' {a b} ha hb := by
    exact T.prelocal.sheafify_inductionOn₂' T.prelocal T.prelocal
      (fun f g hx => f hx + g hx) (by
        intro U V a b ha hb
        rw [prelocal_pred_iff] at ha hb ⊢
        intro W hW hWI x y hx hy
        rw [IsAdditive.map_add]
        exact congrArg₂ (· + ·) (ha W hW (fun z hz => (hWI hz).1) x y hx hy)
          (hb W hW (fun z hz => (hWI hz).2) x y hx hy))
      (a := fun x hx => a ⟨⟨x.val, hx⟩, x.property⟩)
      (b := fun x hx => b ⟨⟨x.val, hx⟩, x.property⟩) ha hb

private def coefficientFunctionsEquiv (U : Opens X) :
    T.sheaf.presheaf.obj (op U) ≃ T.coefficientFunctions U where
  toFun s := ⟨fun x => T.value s x.val x.property, T.locallyParallel_value s⟩
  invFun f := T.sectionOfLocallyParallel (fun x hx => f.val ⟨⟨x.val, hx⟩, x.property⟩) f.property
  left_inv s := T.section_ext fun x hx => T.value_sectionOfLocallyParallel _ _ x hx
  right_inv f := by
    apply Subtype.ext
    funext x
    exact T.value_sectionOfLocallyParallel _ _ x.val x.property

-- Keep the predicate representation private; values have the public equations below.
@[no_expose]
instance instAddCommMonoidSections (U : Opens X) :
    AddCommMonoid (T.sheaf.presheaf.obj (op U)) := by
  exact (T.coefficientFunctionsEquiv U).addCommMonoid

/-- Zero sections have zero coefficients. -/
@[simp]
theorem value_zero {U : Opens X} (x : S) (hx : x.val ∈ U) :
    T.value (0 : T.sheaf.presheaf.obj (op U)) x hx = 0 := by
  simp [Equiv.zero_def, coefficientFunctionsEquiv, value_sectionOfLocallyParallel]

/-- Section addition is pointwise at coefficient points. -/
@[simp]
theorem value_add {U : Opens X} (s t : T.sheaf.presheaf.obj (op U))
    (x : S) (hx : x.val ∈ U) : T.value (s + t) x hx = T.value s x hx + T.value t x hx := by
  simp [Equiv.add_def, coefficientFunctionsEquiv, value_sectionOfLocallyParallel]

/-- Repeated section addition is pointwise, independently of any scalar ring. -/
@[simp]
theorem value_nsmul {U : Opens X} (n : ℕ) (s : T.sheaf.presheaf.obj (op U))
    (x : S) (hx : x.val ∈ U) : T.value (n • s) x hx = n • T.value s x hx := by
  induction n with
  | zero => simp only [zero_nsmul, value_zero]
  | succ n hn => simp only [succ_nsmul, value_add, hn]

/-- Evaluation preserves finite sums of locally parallel sections. -/
@[simp]
theorem value_sum {ι : Type*} {U : Opens X} (s : Finset ι)
    (f : ι → T.sheaf.presheaf.obj (op U)) (x : S) (hx : x.val ∈ U) :
    T.value (∑ i ∈ s, f i) x hx = ∑ i ∈ s, T.value (f i) x hx := by
  let e : T.sheaf.presheaf.obj (op U) →+ M :=
    { toFun t := T.value t x hx
      map_zero' := T.value_zero x hx
      map_add' s t := T.value_add s t x hx }
  exact map_sum e f s

variable (R : Type r) [Semiring R] [Module R M]

/-- Chart transports commute with coefficient scalars. -/
class PreservesSMul : Prop where
  /-- Transport preserves scalar multiplication. -/
  map_smul : ∀ U hU x y hx hy (a : R) b,
    T.transport U hU x y hx hy (a • b) = a • T.transport U hU x y hx hy b

attribute [simp] PreservesSMul.map_smul

variable [T.PreservesSMul R]

omit [T.IsAdditive] in
private theorem smul_locallyParallel (a : R) {U : Opens X}
    (s : T.sheaf.presheaf.obj (op U)) :
    T.prelocal.sheafify.pred (fun x hx => a • T.value s ⟨x.val, hx⟩ x.property) :=
  T.prelocal.sheafify_inductionOn' (fun f hx => a • f hx)
    (by
      intro V f hf
      rw [prelocal_pred_iff] at hf ⊢
      intro W hW hWV x y hx hy
      rw [PreservesSMul.map_smul]
      exact congrArg (a • ·) (hf W hW hWV x y hx hy)) (T.locallyParallel_value s)

instance instSMulSections (U : Opens X) : SMul R (T.sheaf.presheaf.obj (op U)) where
  smul a s := T.sectionOfLocallyParallel
    (fun x hx => a • T.value s ⟨x.val, hx⟩ x.property) (by exact T.smul_locallyParallel R a s)

omit [T.IsAdditive] in
/-- Scalar multiplication is pointwise at coefficient points. -/
@[simp]
theorem value_smul {U : Opens X} (a : R) (s : T.sheaf.presheaf.obj (op U))
    (x : S) (hx : x.val ∈ U) : T.value (a • s) x hx = a • T.value s x hx := by
  exact T.value_sectionOfLocallyParallel _ _ x hx

instance instModuleSections (U : Opens X) : Module R (T.sheaf.presheaf.obj (op U)) := by
  let e : T.sheaf.presheaf.obj (op U) →+ ({x : S // x.val ∈ U} → M) :=
    { toFun s x := T.value s x.val x.property
      map_zero' := by funext x; exact T.value_zero x.val x.property
      map_add' s t := by funext x; exact T.value_add s t x.val x.property }
  exact Function.Injective.module R e
    (fun s t he => T.section_ext fun x hx => congrFun he ⟨x, hx⟩)
    (fun a s => funext fun x => T.value_smul R a s x.val x.property)

/-- Evaluation at any coefficient point is linear. -/
def evaluationLinearMap {U : Opens X} (x : S) (hx : x.val ∈ U) :
    T.sheaf.presheaf.obj (op U) →ₗ[R] M where
  toFun s := T.value s x hx
  map_add' _ _ := T.value_add _ _ _ _
  map_smul' _ _ := T.value_smul R _ _ _ _

/-- Linear evaluation reads the original coefficient value. -/
@[simp]
theorem evaluationLinearMap_apply {U : Opens X} (x : S) (hx : x.val ∈ U)
    (s : T.sheaf.presheaf.obj (op U)) :
    T.evaluationLinearMap R x hx s = T.value s x hx := by rfl

/-- Restriction of the original transport sheaf, bundled as a linear map. -/
def restrictionLinearMap {U V : Opens X} (hVU : V ≤ U) :
    T.sheaf.presheaf.obj (op U) →ₗ[R] T.sheaf.presheaf.obj (op V) where
  toFun := T.sheaf.presheaf.map (homOfLE hVU).op
  map_add' s t := by
    apply T.section_ext
    intro x hx
    simp only [value_restrict, value_add]
  map_smul' a s := by
    apply T.section_ext
    intro x hx
    simp only [value_restrict, value_smul, RingHom.id_apply]

/-- Linear restriction is the original sheaf restriction. -/
theorem restrictionLinearMap_apply {U V : Opens X} (hVU : V ≤ U)
    (s : T.sheaf.presheaf.obj (op U)) :
    T.restrictionLinearMap R hVU s = T.sheaf.presheaf.map (homOfLE hVU).op s := by rfl

/-- Linear restriction preserves coefficient values. -/
@[simp]
theorem value_restrictionLinearMap {U V : Opens X} (hVU : V ≤ U)
    (s : T.sheaf.presheaf.obj (op U)) (x : S) (hx : x.val ∈ V) :
    T.value (T.restrictionLinearMap R hVU s) x hx = T.value s x (hVU hx) := by
  rw [restrictionLinearMap_apply, value_restrict]

/-- On a preconnected subopen of a chart, evaluation is a linear equivalence. -/
def evaluationLinearEquiv {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    [PreconnectedSpace U] (x : S) (hx : x.val ∈ U) :
    T.sheaf.presheaf.obj (op U) ≃ₗ[R] M where
  __ := T.evaluationEquiv hB hUB x hx
  map_add' _ _ := by simp only [Equiv.toFun_as_coe, evaluationEquiv_apply, value_add]
  map_smul' _ _ := by
    simp only [Equiv.toFun_as_coe, evaluationEquiv_apply, value_smul, RingHom.id_apply]

/-- The linear evaluation equivalence evaluates the original section. -/
@[simp]
theorem evaluationLinearEquiv_apply {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    [PreconnectedSpace U] (x : S) (hx : x.val ∈ U)
    (s : T.sheaf.presheaf.obj (op U)) :
    T.evaluationLinearEquiv R hB hUB x hx s = T.value s x hx := by
  exact T.evaluationEquiv_apply hB hUB x hx s

/-- Inverse linear evaluation reconstructs coefficients by the original transport. -/
@[simp]
theorem value_evaluationLinearEquiv_symm {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    [PreconnectedSpace U] (x : S) (hx : x.val ∈ U) (a : M) (y : S) (hy : y.val ∈ U) :
    T.value ((T.evaluationLinearEquiv R hB hUB x hx).symm a) y hy =
      T.transport B hB x y (hUB hx) (hUB hy) a := by
  exact T.value_evaluationEquiv_symm hB hUB x hx a y hy

/-- The original transport presheaf with linear restrictions. -/
def semimodulePresheaf : X.Presheaf (SemimoduleCat.{max u v} R) where
  obj U := SemimoduleCat.of R (T.sheaf.presheaf.obj (op U.unop))
  map f := SemimoduleCat.ofHom (T.restrictionLinearMap R f.unop.le)
  map_id U := by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact ConcreteCategory.congr_hom (T.sheaf.presheaf.map_id U) s
  map_comp f g := by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact ConcreteCategory.congr_hom (T.sheaf.presheaf.map_comp f g) s

/-- The semimodule presheaf has exactly the original section carriers. -/
@[simp]
theorem semimodulePresheaf_obj (U : (Opens X)ᵒᵖ) :
    (T.semimodulePresheaf R).obj U =
      SemimoduleCat.of R (T.sheaf.presheaf.obj (op U.unop)) := by rfl

/-- The semimodule presheaf maps are the original linear restrictions. -/
@[simp]
theorem semimodulePresheaf_map {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (T.semimodulePresheaf R).map f =
      eqToHom (T.semimodulePresheaf_obj R U) ≫
        SemimoduleCat.ofHom (T.restrictionLinearMap R f.unop.le) ≫
          eqToHom (T.semimodulePresheaf_obj R V).symm := by rfl

/-- Forgetting linear structure recovers the existing presheaf exactly. -/
@[simp]
theorem semimodulePresheaf_comp_forget :
    T.semimodulePresheaf R ⋙ forget (SemimoduleCat R) = T.sheaf.presheaf := by rfl

/-- Locally parallel coefficients form a sheaf of semimodules over a semiring. -/
def semimoduleSheaf : X.Sheaf (SemimoduleCat.{max u v} R) where
  obj := T.semimodulePresheaf R
  property := (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp
    (Opens.grothendieckTopology X) (T.semimodulePresheaf R)
    (forget (SemimoduleCat.{max u v} R))).mpr
    (by simpa only [semimodulePresheaf_comp_forget] using T.sheaf.property)

/-- The semimodule sheaf uses the characterized linear presheaf. -/
@[simp]
theorem semimoduleSheaf_obj : (T.semimoduleSheaf R).obj = T.semimodulePresheaf R := by rfl

/-- Forgetting the semimodule-valued sheaf gives the original transport presheaf. -/
theorem semimoduleSheaf_comp_forget :
    (T.semimoduleSheaf R).obj ⋙ forget (SemimoduleCat R) = T.sheaf.presheaf := by
  exact T.semimodulePresheaf_comp_forget R

end Mei.DenseBasisTransport
