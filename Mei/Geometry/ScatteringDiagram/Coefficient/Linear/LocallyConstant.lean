/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.Linear

/-!
# Linear coefficient sections away from walls

Locally constant families of linear coefficient maps on an off-wall open define
linear maps into `coefficientLocalSystem`. Local transport in a
convex chart contained in that open is the identity, since its segments meet no
walls.
-/

public noncomputable section

open TauCeti (FinitePolyhedralComplex)

open CategoryTheory TopologicalSpace Opposite Set Topology TopCat Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V G M : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {C : FinitePolyhedralComplex h}
  [Group G] (D : FiniteWallDiagram C G)


variable {R E : Type*} [Semiring R] [AddCommMonoid M] [DistribMulAction G M]
  [Module R M] [AddCommMonoid E] [Module R E]
  {U : Opens C.regularSpace} (hoff : (U : Set C.regularSpace) ⊆ C.coefficientPoints)
  (g : LocallyConstant U (E →ₗ[R] M))

include hoff in
private theorem locallyParallel_locallyConstant (a : E) :
    (D.coefficientTransport M).prelocal.sheafify.pred
      (fun x : U => fun _ => g x a) := by
  intro x
  obtain ⟨A, hA, hxA, hconst⟩ := g.isLocallyConstant.exists_open x
  let W : Opens C.regularSpace :=
    ⟨Subtype.val '' A, U.isOpen.isOpenMap_subtype_val _ hA⟩
  have hWU : W ≤ U := fun z hz => by
    obtain ⟨y, _, rfl⟩ := hz
    exact y.property
  have hsame (z : W) : g ⟨z.val, hWU z.property⟩ = g x := by
    obtain ⟨y, hy, he⟩ := z.property
    have ey : y = (⟨z.val, hWU z.property⟩ : U) := Subtype.ext he
    exact ey ▸ hconst y hy
  refine ⟨W, ⟨x, hxA, rfl⟩, homOfLE hWU, ?_⟩
  rw [DenseBasisTransport.prelocal_pred_iff]
  intro B' hB' hB'W y z hy hz
  have hchart : B' ∈ C.coefficientCharts := by
    simpa only [D.coefficientTransport_basis M] using hB'
  rw [D.coefficientTransport_transport M B' hchart y z hy hz,
    D.coefficientPathTransport_coefficientSegment_eq_refl_of_subset B' hchart
      (fun q hq => hoff (hWU (hB'W hq))) y z hy hz, Equiv.refl_apply]
  exact congrArg (fun f : E →ₗ[R] M => f a)
    ((hsame ⟨y.val, hB'W hy⟩).trans (hsame ⟨z.val, hB'W hz⟩).symm)

variable [SMulCommClass G R M]

/-- A locally constant family of linear coefficient maps on an off-wall open,
as a linear map into coefficient-local-system sections. Its value at a point
`x` of the open is `g x a` for incoming coefficient `a`. -/
def locallyConstantCoefficientSections :
    E →ₗ[R] (D.coefficientLocalSystem M).presheaf.obj (op U) := by
  let T := D.coefficientTransport M
  -- Construct with the transport-section instances so the generic value lemmas
  -- match directly. These are the instances registered on coefficient sections.
  letI : AddCommMonoid (T.sheaf.presheaf.obj (op U)) := T.instAddCommMonoidSections U
  letI : Module R (T.sheaf.presheaf.obj (op U)) := T.instModuleSections R U
  exact ({
    toFun a := T.sectionOfLocallyParallel
      (fun x : U => fun _ => g x a) (D.locallyParallel_locallyConstant hoff g a)
    map_add' a b := by
      apply T.section_ext
      intro x hx
      simp only [T.value_add, DenseBasisTransport.value_sectionOfLocallyParallel, map_add]
    map_smul' r a := by
      apply T.section_ext
      intro x hx
      simp only [T.value_smul (R := R),
        DenseBasisTransport.value_sectionOfLocallyParallel, map_smul, RingHom.id_apply]
  } : E →ₗ[R] T.sheaf.presheaf.obj (op U))

/-- The constructed section reads the prescribed linear coefficient map. -/
@[simp]
theorem value_locallyConstantCoefficientSections (a : E) (x : C.coefficientPoints)
    (hx : x.val ∈ U) :
    (D.coefficientTransport M).value (D.locallyConstantCoefficientSections hoff g a) x hx =
      g ⟨x.val, hx⟩ a := by
  exact (D.coefficientTransport M).value_sectionOfLocallyParallel _ _ x hx

/-- Restricting the section map only restricts its endpoint domain; the
locally constant input maps themselves are pulled back by the open inclusion. -/
@[simp]
theorem locallyConstantCoefficientSections_restrict {U' : Opens C.regularSpace}
    (hU'U : U' ≤ U) (a : E) :
    (D.coefficientTransport M).restrictionLinearMap R hU'U
        (D.locallyConstantCoefficientSections hoff g a) =
      D.locallyConstantCoefficientSections (fun _ hx => hoff (hU'U hx))
        (LocallyConstant.comap
          ⟨fun x => ⟨x.val, hU'U x.property⟩, continuous_subtype_val.subtype_mk _⟩ g) a := by
  apply (D.coefficientTransport M).section_ext
  intro x hx
  calc
    _ = g ⟨x.val, hU'U hx⟩ a :=
      ((D.coefficientTransport M).value_restrictionLinearMap (R := R) _ _ _ _).trans
        (D.value_locallyConstantCoefficientSections hoff g a x (hU'U hx))
    _ = _ := by
      simpa only [LocallyConstant.coe_comap_apply, ContinuousMap.coe_mk] using
        (D.value_locallyConstantCoefficientSections
          (fun _ hz => hoff (hU'U hz))
          (LocallyConstant.comap
            (⟨fun z => ⟨z.val, hU'U z.property⟩,
              continuous_subtype_val.subtype_mk _⟩ : C(U', U)) g)
          a x hx).symm

end Mei.FiniteWallDiagram
