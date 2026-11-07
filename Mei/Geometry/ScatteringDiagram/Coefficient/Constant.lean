/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.Linear

/-!
# Constant sections of the coefficient local system

If every wall label of a finite wall diagram fixes a coefficient, then the family taking this
value at every off-wall point is a section of `coefficientLocalSystem` over every open subset
of the regular locus, including opens meeting walls and walls on which the crossing factors
would otherwise act. Path transport is a product of labels and their inverses, so it fixes the
coefficient, and no consistency of the diagram is needed.

For a linear family of fixed coefficients this gives a linear map into the sections whose value
at each off-wall point is the family itself, uniquely determined by these values.
`FiniteWallDiagram.exists_forall_value_eq_iff_smul_eq` shows that for one wall the fixedness of
the label is also necessary. The wall-crossing transport follows Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Mei.FiniteWallDiagram

variable {N V G : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {C : FinitePolyhedralComplex h}
  [Group G] (D : FiniteWallDiagram C G)

section MulAction

variable (M : Type*) [MulAction G M] (U : Opens C.regularSpace) (c : M)
  (hc : ∀ P, D.label P • c = c)

include hc in
/-- A coefficient fixed by every wall label is parallel for the coefficient transport on every
transport chart: path transport multiplies by labels and their inverses. -/
private theorem prelocal_pred_constant :
    (D.coefficientTransport M).prelocal.sheafify.pred (fun _ : U => fun _ => c) := by
  intro x
  refine ⟨U, x.property, 𝟙 U, ?_⟩
  rw [DenseBasisTransport.prelocal_pred_iff]
  intro B hB _ y z hy hz
  have hchart : B ∈ C.coefficientCharts := by
    simpa only [D.coefficientTransport_basis M] using hB
  rw [D.coefficientTransport_transport M B hchart y z hy hz, D.coefficientPathTransport_apply M]
  exact D.pathProduct_mem (S := MulAction.stabilizer G c) _ fun a _ => hc a.2.1

/-- A coefficient fixed by every wall label, as a section of the coefficient local system over
an arbitrary open subset of the regular locus. Its value at each off-wall point is the
coefficient. -/
def constantCoefficientSection : (D.coefficientLocalSystem M).presheaf.obj (op U) :=
  (D.coefficientTransport M).sectionOfLocallyParallel (fun _ : U => fun _ => c)
    (D.prelocal_pred_constant M U c hc)

/-- The constant section takes the prescribed value at every off-wall point of the open. -/
@[simp]
theorem value_constantCoefficientSection (x : C.coefficientPoints) (hx : x.val ∈ U) :
    (D.coefficientTransport M).value (D.constantCoefficientSection M U c hc) x hx = c :=
  (D.coefficientTransport M).value_sectionOfLocallyParallel _ _ x hx

/-- Restriction to a smaller open carries the constant section to the constant section. -/
@[simp]
theorem restriction_constantCoefficientSection {U' : Opens C.regularSpace} (hU'U : U' ≤ U) :
    (D.coefficientLocalSystem M).presheaf.map (homOfLE hU'U).op
        (D.constantCoefficientSection M U c hc) = D.constantCoefficientSection M U' c hc :=
  (D.coefficientTransport M).section_ext fun x hx => by
    rw [DenseBasisTransport.value_restrict, value_constantCoefficientSection,
      value_constantCoefficientSection]

end MulAction

section Linear

variable {R E : Type*} (M : Type*) (U : Opens C.regularSpace) [Semiring R] [AddCommMonoid M]
  [DistribMulAction G M] [Module R M] [SMulCommClass G R M] [AddCommMonoid E] [Module R E]
  (g : E →ₗ[R] M) (hg : ∀ e P, D.label P • g e = g e)

/-- A linear family of coefficients fixed by every wall label, as a linear map into the sections
of the coefficient local system over an arbitrary open subset of the regular locus. Its value at
each off-wall point is the family itself. -/
def constantCoefficientSections :
    E →ₗ[R] (D.coefficientLocalSystem M).presheaf.obj (op U) :=
  -- Construct with the transport-section instances, so the value lemmas match directly.
  letI : AddCommMonoid ((D.coefficientTransport M).sheaf.presheaf.obj (op U)) :=
    (D.coefficientTransport M).instAddCommMonoidSections U
  letI : Module R ((D.coefficientTransport M).sheaf.presheaf.obj (op U)) :=
    (D.coefficientTransport M).instModuleSections R U
  { toFun e := D.constantCoefficientSection M U (g e) (hg e)
    map_add' a b := by
      apply (D.coefficientTransport M).section_ext
      intro x hx
      simp only [(D.coefficientTransport M).value_add, value_constantCoefficientSection]
      exact map_add g a b
    map_smul' r a := by
      apply (D.coefficientTransport M).section_ext
      intro x hx
      simp only [(D.coefficientTransport M).value_smul (R := R),
        value_constantCoefficientSection, RingHom.id_apply]
      exact map_smul g r a }

/-- The constant sections take the prescribed values at every off-wall point of the open. -/
@[simp]
theorem value_constantCoefficientSections (e : E) (x : C.coefficientPoints) (hx : x.val ∈ U) :
    (D.coefficientTransport M).value (D.constantCoefficientSections M U g hg e) x hx = g e :=
  D.value_constantCoefficientSection M U (g e) (hg e) x hx

/-- A section is determined by its values at off-wall points, so the constant sections are the
only linear family of sections of the open with the prescribed constant values. -/
theorem eq_constantCoefficientSections_of_value_eq {t : E →ₗ[R] _}
    (ht : ∀ e (x : C.coefficientPoints) (hx : x.val ∈ U),
      (D.coefficientTransport M).value (t e) x hx = g e) :
    t = D.constantCoefficientSections M U g hg :=
  LinearMap.ext fun e => (D.coefficientTransport M).section_ext fun x hx => by
    rw [ht, value_constantCoefficientSections]

end Linear

end Mei.FiniteWallDiagram
