/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.End.Recursion
public import Mei.LinearAlgebra.ModuleFiltration.Map
public import Mei.LinearAlgebra.ModuleFiltration.Nilpotent

/-!
# Finite recursion on filtered module quotients

A filtration-raising endomorphism gives a nilpotent recursion at each order.
The shared semimodule theorem `Module.End.eq_finiteRecursion_of_eq_add` identifies
every solution with the sum of its iterates. The solution operators commute with
all quotient transitions and hence assemble into a linear map on the completion.
That map solves the recursion for the endomorphism of the completion induced by
`completionMap`, and every solution of that recursion equals it.

The original module need not be complete or separated, and its endomorphism need
not be nilpotent. This supplies the algebraic uniqueness step for comparing
independent geometric recursions; it does not establish those geometric equations.
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M) (f : Module.End R M)
  (hf : ∀ k, F.submodule k ≤ (F.submodule (k + 1)).comap f)

/-- The linear solution operator on the order-`k` quotient. -/
def quotientRecursion (k : ℕ) : Module.End R (F.quotient k) :=
  (F.quotientRaisingEnd f hf k).finiteRecursion (k + 1)

/-- The quotient solution operator is the generic finite recursion operator. -/
theorem quotientRecursion_eq_finiteRecursion (k : ℕ) :
    F.quotientRecursion f hf k = (F.quotientRaisingEnd f hf k).finiteRecursion (k + 1) :=
  (rfl)

/-- The quotient solution is the finite sum retaining powers zero through `k`. -/
theorem quotientRecursion_apply (k : ℕ) (a : F.quotient k) :
    F.quotientRecursion f hf k a =
      ∑ j ∈ Finset.range (k + 1), (F.quotientRaisingEnd f hf k ^ j) a :=
  Module.End.finiteRecursion_apply _ _ _

/-- The finite sum solves the quotient recursion. -/
theorem quotientRecursion_eq_add (k : ℕ) (a : F.quotient k) :
    F.quotientRecursion f hf k a =
      a + F.quotientRaisingEnd f hf k (F.quotientRecursion f hf k a) :=
  Module.End.finiteRecursion_eq_add _ (F.quotientRaisingEnd_pow_eq_zero f hf k) a

/-- Every solution of the quotient recursion is the shared finite sum. -/
theorem eq_quotientRecursion_of_eq_add (k : ℕ) {a x : F.quotient k}
    (hx : x = a + F.quotientRaisingEnd f hf k x) :
    x = F.quotientRecursion f hf k a :=
  Module.End.eq_finiteRecursion_of_eq_add _
    (F.quotientRaisingEnd_pow_eq_zero f hf k) hx

/-- The solution operators commute with quotient transitions, despite the
different lengths of their defining sums. -/
@[simp]
theorem transition_quotientRecursion {k l : ℕ} (hkl : k ≤ l) (a : F.quotient l) :
    F.transition hkl (F.quotientRecursion f hf l a) =
      F.quotientRecursion f hf k (F.transition hkl a) := by
  have h := Module.End.comp_finiteRecursion
    (F.quotientRaisingEnd f hf l) (F.quotientRaisingEnd f hf k) (F.transition hkl)
    (LinearMap.ext (F.transition_quotientRaisingEnd f hf hkl))
    (F.quotientRaisingEnd_pow_eq_zero f hf l)
    (F.quotientRaisingEnd_pow_eq_zero f hf k)
  exact LinearMap.congr_fun h a

/-- Compatible finite solutions define a linear solution operator on the completion. -/
def completionRecursion : Module.End R F.completion :=
  F.lift (fun k => (F.quotientRecursion f hf k).comp (F.projection k)) (by
    intro k l hkl
    ext a
    simp only [LinearMap.comp_apply, transition_quotientRecursion, transition_projection])

/-- Each projection of the completed solution is its finite quotient solution. -/
@[simp]
theorem projection_completionRecursion (k : ℕ) (a : F.completion) :
    F.projection k (F.completionRecursion f hf a) =
      F.quotientRecursion f hf k (F.projection k a) :=
  F.projection_lift _ _ k a

/-- The completed solution satisfies the recursion at every finite order. -/
theorem projection_completionRecursion_eq_add (k : ℕ) (a : F.completion) :
    F.projection k (F.completionRecursion f hf a) = F.projection k a +
      F.quotientRaisingEnd f hf k (F.projection k (F.completionRecursion f hf a)) := by
  simpa only [projection_completionRecursion] using
    F.quotientRecursion_eq_add f hf k (F.projection k a)

/-- A compatible solution is uniquely determined by its finite-order recursions. -/
theorem eq_completionRecursion_of_forall_projection_eq_add {a x : F.completion}
    (hx : ∀ k, F.projection k x =
      F.projection k a + F.quotientRaisingEnd f hf k (F.projection k x)) :
    x = F.completionRecursion f hf a := by
  apply F.completion_ext
  intro k
  rw [projection_completionRecursion]
  exact F.eq_quotientRecursion_of_eq_add f hf k (hx k)

/-- The completed solution solves the recursion for the endomorphism of the
completion induced by `f`. -/
theorem completionRecursion_eq_add_completionMap (a : F.completion) :
    F.completionRecursion f hf a = a + F.completionMap F f id monotone_id
      (fun k _ hx => F.antitone (Nat.le_succ (k + 1)) (hf (k + 1) hx))
      (F.completionRecursion f hf a) := by
  apply F.completion_ext
  intro k
  simpa only [map_add, projection_completionMap, id_eq, quotientRaisingEnd_eq_mapQ] using
    F.projection_completionRecursion_eq_add f hf k a

/-- Every solution of the recursion for the endomorphism of the completion
induced by `f` is the completed solution. -/
theorem eq_completionRecursion_of_eq_add_completionMap {a x : F.completion}
    (hx : x = a + F.completionMap F f id monotone_id
      (fun k _ hx => F.antitone (Nat.le_succ (k + 1)) (hf (k + 1) hx)) x) :
    x = F.completionRecursion f hf a := by
  apply F.eq_completionRecursion_of_forall_projection_eq_add f hf
  intro k
  simpa only [map_add, projection_completionMap, id_eq, quotientRaisingEnd_eq_mapQ] using
    congrArg (F.projection k) hx

end Mei.ModuleFiltration
