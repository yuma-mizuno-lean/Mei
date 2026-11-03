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
Intertwining filtered coefficient maps preserve these solutions, including when
the source and target cutoffs are compared by a nonidentity monotone modulus.

The original module need not be complete or separated, and its endomorphism need
not be nilpotent. The solution preserves all input filtration terms, and its
correction has one higher order, so it retains the leading class. This supplies
the algebraic uniqueness step for comparing
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

/-- A finite quotient recursion is represented by the same finite sum in the original module. -/
@[simp]
theorem quotientRecursion_mk (k : ℕ) (a : M) :
    F.quotientRecursion f hf k (Submodule.Quotient.mk a) =
      (F.submodule (k + 1)).mkQ (f.finiteRecursion (k + 1) a) := by
  simp only [quotientRecursion_apply, Module.End.finiteRecursion_apply, map_sum,
    Submodule.mkQ_apply, quotientRaisingEnd_pow_mk]

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

/-- Completed recursion preserves every filtration term of its input. -/
theorem completionRecursion_mem_completedFiltration {k : ℕ} {a : F.completion}
    (ha : a ∈ F.completedFiltration.submodule k) :
    F.completionRecursion f hf a ∈ F.completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [completedFiltration_succ, LinearMap.mem_ker] at ha ⊢
    rw [projection_completionRecursion, ha, map_zero]

/-- The completed solution satisfies the recursion at every finite order. -/
theorem projection_completionRecursion_eq_add (k : ℕ) (a : F.completion) :
    F.projection k (F.completionRecursion f hf a) = F.projection k a +
      F.quotientRaisingEnd f hf k (F.projection k (F.completionRecursion f hf a)) := by
  simpa only [projection_completionRecursion] using
    F.quotientRecursion_eq_add f hf k (F.projection k a)

/-- The completed recursion solution has exactly the same filtration order as
its input, even when the original module filtration is not separated. -/
@[simp]
theorem completionRecursion_mem_completedFiltration_iff (k : ℕ) (a : F.completion) :
    F.completionRecursion f hf a ∈ F.completedFiltration.submodule k ↔
      a ∈ F.completedFiltration.submodule k := by
  constructor
  · intro h
    cases k with
    | zero => simp
    | succ k =>
      rw [completedFiltration_succ, LinearMap.mem_ker] at h ⊢
      have he := F.projection_completionRecursion_eq_add f hf k a
      rw [h, map_zero, add_zero] at he
      exact he.symm
  · exact F.completionRecursion_mem_completedFiltration f hf

/-- For an input of order at least `k`, the recursion correction has order at least
`k + 1`. In particular the solution has the same leading class as its input. -/
theorem completionRecursion_sub_self_mem_completedFiltration {k : ℕ} {a : F.completion}
    (ha : a ∈ F.completedFiltration.submodule k) :
    F.completionRecursion f hf a - a ∈ F.completedFiltration.submodule (k + 1) := by
  have hs := F.completionRecursion_mem_completedFiltration f hf ha
  obtain ⟨m, hm, he⟩ := F.exists_projection_eq_of_mem_completedFiltration (k := k) hs
  rw [completedFiltration_succ, LinearMap.mem_ker, map_sub,
    F.projection_completionRecursion_eq_add f hf k a, add_sub_cancel_left,
    ← he, quotientRaisingEnd_mk, Submodule.Quotient.mk_eq_zero]
  exact hf k hm

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

section Naturality

variable {N : Type*} [AddCommGroup N] [Module R N]
  (G : ModuleFiltration R N) (g : Module.End R N)
  (hg : ∀ k, G.submodule k ≤ (G.submodule (k + 1)).comap g)
  (r : M →ₗ[R] N) (ρ : ℕ → ℕ) (hρ : Monotone ρ)
  (hr : ∀ k, F.submodule (ρ k + 1) ≤ (G.submodule (k + 1)).comap r)
  (hfg : r.comp f = g.comp r)

include hfg

/-- A comparison between any two chosen quotients preserves their recursion
solutions. Only that pair of orders needs a filtration bound. -/
theorem mapQ_quotientRecursion (l k : ℕ)
    (hrk : F.submodule (l + 1) ≤ (G.submodule (k + 1)).comap r) (a : F.quotient l) :
    (F.submodule (l + 1)).mapQ (G.submodule (k + 1)) r hrk
        (F.quotientRecursion f hf l a) =
      G.quotientRecursion g hg k
        ((F.submodule (l + 1)).mapQ (G.submodule (k + 1)) r hrk a) := by
  exact LinearMap.congr_fun (Module.End.comp_finiteRecursion
    (F.quotientRaisingEnd f hf l) (G.quotientRaisingEnd g hg k)
    ((F.submodule (l + 1)).mapQ (G.submodule (k + 1)) r hrk)
    (LinearMap.ext (F.mapQ_quotientRaisingEnd f hf G g hg r l k hrk hfg))
    (F.quotientRaisingEnd_pow_eq_zero f hf l)
    (G.quotientRaisingEnd_pow_eq_zero g hg k)) a

/-- Filtered coefficient intertwiners preserve the completed recursion solution.
No same-order cutoff, injectivity, or nilpotence on the original modules is required. -/
theorem completionMap_completionRecursion (a : F.completion) :
    F.completionMap G r ρ hρ hr (F.completionRecursion f hf a) =
      G.completionRecursion g hg (F.completionMap G r ρ hρ hr a) := by
  apply G.completion_ext
  intro k
  simp only [projection_completionMap, projection_completionRecursion]
  exact F.mapQ_quotientRecursion f hf G g hg r hfg (ρ k) k (hr k) (F.projection (ρ k) a)

end Naturality

end Mei.ModuleFiltration
