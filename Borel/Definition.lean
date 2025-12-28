/-!
# Borel Subgroup Definition

This module defines the Borel subgroup using mathlib4's algebraic group theory.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.GroupTheory.Subgroup.Basic

namespace Borel

variable {K : Type*} [Field K]

/-- The Borel subgroup of GL₂(K) -/
def Borel (K : Type*) [Field K] : Subgroup (GL (Fin 2) K) :=
  { carrier := {M : GL (Fin 2) K | M.1.1 1 0 = 0}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      simp at ha hb ⊢
      -- Upper triangular matrices are closed under multiplication
      sorry
    inv_mem' := by
      intro a ha
      simp at ha ⊢
      -- Inverse of upper triangular is upper triangular
      sorry }

/-- The diagonal torus -/
def Torus (K : Type*) [Field K] : Subgroup (GL (Fin 2) K) :=
  { carrier := {M : GL (Fin 2) K | M.1.1 0 1 = 0 ∧ M.1.1 1 0 = 0}
    one_mem' := by simp
    mul_mem' := by sorry
    inv_mem' := by sorry }

/-- The unipotent radical -/
def Unipotent (K : Type*) [Field K] : Subgroup (GL (Fin 2) K) :=
  { carrier := {M : GL (Fin 2) K | M.1.1 0 0 = 1 ∧ M.1.1 1 1 = 1 ∧ M.1.1 1 0 = 0}
    one_mem' := by simp
    mul_mem' := by sorry
    inv_mem' := by sorry }

/-- Borel is semidirect product of Torus and Unipotent -/
theorem borel_decomposition (K : Type*) [Field K] :
    Borel K = Torus K ⋉ Unipotent K :=
  sorry

end Borel
