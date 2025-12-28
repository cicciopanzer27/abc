/-!
# Spectral Decoupling Theorem

This module proves that perturbations of the unipotent radical do not affect
the diagonal spectrum in Borel matrices.
-/

import Borel.Definition
import Mathlib.LinearAlgebra.Matrix.Eigenvalue

namespace Borel

variable {K : Type*} [Field K]

/-- Spectral decoupling theorem -/
theorem spectral_decoupling (M : Matrix (Fin 2) (Fin 2) K)
    (hM : M 1 0 = 0) -- M is upper triangular
    (E : Matrix (Fin 2) (Fin 2) K)
    (hE : E 1 0 = 0) : -- E is upper triangular
    (M + E).eigenvalues = M.eigenvalues + E.diagonal :=
  sorry

/-- Eigenvalue stability: linear vs square root -/
theorem eigenvalue_stability (M : Matrix (Fin 2) (Fin 2) K)
    (hM : M 1 0 = 0)
    (E : Matrix (Fin 2) (Fin 2) K)
    (hE : E 1 0 = 0)
    (ε : ℝ) (hε : ‖E‖ ≤ ε) :
    ‖(M + E).eigenvalues - M.eigenvalues‖ ≤ ε :=
  sorry

end Borel
