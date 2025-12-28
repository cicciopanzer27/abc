/-!
# Log-Theta-Lattice Definition

This module defines the log-theta-lattice structure, which is the central
structure connecting multiple Hodge theaters in IUT.
-/

import Frobenioid.Basic
import Correspondence.Main
import Mathlib.Data.Finset.Basic

namespace LogThetaLattice

variable {K : Type*} [Field K] {F : Type*} [Category F] [Frobenioid F]

/-- A Hodge theater in IUT -/
structure HodgeTheater where
  /-- The number field -/
  numberField : Type*
  /-- The elliptic curve -/
  ellipticCurve : Type*
  /-- Local Frobenioids at each place -/
  localFrobenioids : Type*
  /-- Log-theta-lattice structure -/
  latticeStructure : Type*

/-- A log-theta-lattice is a directed graph of Hodge theaters -/
structure LogThetaLattice where
  /-- The set of Hodge theaters -/
  theaters : Finset HodgeTheater
  /-- Theta-link connections -/
  thetaLinks : HodgeTheater → HodgeTheater → Prop
  /-- Log-link connections -/
  logLinks : HodgeTheater → HodgeTheater → Prop

/-- Theta-link morphism -/
def thetaLinkMorphism (j : ℕ) (u : K) (b : K) : Matrix (Fin 2) (Fin 2) K :=
  ![![j^2 * u, b], ![0, 1]]

/-- Log-link morphism -/
def logLinkMorphism (log_u : K) : Matrix (Fin 2) (Fin 2) K :=
  ![![1, log_u], ![0, 1]]

/-- Theta-link preserves Borel structure -/
theorem theta_link_borel (j : ℕ) (u : K) (b : K) :
    (thetaLinkMorphism j u b) 1 0 = 0 :=
  by simp [thetaLinkMorphism]

/-- Log-link preserves Borel structure -/
theorem log_link_borel (log_u : K) :
    (logLinkMorphism log_u) 1 0 = 0 :=
  by simp [logLinkMorphism]

end LogThetaLattice
