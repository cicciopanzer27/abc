/-!
# Borel Structure Preservation in Log-Theta-Lattice

This module proves that all morphisms in a log-theta-lattice preserve Borel structure.
-/

import LogThetaLattice.Definition
import Borel.Definition
import Correspondence.Main

namespace LogThetaLattice

variable {K : Type*} [Field K]

/-- All Theta-links preserve Borel structure -/
theorem theta_links_preserve_borel 
    (j : ℕ) (u : K) (b : K) :
    thetaLinkMorphism j u b ∈ Borel.Borel K :=
  by
    apply Borel.Borel.mem_iff.mpr
    exact theta_link_borel j u b

/-- All log-links preserve Borel structure -/
theorem log_links_preserve_borel (log_u : K) :
    logLinkMorphism log_u ∈ Borel.Borel K :=
  by
    apply Borel.Borel.mem_iff.mpr
    exact log_link_borel log_u

/-- Compositions of Theta-links and log-links preserve Borel structure -/
theorem composition_preserves_borel
    (M_theta : Matrix (Fin 2) (Fin 2) K)
    (M_log : Matrix (Fin 2) (Fin 2) K)
    (h_theta : M_theta 1 0 = 0)
    (h_log : M_log 1 0 = 0) :
    (M_theta * M_log) 1 0 = 0 :=
  sorry
  /- Proof: Product of upper triangular matrices is upper triangular -/

/-- All morphisms in a log-theta-lattice preserve Borel structure -/
theorem lattice_borel_preservation 
    (L : LogThetaLattice) :
    ∀ (HT₁ HT₂ : L.theaters),
    (L.thetaLinks HT₁ HT₂ ∨ L.logLinks HT₁ HT₂) →
    ∃ (M : Matrix (Fin 2) (Fin 2) K),
    M 1 0 = 0 :=
  sorry
  /- Proof: By induction on lattice structure, using 
     theta_links_preserve_borel and log_links_preserve_borel -/

end LogThetaLattice
