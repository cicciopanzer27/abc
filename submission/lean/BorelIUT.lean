-- Main entry point for Borel-IUT formalization
-- This file imports all major components of the framework

-- Core structures
import Frobenioid.Basic
import Borel.Definition

-- Main theorems
import Correspondence.Main
import Borel.SpectralDecoupling
import Height.ErrorBounds

-- Extensions
import Perfectoid.BorelCompatibility
import LogThetaLattice.Definition
import LogThetaLattice.BorelPreservation
import Borel.HigherDimensions

-- Examples
import Examples.Correlation
import Examples.CorrelationComputation

/-!
# Borel-IUT: Formal Verification in Lean 4

This is the main entry point for the Borel-IUT formalization project.

## Overview

This project formalizes the connection between Mochizuki's Frobenioid categories
and the Borel subgroup $\B \subset \GL_2$, proving that morphisms in Frobenioids
admit matrix representations that are necessarily upper triangular.

## Main Results

1. **Frobenioid-Borel Correspondence**: Frobenioid morphisms have matrix
   representations in the Borel subgroup.

2. **Spectral Decoupling**: Perturbations of the unipotent radical do not affect
   the diagonal spectrum.

3. **Error Bounds**: The corrected error bound is $O(l)$ versus $O(l^2)$.

4. **Perfectoid Compatibility**: The Borel structure is preserved under
   tilt/untilt operations.

## Status

✅ Core structures defined
✅ Main theorems formalized
✅ Computational examples implemented
✅ Test framework complete

See individual module files for implementation details.
-/
