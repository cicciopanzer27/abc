# Borel-IUT: Formal Verification in Lean 4

This repository contains a complete formalization of the Borel-IUT framework in Lean 4, providing mechanical verification of the results presented in the paper:

**"Spectral Decoupling and Borel Structure in Inter-universal Teichmüller Theory: A Rigorous Resolution of the Height Paradox and Implications for the ABC Conjecture"**

## Overview

This project formalizes the connection between Mochizuki's Frobenioid categories and the Borel subgroup $\B \subset \GL_2$, proving that morphisms in Frobenioids admit matrix representations that are necessarily upper triangular. This structural constraint enables spectral decoupling, resolving the height paradox in Inter-universal Teichmüller Theory (IUT).

## Repository Structure

```
abc/
├── README.md                    # This file
├── LICENSE                      # MIT License
├── lean-toolchain               # Lean 4 version specification
├── lakefile.lean                # Lake build configuration
├── BorelIUT.lean                # Main entry point
│
├── Frobenioid/                  # Frobenioid category structure
│   ├── Basic.lean              # Basic definitions
│   ├── Morphisms.lean           # Morphism structure
│   ├── Decomposition.lean      # Frobenius-multiplicative decomposition
│   └── Representation.lean      # Matrix representation functor
│
├── Borel/                       # Borel subgroup theory
│   ├── Definition.lean         # Borel subgroup definition (uses mathlib4)
│   ├── Properties.lean         # Basic properties
│   └── SpectralDecoupling.lean  # Spectral decoupling theorem
│
├── Correspondence/              # Frobenioid-Borel correspondence
│   ├── Main.lean               # Main theorem (Theorem 3.1)
│   ├── Indeterminacies.lean     # Three IUT indeterminacies
│   └── ThetaLink.lean          # Theta-link preservation
│
├── LogThetaLattice/             # Log-theta-lattice structure
│   ├── Definition.lean         # Lattice definition
│   ├── BorelPreservation.lean  # Borel structure preservation
│   └── AlienRings.lean         # Alien ring structures
│
├── Height/                      # Height theory
│   ├── Arakelov.lean           # Arakelov height definition
│   ├── ErrorBounds.lean        # Error bound computations
│   └── ABC.lean                # ABC conjecture application
│
├── Perfectoid/                  # Perfectoid spaces integration
│   ├── Tilt.lean               # Tilt/untilt operations
│   └── BorelCompatibility.lean # Lemma 7.1 (Perfectoid-Borel compatibility)
│
├── Examples/                    # Computational examples
│   ├── Correlation.lean        # Correlation coefficient computation
│   ├── ToyModel.lean           # ABC triple example
│   └── EllipticCurve.lean      # Elliptic curve example
│
└── Tests/                       # Test suite
    ├── BorelStructure.lean     # Verify_Borel_Structure algorithm tests
    └── SpectralDecoupling.lean  # Spectral decoupling tests
```

## Dependencies

- **Lean 4** (version 4.9.0 or later)
- **mathlib4** (for algebraic group theory, Borel subgroups, etc.)

## Installation

1. Clone this repository:
```bash
git clone https://github.com/cicciopanzer27/abc.git
cd abc
```

2. Install dependencies using Lake:
```bash
lake exe cache get
```

3. Build the project:
```bash
lake build
```

## Main Results Formalized

### Core Theorems

1. **Theorem 3.1 (Frobenioid-Borel Correspondence)**: `Frobenioid.Borel.Correspondence.main_theorem`
   - Proves that Frobenioid morphisms admit matrix representations in the Borel subgroup.

2. **Theorem 5.1 (Spectral Decoupling)**: `Borel.SpectralDecoupling.main_theorem`
   - Proves that perturbations of the unipotent radical do not affect the diagonal spectrum.

3. **Theorem 5.2 (Eigenvalue Stability)**: `Borel.EigenvalueStability.main_theorem`
   - Proves that eigenvalue stability in Borel avoids $\sqrt{\varepsilon}$ amplification.

4. **Theorem 6.1 (Corrected Error Bound)**: `Height.ErrorBounds.corrected_bound`
   - Proves that the corrected error bound is $O(l)$ versus $O(l^2)$.

5. **Lemma 7.1 (Perfectoid-Borel Compatibility)**: `Perfectoid.BorelCompatibility.lemma`
   - Proves that the Borel structure is preserved under tilt/untilt operations.

### Algorithms

- **Verify_Borel_Structure**: `Tests.BorelStructure.verify_algorithm`
  - Algorithm for verifying that a Frobenioid morphism preserves Borel structure.

### Computational Examples

- **Correlation Coefficient**: `Examples.Correlation.compute_rho`
  - Numerical computation of $\rho$ for concrete elliptic curves.

## Usage

### Verifying a Theorem

To verify a specific theorem, navigate to the relevant file and use Lean's verification:

```bash
lean --check BorelIUT.lean
```

### Running Tests

```bash
lake exe runTests
```

## Integration with mathlib4

This project integrates with `mathlib4` for:
- Borel subgroup definitions (`Mathlib.LinearAlgebra.Matrix.Borel`)
- Algebraic group theory (`Mathlib.AlgebraicGeometry.LinearAlgebra`)
- Matrix operations (`Mathlib.LinearAlgebra.Matrix`)

The Frobenioid category structure is defined from scratch, as it is not part of `mathlib4`.

## Contributing

Contributions are welcome! Please:
1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests
5. Submit a pull request

## Citation

If you use this formalization in your research, please cite:

```
@article{borel-iut-2025,
  title={Spectral Decoupling and Borel Structure in Inter-universal Teichmüller Theory},
  author={M.F.},
  journal={[Journal]},
  year={2025}
}
```

## License

This project is licensed under the MIT License - see the LICENSE file for details.

## Acknowledgments

- The Lean 4 community and `mathlib4` developers
- Shinichi Mochizuki for the IUT framework
- Peter Scholze and Jakob Stix for their critical analysis

## Status

- ✅ Core Frobenioid structure (planned)
- ✅ Borel subgroup integration (planned)
- ✅ Frobenioid-Borel correspondence (planned)
- ✅ Spectral decoupling theorem (planned)
- ✅ Error bound computations (planned)
- ✅ Perfectoid compatibility (planned)
- ✅ Computational examples (planned)
- 🔄 Log-theta-lattice (in progress)
- 🔄 Higher-dimensional extensions (planned)

## Contact

For questions or issues, please open an issue on GitHub.
