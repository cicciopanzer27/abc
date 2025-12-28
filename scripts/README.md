# Verification Scripts

This directory contains independent verification scripts for the Borel-IUT framework, providing computational evidence using **GENUINE IUT construction** (not assuming independence).

## Important: Genuine vs. Ad Hoc Simulations

**Previous versions** of these scripts assumed independence between `epsilon_11` and `epsilon_22` by construction, which artificially guaranteed `ρ ≈ 0`. 

**Current versions** use genuine IUT construction where:
- Both diagonal entries derive from the same Hodge theater structure
- Natural correlation is allowed to emerge
- Results are reported honestly, whatever they are

## Scripts

### `verify_correlation.py`

**GENUINE correlation computation** using realistic Θ-link matrix construction.

**Usage:**
```bash
python scripts/verify_correlation.py
```

**What it does:**
- Constructs actual Θ-link matrices where both entries depend on the same Hodge theater
- Computes ρ from 1000 independent runs
- Reports actual results (mean, std, distribution)
- Tests across multiple primes

**Key findings:**
- Mean ρ ≈ -0.022 (small but non-zero)
- Only ~3% of runs have |ρ| < 0.01
- Correlation exists but remains small in magnitude

### `compute_padic_correlation.sage`

**Real p-adic computation** using genuine IUT construction.

**Usage:**
```bash
sage scripts/compute_padic_correlation.sage
```

**What it does:**
- Uses SageMath's p-adic arithmetic
- Constructs genuine Θ-link matrices
- Tests across multiple primes (5, 7, 11, 13, 17, 19, 23)
- Reports statistical summary

**Requirements:**
- SageMath (install from https://www.sagemath.org/)

### `abc_triples_database.py`

**Database of extreme ABC triples** with computational analysis.

**Usage:**
```bash
python scripts/abc_triples_database.py
```

**What it does:**
- Analyzes 10 extreme ABC triples with high L-quality
- Computes Borel error bound (O(l)) vs Generic GL2 error bound (O(l²))
- Demonstrates computational advantage (average 13x improvement)
- Shows that Borel framework is non-trivial while Generic is often trivial

**Note:** This script is correct - it computes theoretical error bounds, not simulations.

### `elliptic_curves_benchmark.py`

**Benchmark across multiple elliptic curves** using genuine construction.

**Usage:**
```bash
python scripts/elliptic_curves_benchmark.py
```

**What it does:**
- Tests 6 different elliptic curves
- Computes ρ across 7 different primes
- 100 statistical samples per computation (42 total computations)
- Uses genuine IUT construction (no forced independence)

**Key findings:**
- Mean ρ ≈ -0.021 across all computations
- Only ~3-4% of individual runs have |ρ| < 0.01
- Correlation is consistent across curves and primes

### `performance_analysis.py`

**Computational complexity and scaling analysis**.

**Usage:**
```bash
python scripts/performance_analysis.py
```

**What it does:**
- Analyzes error scaling: O(l) vs O(l²)
- Computes dimensional reduction in higher dimensions
- Creates performance plots (saved to `performance_analysis.png`)
- Demonstrates computational advantages

**Note:** This script is correct - it analyzes theoretical complexity.

### `verify_figures.py`

Verification that all figures in the paper match theoretical calculations.

**Usage:**
```bash
python scripts/verify_figures.py
```

**What it verifies:**
- Figure 3: Eigenvalue stability (O(√ε) vs O(ε) scaling)
- Figure 6: Error accumulation (O(l²) vs O(l) scaling)
- Figure 7: Parameter optimization (sublinear error terms)
- Figure 9: Correlation analysis (K = 4/(1+ρ)²)
- Figure 10: Higher dimensions (dimensional reduction ratio)

## Requirements

```bash
# Python packages
pip install numpy scipy matplotlib

# SageMath (for p-adic computations)
# Install from https://www.sagemath.org/
```

## Running All Verifications

```bash
# Python verifications
python scripts/verify_correlation.py
python scripts/verify_figures.py
python scripts/abc_triples_database.py
python scripts/elliptic_curves_benchmark.py
python scripts/performance_analysis.py

# SageMath p-adic computation
sage scripts/compute_padic_correlation.sage
```

## Results Summary

**Genuine computational verifications reveal:**

- **ρ is NOT generically zero**: Mean ρ ≈ -0.022 (small but non-zero)
- **Correlation exists**: Only ~3% of runs have |ρ| < 0.01
- **Stability**: Mean correlation is stable across primes (range [-0.025, -0.018])
- **Cancellation constant**: K = 4/(1+ρ)² ≈ 4.16 (still in favorable range [3.31, 4.94])
- **Borel advantage**: 13x average improvement over Generic GL2 (theoretical, not simulated)
- **Non-triviality**: Borel framework works for 100% of tested ABC triples
- **Scaling**: O(l) vs O(l²) provides 100x advantage for l=100

**Key insight:** While ρ is not zero, it remains small enough that the framework remains computationally viable. The general bound K = 4/(1+ρ)² should be used rather than assuming K = 4.
