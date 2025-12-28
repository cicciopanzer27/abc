# Verification Scripts

This directory contains independent verification scripts for the Borel-IUT framework.

## Scripts

### `verify_correlation.py`

Independent verification of the correlation coefficient ρ computation.

**Usage:**
```bash
python scripts/verify_correlation.py
```

**What it does:**
- Computes ρ for E: y² = x³ + x + 1 with p = 13
- Verifies that ρ ≈ -0.0021
- Tests correlation stability across multiple primes (5, 7, 11, 13, 17, 19, 23)

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
pip install numpy scipy matplotlib
```

## Running All Verifications

```bash
python scripts/verify_correlation.py
python scripts/verify_figures.py
```

Both scripts should complete without errors if all verifications pass.
