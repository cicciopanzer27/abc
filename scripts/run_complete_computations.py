#!/usr/bin/env python3
"""
Run complete real computations and save results for paper.

This script executes all real IUT constructions, computes correlation
coefficients, and saves results in formats suitable for the paper.
"""

import sys
import json
import numpy as np
from real_iut_construction import (
    EllipticCurve, construct_hodge_theater_step_by_step, 
    compute_correlation_real
)

def run_multiple_computations():
    """Run computations for multiple curves and primes."""
    print("="*70)
    print("RUNNING COMPLETE REAL COMPUTATIONS")
    print("="*70)
    
    curves = [
        EllipticCurve(0, 1, 1),  # y² = x³ + x + 1
        EllipticCurve(0, 0, 1),  # y² = x³ + 1
        EllipticCurve(0, -1, 1), # y² = x³ - x + 1
    ]
    
    primes = [5, 7, 11, 13, 17, 19, 23]
    
    all_results = []
    
    for curve_idx, curve in enumerate(curves):
        for p in primes:
            print(f"\n{'='*70}")
            print(f"Curve {curve_idx+1}: y² = x³ + {curve.a}x² + {curve.b}x + {curve.c}")
            print(f"Prime: p = {p}")
            print(f"{'='*70}")
            
            try:
                # Real construction
                hodge_theater = construct_hodge_theater_step_by_step(curve, p, 13)
                
                # Real correlation computation
                rho, stats = compute_correlation_real(hodge_theater)
                
                result = {
                    'curve': {
                        'a': curve.a,
                        'b': curve.b,
                        'c': curve.c,
                        'conductor': curve.conductor()
                    },
                    'prime': p,
                    'steps': 13,
                    'rho': float(rho),
                    'K': float(stats['K']),
                    'cov': float(stats['cov']),
                    'var_11': float(stats['var_11']),
                    'var_22': float(stats['var_22']),
                    'mean_11': float(stats['mean_11']),
                    'mean_22': float(stats['mean_22']),
                    'n': int(stats['n']),
                    'errors_11': [float(e) for e in hodge_theater.diagonal_errors_11],
                    'errors_22': [float(e) for e in hodge_theater.diagonal_errors_22]
                }
                
                all_results.append(result)
                
                print(f"\n[RESULT] rho = {rho:.6f}, K = {stats['K']:.6f}")
                
            except Exception as e:
                print(f"[ERROR] {e}")
                import traceback
                traceback.print_exc()
                continue
    
    # Save results
    with open('scripts/computation_results.json', 'w') as f:
        json.dump(all_results, f, indent=2)
    
    print(f"\n{'='*70}")
    print(f"COMPUTATIONS COMPLETE")
    print(f"{'='*70}")
    print(f"Total computations: {len(all_results)}")
    print(f"Results saved to: scripts/computation_results.json")
    
    # Summary statistics
    if all_results:
        rhos = [r['rho'] for r in all_results]
        Ks = [r['K'] for r in all_results]
        
        print(f"\nSummary:")
        print(f"  Mean rho: {np.mean(rhos):.6f}")
        print(f"  Std rho: {np.std(rhos):.6f}")
        print(f"  Min rho: {np.min(rhos):.6f}")
        print(f"  Max rho: {np.max(rhos):.6f}")
        print(f"  Mean K: {np.mean(Ks):.6f}")
        print(f"  K range: [{np.min(Ks):.6f}, {np.max(Ks):.6f}]")
    
    return all_results

if __name__ == "__main__":
    results = run_multiple_computations()
